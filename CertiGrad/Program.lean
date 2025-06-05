/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

A Term language for conveniently constructing stochastic computation graphs.
-/
-- import .tensor .graph .tactics .ops data.hash_map

import CertiGrad.Tensor
import CertiGrad.Graph
import CertiGrad.Ops
import CertiGrad.Tactics

-- import Std .Data.DHashMap


#print "compiling program..."

namespace certigrad
namespace program

-- open list

inductive UnaryOp : Type
| neg : UnaryOp
| exp : UnaryOp
| log : UnaryOp
| sqrt : UnaryOp
| softplus : UnaryOp
| sigmoid : UnaryOp

inductive BinaryOp : Type
| add : BinaryOp
| sub : BinaryOp
| mul : BinaryOp
| div : BinaryOp

inductive Term : Type
| unary : UnaryOp → Term → Term
| binary : BinaryOp → Term → Term → Term
| sum : Term → Term
| scale : TReal→ Term → Term
| gemm : Term → Term → Term
| mvn_kl : Term → Term → Term
| mvn_empirical_kl : Term → Term → Term → Term
| bernoulli_neglogpdf : Term → Term → Term
| id : Label → Term

-- instance : has_neg Term := ⟨term.unary UnaryOp.neg⟩
-- instance : has_smul TRealterm := ⟨term.scale⟩
-- instance : has_add Term := ⟨term.binary BinaryOp.add⟩
-- instance : has_sub Term := ⟨term.binary BinaryOp.sub⟩
-- instance : has_mul Term := ⟨term.binary BinaryOp.mul⟩
-- instance : has_div Term := ⟨term.binary BinaryOp.div⟩

-- instance coe_id : has_coe Label Term := ⟨term.id⟩

def exp : Term → Term := Term.unary UnaryOp.exp
def log : Term → Term := Term.unary UnaryOp.log
def sqrt : Term → Term := Term.unary UnaryOp.sqrt
def softplus : Term → Term := Term.unary UnaryOp.softplus
def sigmoid : Term → Term := Term.unary UnaryOp.sigmoid

inductive rterm : Type
| mvn : Term → Term → rterm
| mvn_std : S → rterm

inductive statement : Type
| param : Label → S → statement
| input : Label → S → statement
| cost : Label → statement
| assign : Label → Term → statement
| sample : Label → rterm → statement

structure state : Type :=
  next_id : Nat
  -- shapes : hash_map Label (λ x => S)
  shapes : Std.DHashMap Label (λ x => S)
  nodes : List Node
  costs : List ID
  targets : List Reference
  inputs : List Reference

-- def empty_state : state := ⟨0, mk_hash_map (λ (x : label)=> x^.to_nat), [], [], [], []⟩
def empty_state : state := ⟨0, Std.DHashMap.emptyWithCapacity , [], [], [], []⟩

-- operators like `ops.neg` are currently commented out in `Ops.lean`
noncomputable def unary_to_op (shape : S) : UnaryOp → det.op [shape] shape
| UnaryOp.neg      => ops.neg shape
| UnaryOp.exp      => ops.exp shape
| UnaryOp.log      => ops.log shape
| UnaryOp.sqrt     => ops.sqrt shape
| UnaryOp.softplus => ops.softplus shape
| UnaryOp.sigmoid  => ops.sigmoid shape

noncomputable def binary_to_op (shape : S) : BinaryOp → det.op [shape, shape] shape
| BinaryOp.add     => ops.add shape
| BinaryOp.mul     => ops.mul shape
| BinaryOp.sub     => ops.sub shape
| BinaryOp.div     => ops.div shape

def get_id (next_id : ℕ) : Option ID → ID
| none => ID.nat next_id
| (some ident) => ident

  -- def process_term : Term → state → Option ID → Reference × state := sorry

noncomputable def process_term : Term → state → Option ID → Reference × state
  | Term.unary f t, st, ident =>
    let ((p₁, shape), st') := process_term t st none
    let ⟨next_id, shapes, nodes, costs, targets, inputs⟩ := st'
    ((get_id next_id ident, shape),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, shape), [(p₁, shape)], Operator.det (unary_to_op shape f)⟩],
      costs, targets, inputs⟩)

  | Term.binary f t₁ t₂, st, ident =>
    let ((p₁, shape), st₁) := process_term t₁ st none
    let ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t₂ st₁ none
    ((get_id next_id ident, shape),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], Operator.det (binary_to_op shape f)⟩],
      costs, targets, inputs⟩)

  | Term.sum t, st, ident =>
    let ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t st none
    ((get_id next_id ident, []),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, []), [(p₁, shape)], Operator.det (ops.sum shape)⟩],
      costs, targets, inputs⟩)

  | Term.scale α t, st, ident =>
    let ((p₁, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t st none
    ((get_id next_id ident, shape),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, shape), [(p₁, shape)], Operator.det (ops.scale α shape)⟩],
      costs, targets, inputs⟩)

  | Term.gemm t₁ t₂, st, ident =>
    let ((p₁, shape₁), st₁) := process_term t₁ st none
    let ((p₂, shape₂), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t₂ st₁ none
    let m := shape₁.headD 0
    let n := shape₁.tail.headD 0
    let p := shape₂.tail.headD 0
    ((get_id next_id ident, [m, p]),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, [m, p]), [(p₁, [m, n]), (p₂, [n, p])], Operator.det (ops.gemm m n p)⟩],
      costs, targets, inputs⟩)

  | Term.mvn_kl t₁ t₂, st, ident =>
    let ((p₁, shape₁), st₁) := process_term t₁ st none
    let ((p₂, shape₂), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t₂ st₁ none
    ((get_id next_id ident, []),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, []), [(p₁, shape₂), (p₂, shape₂)], Operator.det (ops.mvn_kl shape₂)⟩],
      costs, targets, inputs⟩)

  | Term.mvn_empirical_kl t₁ t₂ t₃, st, ident =>
    let ((p₁, shape₁), st₁) := process_term t₁ st none
    let ((p₂, shape₂), st₂) := process_term t₂ st₁ none
    let ((p₃, shape₃), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t₃ st₂ none
    ((get_id next_id ident, []),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, []), [(p₁, shape₃), (p₂, shape₃), (p₃, shape₃)], Operator.det (det.op.mvn_empirical_kl shape₃)⟩],
      costs, targets, inputs⟩)

  | Term.bernoulli_neglogpdf t₁ t₂, st, ident =>
    let ((p₁, shape₁), st₁) := process_term t₁ st none
    let ((p₂, shape₂), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) := process_term t₂ st₁ none
    ((get_id next_id ident, []),
      ⟨next_id+1, shapes,
      nodes ++ [⟨(get_id next_id ident, []), [(p₁, shape₂), (p₂, shape₂)], Operator.det (ops.bernoulli_neglogpdf shape₂)⟩],
      costs, targets, inputs⟩)

  | Term.id s, ⟨next_id, shapes, nodes, costs, targets, inputs⟩, ident =>
    match shapes.get? s with
    | some shape => ((ID.str s, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩)
    | none       => (default, empty_state)


noncomputable
def process_rterm : rterm → state → Option ID → Reference × state
| (rterm.mvn t₁ t₂), st, ident =>
    match process_term t₁ st none with
    | ((p₁, shape'), st') =>
      match process_term t₂ st' none with
      | ((p₂, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) =>
        ((get_id next_id ident, shape),
          ⟨next_id+1, shapes,
          List.concat nodes ⟨(get_id next_id ident, shape), [(p₁, shape), (p₂, shape)], Operator.rand (rand.op.mvn shape)⟩,
          costs, targets, inputs⟩)

| (rterm.mvn_std shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩, ident =>
  ((get_id next_id ident, shape),
   ⟨next_id+1, shapes,
    nodes ++ [⟨(get_id next_id ident, shape), [], Operator.rand (rand.op.mvn_std shape)⟩],
    costs, targets, inputs⟩)

noncomputable
def program_to_graph_core : List statement → state → state
| [], st => st
| (statement.assign s t::statements), st =>
  match process_term t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) =>
     program_to_graph_core statements ⟨next_id, shapes.insert s shape, nodes, costs, targets, inputs⟩

| (statement.sample s t::statements), st =>
  match process_rterm t st (some (ID.str s)) with
  | ((_, shape), ⟨next_id, shapes, nodes, costs, targets, inputs⟩) =>
    program_to_graph_core statements ⟨next_id, shapes.insert s shape, nodes, costs, targets, inputs⟩

| (statement.param s shape::statements), ⟨next_id, shapes, nodes, costs, targets, inputs⟩ =>
  program_to_graph_core statements ⟨next_id, shapes.insert s shape, nodes, costs, List.concat targets (ID.str s, shape), List.concat inputs (ID.str s, shape)⟩

| (statement.input s shape::statements), ⟨next_id, shapes, nodes, costs, targets, inputs⟩ =>
  program_to_graph_core statements ⟨next_id, shapes.insert s shape, nodes, costs, targets, List.concat inputs (ID.str s, shape)⟩

| (statement.cost s::statements), ⟨next_id, shapes, nodes, costs, targets, inputs⟩ =>
  program_to_graph_core statements ⟨next_id, shapes, nodes, List.concat costs (ID.str s), targets, inputs⟩

end program

def program := List program.statement

noncomputable
def program_to_graph : program → Graph
| prog =>  match program.program_to_graph_core prog program.empty_state with
           | ⟨next_id, shapes, nodes, costs, targets, inputs⟩ => ⟨nodes, costs, targets, inputs⟩

def mk_inputs : ∀ (g : Graph), Dvec T g.inputs.p2 → Env
| g, ws => certigrad.env.insert_all g.inputs ws

end certigrad
