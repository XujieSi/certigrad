/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Deterministic operators.
-/
-- import .tgrads .util .tcont .det

import CertiGrad.Tgrads
import CertiGrad.Util
import CertiGrad.Tcont
import CertiGrad.Det
import CertiGrad.SimpGrad
import Lean
open Lean Elab Tactic Meta


namespace certigrad
open T util_list
set_option linter.unusedVariables false
namespace ops

section tactic
-- open tactic

-- meta def idx_over :TacticM Unit :=
-- do exfalso, to_expr ```(at_idx_over H_at_idx dec_trivial) >>= exact

def idxOver : TacticM Unit := do
  -- let varId ← getMainGoal
  -- let newId ← Lean.MVarId.falseOrByContra varId
  -- setGoals [newId]

  -- mkAppM ``certigrad.T.is_cdifferentiable_log #[k]
  -- let mvarIds ← tid.apply e'
  -- apply at_idx_over H_at_idx (by simp)

  match (← getLCtx).findFromUserName? `H_at_idx with
  | some l =>
      let e' ←  mkAppM ``at_idx_over #[l.toExpr]
      let falseGoalId ← Lean.MVarId.falseOrByContra (← getMainGoal)
      -- setGoals (← falseGoalId.apply e')
      -- there should be only one sub-goal at this point, i.e., not (n+1 < 1)
      for subGoalId in (← falseGoalId.apply e') do
        -- empty Simp.Context: { simpTheorems := #[]}
        let (result?, stats) ← simpGoal subGoalId { simpTheorems := #[(← getSimpTheorems)]}
        match result? with
        | none => replaceMainGoal []
        | some (_, mvarId) => replaceMainGoal [mvarId]

      return ()
  | none =>
    log m!"cannot find hypothesis at_idx_over"
    return ()


elab "idx_over" : tactic => do idxOver


def substEqThenApplyCore (Hname s1 s2 : Name) (f : MVarId → TacticM (List MVarId)) : TacticM Unit := do
  -- `let` tactic corresponds to `Lean.MVarId.define`
  -- `have` roughly corresponds to `Lean.MVarId.assert`, `mvarId.assign` Lean.MVarId.assign
  -- `intro` corresponds to `introStep`, `Lean.MVarId.intro`,

  let goalId ← getMainGoal

  let H ← (← getLCtx).findFromUserName? Hname
  let fshape ← (← getLCtx).findFromUserName? s1
  let shape ← (← getLCtx).findFromUserName? s2
  let eqH ← mkAppM `Eq #[fshape.toExpr, shape.toExpr]
  let eqV ← mkAppM `And.right #[H.toExpr]
  let assertId ← goalId.assert `H_fshape_eq eqH eqV
  let (fid, vid) ← Lean.Meta.intro1Core assertId true

  let vid2 ← subst vid fid

  let (result?, stats) ← simpGoal vid2 { simpTheorems := #[(← getSimpTheorems)]}
  match result? with
  | none => replaceMainGoal []
  | some (_, mvarId) =>
    let subGoals ← Meta.repeat' f [mvarId]
    match subGoals with
    | [] => replaceMainGoal []
    | [g] => try Lean.MVarId.assumption  g
      catch exp => setGoals subGoals
    | _ => setGoals subGoals


def proveODiff : TacticM Unit := do
  substEqThenApplyCore `H_at_idx `fshape `shape proveDifferentiableCore


elab "prove_odiff" : tactic => do proveODiff


-- def PbCorrectApplyCore (Hname s1 s2 s3 s4: Name) (f : TacticM Unint) : TacticM Unit := do
--   -- `let` tactic corresponds to `Lean.MVarId.define`
--   -- `have` roughly corresponds to `Lean.MVarId.assert`, `mvarId.assign` Lean.MVarId.assign
--   -- `intro` corresponds to `introStep`, `Lean.MVarId.intro`,

--   let goalId ← getMainGoal
--   logInfo m!"PbCorrectApplyCore is Called : {← goalId.getType}"

--   let H ← (← getLCtx).findFromUserName? Hname
--   let fshape ← (← getLCtx).findFromUserName? s1
--   let shape ← (← getLCtx).findFromUserName? s2
--   let g_out ← (← getLCtx).findFromUserName? s3
--   let y ← (← getLCtx).findFromUserName? s4
--   let eqH ← mkAppM `Eq #[fshape.toExpr, shape.toExpr]
--   let eqV ← mkAppM `And.right #[H.toExpr]
--   logInfo m!"{g_out.toExpr}"
--   let assertId ← goalId.assert `H_fshape_eq eqH eqV
--   let (fid, vid) ← Lean.Meta.intro1Core assertId true
--   let vid2 ← subst vid fid
--   let pf ← mkAppM ``certigrad.T.grad_dot₂ #[g_out.toExpr, y.toExpr]
--   evalTactic (← `(rw[pf]))
--   let HkGrad ← assert `H_k_grad (← mkEq lhs rhs) (← mkFreshExprMVar (← mkEq lhs rhs))
--   -- 然后用 `erw`（在 TacticM 里是 `Tactic.erw`）
--   Tactic.erw (← getLocalDecl `H_k_grad).toExpr (← `(certigrad.T.grad_dot₁))

--   -- let H_k_grad ← (← getLCtx).findFromUserName? `H_k_grad
--   -- logInfo m!"H_k_grad: {H_k_grad.toExpr}"


--   evalTactic (← `(tactic| simp))

--   evalTactic (← `(tactic|rw [← certigrad.T.grad_tmulT]))

--   evalTactic (← `(tactic|dsimp [force]))

--   simplify_Grad

--   evalTactic (← `(tactic|rfl))


def proveOCont :TacticM Unit := do
  substEqThenApplyCore `H_at_idx `ishape `shape proveContinuousCore

elab "prove_ocont" : tactic => do proveOCont

end tactic

open det

namespace scale

noncomputable
def f (α : TReal) {shape : S} (xs : Dvec T [shape]) : T shape := α • xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => True

noncomputable
def f_pb (α : TReal) {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape := force (α • gy) fshape

attribute [simp] f f_pre f_pb



/-

Copy of definition of is_odifferentiable

noncomputable
def is_odifferentiable {ishapes : List S} {oshape : S} (f : Dvec T ishapes → T oshape) (f_pre : Dvec T ishapes → Prop) : Prop :=
    ∀ (xs : Dvec T ishapes), f_pre xs →
    ∀ (idx : Nat) (fshape : S), at_idx ishapes idx fshape →
    ∀ (k : T oshape → TReal), is_cdifferentiable k (f xs) →
    is_cdifferentiable (λ θ₀ => k (f $ update_at θ₀ xs idx)) (get fshape _ xs idx)

-/

-- def at_idx {X : Type} [Inhabited X] (xs : List X) (idx : Nat) (x : X) : Prop :=

-- #print inferInstance

-- instance ins_S : Inhabited S where
--   default := []

-- #check ins_S

-- set_option trace.Elab.definition true
-- set_option pp.all true

-- (kernel) declaration has metavariables 'certigrad.ops.scale.f_odiff'
-- https://leanprover-community.github.io/archive/stream/270676-lean4/topic/(kernel).20declaration.20has.20metavariables.html

lemma f_odiff_verbose_proof (α : TReal) {shape : S} : is_odifferentiable (@f α shape) (@f_pre shape) := by
  unfold is_odifferentiable
  intro xs H_pre idx fshape H_at_idx k H_k
  cases xs
  case dcons h tl =>
    cases tl
    simp at H_k
    cases idx
    case zero =>
      -- simp
      obtain ⟨left, right⟩ := H_at_idx
      simp [dnth] at right
      have H_fshape_eq : fshape = shape := right
      rw [H_fshape_eq]
      simp
      proveDifferentiable
      -- apply certigrad.T.is_cdifferentiable_scale
      -- assumption
    case dnil.succ n =>
      have H_False : False := at_idx_over H_at_idx (by simp)
      contradiction

-- (kernel) declaration has metavariables 'certigrad.ops.scale.f_odiff2'
-- the problem may be due to the use of pattern match
-- if we do not use `proveDifferentiable`, it works properly
-- a bug in `proveDifferentiable`??
lemma f_odiff (α : TReal) {shape : S} : is_odifferentiable (@f α shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
  -- intro

  -- have H_fshape_eq : fshape = shape := H_at_idx.right
  -- subst H_fshape_eq
  -- rw [H_fshape_eq]
  -- simp

  -- using `tid.withcontext` does not fully address the problem
  -- we got unknown free variable issue again:
  -- logInfo: done with computeK, k:= fun x => @_fvar.5029 x
  -- solution: we need to use `tid.withContext` wrap myFirstApply as well
  -- proveDifferentiable
  -- assumption
  -- apply certigrad.T.is_cdifferentiable_scale; assumption

| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over
  -- have H_False : False := at_idx_over H_at_idx (by simp)
  -- contradiction

-- #print f_odiff2

-- do get_local `f_pb_correct >>= clear,
--    to_expr ```(shape = fshape) >>= λ ty, to_expr ```(eq.symm H_at_idx.right) >>= λ val, assertv `H_fshape_eq ty val,
--    get_local `H_fshape_eq >>= subst,
--    to_expr ```(T shape → TReal) >>= λ ty, to_expr ```(λ (z : T shape), T.dot z g_out) >>= definev `k ty,
--    to_expr ```(∇ k y = g_out) >>= assert `H_k_grad, dsimp, rewrite `certigrad.T.grad_dot₁,
--    get_local `H_k_grad >>= rewrite_core reducible tt tt occurrences.all tt,
--    get_local `H_y >>= subst

-- do prove_pb_correct_init,
--    try simp_simple,
--    try dsimp,
--    mk_const `certigrad.T.grad_tmulT >>= rewrite_core reducible tt tt occurrences.all tt,
--    simplify_grad,
--    try simp,
--    try reflexivity



lemma f_pb_correct (α : TReal) {shape : S} : pullback_correct (@f α shape) (@f_pre shape) (@f_pb α shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre => by
  have H_fshape_eq : fshape = shape := H_at_idx.right
  -- subst H_fshape_eq
  -- have k : T shape → TReal := λ (z : T shape) => certigrad.T.dot z g_out
  let k := λ (z : T shape) => certigrad.T.dot z g_out
  have H_k_grad : ∇ k (@f α shape ⟦x⟧) = g_out := by simp; rw [certigrad.T.grad_dot₁]
  subst H_fshape_eq
  rw [← H_k_grad]
  subst H_y
  -- dsimp
  -- simp
  -- simp only [f, Dvec.head, dvec.update_at]
  -- simp only [dvec.get]
  simp
  rw [← certigrad.T.grad_tmulT]
  rw [certigrad.T.grad_scale]
  unfold force
  simp
  -- rw [certigrad.T.grad_dot₂]

| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by
  idx_over

  -- exfalso
  -- apply at_idx_over H_at_idx (by simp)

-- #print f_pb_correct
-- idx_over

lemma f_ocont (α : TReal) {shape : S} : is_ocontinuous (@f α shape) (@f_pre shape)
| ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
  -- have H_ishape_eq : ishape = shape := H_at_idx.right
  -- subst H_ishape_eq
  -- simp
  -- proveContinuous

-- prove_ocont
| ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end scale

section open scale

noncomputable
def scale (α : TReal) (shape : S) : det.op [shape] shape :=
det.op.mk "scale" (f α) f_pre (f_pb α) (f_odiff α) (f_pb_correct α) (f_ocont α)

end

namespace neg

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := - xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => True

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape := force (-gy) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre => --by prove_pb_correct
  sorry
| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end neg

section open neg

noncomputable
def neg (shape : S) : det.op [shape] shape :=
  det.op.mk "neg" f f_pre f_pb f_odiff f_pb_correct f_ocont
end


namespace exp

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := exp xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => True

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape := force (gy * y) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre => sorry --by prove_pb_correct
| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end exp

section open exp
noncomputable
def exp (shape : S) : det.op [shape] shape :=
det.op.mk "exp" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace log

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := log xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => xs.head > 0

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape := force (gy / xs.head) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by
  simp at H_pre
  simp [f] at H_k
  prove_odiff
  trivial
  assumption -- handle eta-equivalence,  k  `equiv` (fun x = k x)
| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre => sorry --by prove_pb_correct
| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end log

section open log
noncomputable
def log (shape : S) : det.op [shape] shape :=
det.op.mk "log" f f_pre f_pb f_odiff f_pb_correct f_ocont
end


namespace sqrt

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := sqrt xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => 0 < xs.head

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape := force (gy / (2 * y)) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over


lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
  by
    -- provePbCorrect
    try clear f_pb_correct
    have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
    subst H_fshape_eq
    have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
        rw [certigrad.T.grad_dot₁]
    rw [ H_k_grad ]
    subst H_y
    simp
    rw [← certigrad.T.grad_tmulT]
    dsimp [force]
    simplifyGrad
    simp

| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end sqrt

section open sqrt
noncomputable
def sqrt (shape : S) : det.op [shape] shape :=
det.op.mk "sqrt" f f_pre f_pb f_odiff f_pb_correct f_ocont
end


namespace sigmoid

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := sigmoid xs.head

noncomputable
def f_pre {shape : S} : precondition [shape] := λ xs => true

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape :=
force (gy * y * (1 - y)) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x⟧, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>  by
    try clear f_pb_correct
    have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
    subst H_fshape_eq
    have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
        rw [certigrad.T.grad_dot₁]
    rw [ H_k_grad ]
    subst H_y
    simp
    rw [← certigrad.T.grad_tmulT]
    dsimp [force]
    simplifyGrad
    simp
| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
  | ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
  | ⟦x⟧, (n+1), ishape, H_at_idx, H_pre => by idx_over

end sigmoid

section open sigmoid
  def sigmoid (shape : S) : det.op [shape] shape :=
    det.op.mk "sigmoid" f f_pre f_pb f_odiff f_pb_correct f_ocont
end


namespace softplus

noncomputable
def f {shape : S} (xs : Dvec T [shape]) : T shape := softplus xs.head
noncomputable
def f_pre {shape : S} : precondition [shape] := λ xs => True
noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape :=
  force (gy / (1 + T.exp (- xs.head))) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+1), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| xs, y, H_y, g_out, (n+1), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
  | ⟦x⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
  | xs, (n+1), ishape, H_at_idx, H_pre => by idx_over

end softplus

section open softplus
noncomputable
def softplus (shape : S) : det.op [shape] shape :=
  det.op.mk "softplus" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace add

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape]) : T shape := xs.head + xs.head2
noncomputable
def f_pre {shape : S} : precondition [shape, shape] := λ xs => True
noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : T shape) (idx : Nat) (fshape : S) : T fshape :=
  force gy fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x, y⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| ⟦x₁, x₂⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x₁, x₂⟧, 1, ishape, H_at_idx, H_pre => by prove_ocont
| xs, (n+2), ishape, H_at_idx, H_pre => by idx_over

end add

section open add
noncomputable
def add (shape : S) : det.op [shape, shape] shape :=
  det.op.mk "add" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace mul

noncomputable def f {shape : S} (xs : Dvec T [shape, shape]) : T shape := xs.head * xs.head2
noncomputable def f_pre {shape : S} : precondition [shape, shape] := λ xs => True

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : T shape) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (gy * xs.head2) fshape
| 1, fshape => force (gy * xs.head) fshape
| (n+2), fshape => T.error "mul: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x, y⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
  by
    try clear f_pb_correct
    have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
    subst H_fshape_eq
    have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
      rw [certigrad.T.grad_dot₁]
    rw [ H_k_grad ]
    subst H_y
    simp
    rw [← certigrad.T.grad_tmulT]
    dsimp [force]
    simplifyGrad
    simp
| ⟦x₁, x₂⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
  by
    try clear f_pb_correct
    have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
    subst H_fshape_eq
    have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
      rw [certigrad.T.grad_dot₁]
    rw [ H_k_grad ]
    subst H_y
    simp
    rw [← certigrad.T.grad_tmulT]
    dsimp [force]
    simplifyGrad
    simp
| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

attribute [simp] f f_pre f_pb



lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x₁, x₂⟧, 1, ishape, H_at_idx, H_pre => by prove_ocont
| xs, (n+2), ishape, H_at_idx, H_pre => by idx_over

end mul

section open mul
noncomputable
def mul (shape : S) : det.op [shape, shape] shape :=
  det.op.mk "mul" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace sub

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape]) : T shape := xs.head - xs.head2
noncomputable
def f_pre {shape : S} : precondition [shape, shape] := λ xs => True

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : T shape) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force gy fshape
| 1, fshape => force (- gy) fshape
| (n+2), fshape => T.error "sub: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x, y⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| ⟦x₁, x₂⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x₁, x₂⟧, 1, ishape, H_at_idx, H_pre => by prove_ocont
| xs, (n+2), ishape, H_at_idx, H_pre => by idx_over

end sub

section open sub
noncomputable
def sub (shape : S) : det.op [shape, shape] shape :=
  det.op.mk "sub" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace div

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape]) : T shape := xs.head / xs.head2
noncomputable
def f_pre {shape : S} : precondition [shape, shape] := λ xs => 0 < T.square xs.head2

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : T shape) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (gy / xs.head2) fshape
| 1, fshape => force (- (gy * xs.head) / (T.square xs.head2)) fshape
| (n+2), fshape => T.error "div: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦x, y⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| ⟦x₁, x₂⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp
| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦x₁, x₂⟧, 1, ishape, H_at_idx, H_pre => by prove_ocont
| xs, (n+2), ishape, H_at_idx, H_pre => by idx_over

end div

namespace sum


noncomputable
def f {shape : S} (xs : Dvec T [shape]) : TReal := T.sum xs.head
def f_pre {shape : S} : precondition [shape] := λ xs => True
noncomputable
def f_pb {shape : S} (xs : Dvec T [shape]) (y gy : TReal) (idx : Nat) (fshape : S) : T fshape := force (T.const gy shape) fshape

section open sum
-- TODO(dhs): why won't it find `f` without `sum.`? Bug in Lean?
noncomputable
def sum (shape : S) : det.op [shape] [] :=
  det.op.mk "sum" sum.f sum.f_pre sum.f_pb sum.f_odiff sum.f_pb_correct sum.f_ocont
end

namespace gemm

noncomputable
def f {m n p : TReal} (xs : Dvec T [[m, n], [n, p]]) : T [m, p] := gemm xs.head xs.head2
noncomputable
def f_pre {m n p : TReal} : precondition [[m, n], [n, p]] := λ xs => True
noncomputable
def f_pb {m n p : TReal} (xs : Dvec T [[m, n], [n, p]]) (y gy : T [m, p]) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (T.gemm gy (transpose $ xs.head2)) fshape
| 1, fshape => force (T.gemm (transpose $ xs.head) gy) fshape
| (n+2), fshape => T.error "gemm: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {m n p : TReal} : is_odifferentiable (@f m n p) (@f_pre m n p)
| ⟦x₁, x₂⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by { let shape := [m, n]; prove_odiff }
| ⟦x₁, x₂⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by { let shape := [n, p]; prove_odiff }
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {m n p : TReal} : pullback_correct (@f m n p) (@f_pre m n p) (@f_pb m n p)
| ⟦x₁, x₂⟧, y, H_y, g_out, 0, fshape, H_fshape_at_idx, H_pre =>
    by
      clear f_pb_correct
      have H_fshape_eq : [m, n] = fshape := Eq.symm H_fshape_at_idx.right
      rw [H_fshape_eq]
      let k : T [m, p] → TReal := (λ θ => dot g_out θ)
      have H_grad : ∇ k y = g_out := by { change ∇ (λ θ=>dot g_out θ) y = g_out; rw [certigrad.T.grad_dot₂] }
      rw [← H_grad]
      subst H_y
      simp; dsimp
      rw [← T.grad_tmulT, T.grad_gemm₁ k]

| ⟦x₁, x₂⟧, y, H_y, g_out, 1, fshape, H_fshape_at_idx, H_pre =>
    by
      clear f_pb_correct
      have H_fshape_eq : [n, p] = fshape := Eq.symm H_fshape_at_idx.right
      subst H_fshape_eq
      let k : T [m, p] → TReal := (λ θ => dot g_out θ)
      have H_grad : ∇ k y = g_out := by { change ∇ (λ θ=>dot g_out θ) y = g_out; rw [certigrad.T.grad_dot₂] }
      rw [← H_grad]
      subst H_y
      simp; dsimp
      rw [← T.grad_tmulT, T.grad_gemm₂ k]

| xs, y, H_y, g_out, (n+2), fshape, H_fshape_at_idx, H_pre =>
    False.elim (at_idx_over H_fshape_at_idx (by decide))

lemma f_ocont {m n p : TReal} : is_ocontinuous (@f m n p) (@f_pre m n p)
| ⟦x₁, x₂⟧, 0, ishape, H_at_idx, H_pre => by { let shape := [m, n]; prove_ocont }
| ⟦x₁, x₂⟧, 1, ishape, H_at_idx, H_pre => by { let shape := [n, p]; prove_ocont }
| xs, (n+2), ishape, H_at_idx, H_pre => by idx_over

end gemm

section open gemm
noncomputable
def gemm (m n p : TReal) : det.op [[m, n], [n, p]] [m, p] :=
  det.op.mk "gemm" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace mvn_kl

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape]) : TReal := mvn_kl xs.head xs.head2
noncomputable
def f_pre {shape : S} : precondition [shape, shape] := λ xs => 0 < xs.head2

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : TReal) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (gy • xs.head) fshape
| 1, fshape => force (gy • (xs.head2 - (1 / xs.head2))) fshape
| (n+2), fshape => T.error "mvn_kl: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦μ, σ⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦μ, σ⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦μ, σ⟧, y, H_y, g_out, 0, fshape, H_fshape_at_idx, H_pre =>
    by
      clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_fshape_at_idx.right
      subst H_fshape_eq
      let k : TReal → TReal := λ x => x * g_out
      have H_k_grad : ∇ k y = g_out := by { erw [T.grad_mul₁ id, T.grad_id, one_mul] }
      rw [← H_k_grad]
      subst H_y
      dsimp
      simp
      rw [← T.grad_tmulT]
      simplifyGrad
      simp [T.smul.def]

| ⟦μ, σ⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    let H_σ₂ := square_pos_of_pos H_pre
    let H_diff₁ := by proveDifferentiable
    let H_diff₂ := by proveDifferentiable
    by
      clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      let k : TReal → TReal := λ x => x * g_out

      have H_k_grad : ∇ (λ x => x * g_out) y = g_out := by { erw [T.grad_mul₁ id, T.grad_id, one_mul] }
      rw [← H_k_grad]
      subst H_y
      dsimp
      simp
      rw [← T.grad_tmulT]
      unfold T.mvn_kl
      dsimp [force]
      simplifyGrad
      simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero,
            T.const_one, T.const_bit0, T.const_bit1, T.const_inv,
            left_distrib, right_distrib]
      rw [T.mul_inv_cancel two_pos]
      erw [T.neg_div]
      simp [mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm]
      apply congr_arg; apply congr_arg
      simp only [T.mul_div_mul, square]
      rw [← mul_assoc, T.mul_div_mul, (@T.div_self_square _ σ H_pre)]
      simp
      rw [T.mul_inv_cancel two_pos]
      simp
      rw [T.div_mul_inv]

| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦μ, σ⟧, 0, ishape, H_at_idx, H_pre => by { prove_ocont; apply T.continuous_mvn_kl₁; exact H_pre }
| ⟦μ, σ⟧, 1, ishape, H_at_idx, H_pre => by { prove_ocont }
| ⟦μ, σ⟧, (n+2), ishape, H_at_idx, H_pre => by idx_over

end mvn_kl

section open mvn_kl
noncomputable
def mvn_kl (shape : S) : det.op [shape, shape] [] :=
  det.op.mk "mvn_kl" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace mul_add

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape, shape]) : T shape := (xs.head * xs.head2) + xs.head3
noncomputable
def f_pre {shape : S} : precondition [shape, shape, shape] := λ xs => True
noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape, shape]) (y gy : T shape) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (gy * xs.head2) fshape
| 1, fshape => force (gy * xs.head) fshape
| 2, fshape => force gy fshape
| (n+3), _ => T.error "mul_add: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦z, σ, μ⟧, H_pre, 0, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦z, σ, μ⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦z, σ, μ⟧, H_pre, 2, fshape, H_at_idx, k, H_k => by prove_odiff
| xs, H_pre, (n+3), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦z, σ, μ⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      subst H_y
      simp
      rw [← certigrad.T.grad_tmulT]
      dsimp [force]
      simplifyGrad
      simp

| ⟦z, σ, μ⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      -- simp only [mul_comm, add_comm]
      dsimp
      rw [← T.grad_tmulT]
      simplifyGrad
      rfl

| ⟦z, σ, μ⟧, y, H_y, g_out, 2, fshape, H_at_idx, H_pre =>
    by
      try clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      have H_k_grad :  g_out = ∇ (λ z => T.dot z g_out) y := by
          rw [certigrad.T.grad_dot₁]
      rw [ H_k_grad ]
      -- simp (config := { contextual := true }) only [mul_comm, add_comm]
      dsimp
      rw [← T.grad_tmulT]
      simplifyGrad
      rfl

| xs, y, H_y, g_out, (n+3), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦z, σ, μ⟧, 0, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦z, σ, μ⟧, 1, ishape, H_at_idx, H_pre => by prove_ocont
| ⟦z, σ, μ⟧, 2, ishape, H_at_idx, H_pre => by prove_ocont
| xs, (n+3), ishape, H_at_idx, H_pre => by idx_over

end mul_add

section open mul_add
noncomputable
def mul_add (shape : S) : det.op [shape, shape, shape] shape :=
  det.op.mk "mul_add" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace bernoulli_neglogpdf

noncomputable
def f {shape : S} (xs : Dvec T [shape, shape]) : TReal := bernoulli_neglogpdf xs.head xs.head2
noncomputable
def f_pre {shape : S} : precondition [shape, shape] := λ xs => 0 < xs.head ∧ xs.head < 1

noncomputable
def f_pb {shape : S} (xs : Dvec T [shape, shape]) (y gy : TReal) : Π (idx : Nat) (fshape : S), T fshape
| 0, fshape => force (gy • (1 - xs.head2) / (eps shape + (1 - xs.head)) - gy • (xs.head2 / (eps shape + xs.head))) fshape
| 1, fshape => force (gy • T.log (eps shape + (1 - xs.head)) - gy • T.log (eps shape + xs.head)) fshape
| (n+2), fshape => T.error "bernoulli_neglogpdf: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦p, z⟧, H_pre, 0, fshape, H_at_idx, k, H_k =>
    have H_p₁ : p > 0 := H_pre.left
    have H_p₂ : p < 1 := H_pre.right
    by prove_odiff

| ⟦p, z⟧, H_pre, 1, fshape, H_at_idx, k, H_k => by prove_odiff
| ⟦μ, σ⟧, H_pre, (n+2), fshape, H_at_idx, k, H_k => by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦p, z⟧, y, H_y, g_out, 0, fshape, H_at_idx, H_pre =>
    let H_p := H_pre.left
    let H_1mp := lt1_alt H_pre.right
    let H_diff₁ := by proveDifferentiable
    let H_diff₂ := by proveDifferentiable
    by
      clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      let k : TReal → TReal := λ x => x * g_out
      have H_k_grad : ∇ k y = g_out := by erw [T.grad_mul₁ id, T.grad_id, one_mul]
      rw [← H_k_grad]
      subst H_y
      dsimp
      simp
      rw [← T.grad_tmulT]
      unfold T.bernoulli_neglogpdf
      rw [T.grad_binary (λ θ₁ θ₂ => g_out * - T.sum (z * T.log (eps shape + θ₁) + (1 - z) * T.log (eps shape + (1 - θ₂)))) _ H_diff₁ H_diff₂]
      dsimp
      let H₁ := H_pre.left
      let H₂ := lt1_alt H_pre.right
      simplifyGrad
      simp [T.smul.def, T.neg_div, T.const_neg]
      rw [T.mul_div_mul]
      simp [T.div_mul_inv]

| ⟦p, z⟧, y, H_y, g_out, 1, fshape, H_at_idx, H_pre =>
    let H_diff₁ := by proveDifferentiable
    let H_diff₂ := by proveDifferentiable
    by
      clear f_pb_correct
      have H_fshape_eq : shape = fshape := Eq.symm H_at_idx.right
      subst H_fshape_eq
      let k : TReal → TReal := λ x => x * g_out
      have H_k_grad : ∇ k y = g_out := by erw [T.grad_mul₁ id, T.grad_id, one_mul]
      rw [← H_k_grad]
      subst H_y
      dsimp
      simp
      rw [← T.grad_tmulT]
      unfold T.bernoulli_neglogpdf
      rw [T.grad_binary (λ θ₁ θ₂ => g_out * - T.sum (θ₁ * T.log (eps shape + p) + (1 - θ₂) * T.log (eps shape + (1 - p)))) _ H_diff₁ H_diff₂]
      dsimp
      simplifyGrad
      simp [T.smul.def, const_neg]

| xs, y, H_y, g_out, (n+2), fshape, H_at_idx, H_pre => by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦μ, σ⟧, 0, ishape, H_at_idx, H_pre => by { prove_ocont_init; apply continuous_bernoulli_neglogpdf₁; exact H_pre.left; exact lt1_alt H_pre.right }
| ⟦μ, σ⟧, 1, ishape, H_at_idx, H_pre => by { prove_ocont_init; apply continuous_bernoulli_neglogpdf₂; exact H_pre.left; exact lt1_alt H_pre.right }
| ⟦μ, σ⟧, (n+2), ishape, H_at_idx, H_pre => by idx_over

end bernoulli_neglogpdf

section
open bernoulli_neglogpdf
noncomputable
def bernoulli_neglogpdf (shape : S) : det.op [shape, shape] [] :=
  det.op.mk "bernoulli_neglogpdf" f f_pre f_pb f_odiff f_pb_correct f_ocont
end


end ops

end certigrad
