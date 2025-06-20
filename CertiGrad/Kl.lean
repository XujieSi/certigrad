/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certified graph transformation that integrates out a specific KL divergence term.
-/


import CertiGrad.Util
import CertiGrad.Tensor
import CertiGrad.ComputeGrad
import CertiGrad.Graph
import CertiGrad.Tactics
import CertiGrad.Predicates
import CertiGrad.Lemmas
import CertiGrad.Env
import CertiGrad.ExpectedValue
import CertiGrad.Ops

namespace certigrad
open List

-- set_option trace.Debug.Meta.Tactic.simp true
set_option linter.unusedVariables false

noncomputable def integrate_mvn_kl (eloss : ID) : List Node → List Node
| [] => []

| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], Operator.rand (rand.op.mvn shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], Operator.det (det.op.mvn_empirical_kl shape')⟩
 ::nodes) =>
 (⟨(el, []), [⟨μ, shape⟩, ⟨σ, shape⟩], Operator.det (ops.mvn_kl shape)⟩
::⟨(z, shape), [⟨μ, shape⟩, ⟨σ, shape⟩], Operator.rand (rand.op.mvn shape)⟩
::nodes)

| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], Operator.rand (rand.op.mvn shape)⟩ :: nodes) =>
⟨(z, shape), [(μ, shape), (σ, shape)], Operator.rand (rand.op.mvn shape)⟩ :: integrate_mvn_kl eloss nodes

| (n::nodes) => n :: integrate_mvn_kl eloss nodes

noncomputable def integrate_mvn_kl_pre (eloss : ID) : List Node → Env → Prop
-- EQ1
| [],_ => True
-- EQ2 (a)
| (⟨(rname, rshape), [], Operator.det op⟩::nodes), inputs =>
integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs [] inputs)) inputs)
-- EQ2 (b)
| (⟨(rname, rshape), [], Operator.rand op⟩::nodes), inputs => False
-- EQ3 (a)
| (⟨(rname, rshape), [(pname, pshape)], Operator.det op⟩::nodes), inputs =>
integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs [(pname, pshape)] inputs)) inputs)
-- EQ3 (b)
| (⟨(rname, rshape), [(pname, pshape)], Operator.rand op⟩::nodes), inputs => False
-- EQ4
| (⟨(rname, rshape), [(pname₁, pshape₁), (pname₂, pshape₂)], Operator.det op⟩::nodes), inputs =>
integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs)
-- EQ5
| [⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩],inputs => False
-- EQ6
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [], op⟩::nodes), inputs => False
-- EQ7
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃)], op⟩::nodes), inputs => False
-- EQ8
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄)], op⟩::nodes), inputs => False
-- EQ9
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], Operator.det (det.op.mk _ _ _ _ _ _ _)⟩::nodes), inputs => False
-- EQ10
| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], Operator.rand (rand.op.mvn shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], Operator.det (det.op.mvn_empirical_kl shape')⟩
::nodes), inputs =>
(μ = μ' ∧ σ = σ' ∧ z = z' ∧ shape = shape' ∧ eloss = el ∧ σ ≠ μ)
∧ ((¬ env.hasKey (eloss, []) inputs) ∧ (eloss, []) ∉ (z, shape) :: map Node.ref nodes ∧ 0 < env.get (σ, shape) inputs ∧ ∀ (y : T shape), allParentsInEnv (env.insert (z, shape) y inputs) nodes)
-- EQ11
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], Operator.rand op⟩::nodes), inputs => False
-- EQ12
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), ((pname₃, shape₃)::(pname₄, shape₄)::(pname₅, shape₅)::parent::parents), op⟩::nodes), inputs => False
-- EQ13
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, (shape₂ :: shapes₂)), parents, op⟩::nodes), inputs => False
-- EQ14 (a)
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), Operator.det op⟩::nodes), inputs =>
integrate_mvn_kl_pre eloss nodes (env.insert (rname₂, shape₂) (op.f $ env.getKs ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents) inputs) inputs)
-- EQ14 (b)
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), Operator.rand op⟩::nodes), inputs => False

open util_list
open List
theorem integrate_mvn_kl_correct (eloss : ID) (costs : List ID) :
∀ (nodes : List Node) (inputs : Env),
  eloss ∉ costs →
  integrate_mvn_kl_pre eloss nodes inputs →
  uniqIds nodes inputs →
  allParentsInEnv inputs nodes →
  pdfsExistAt nodes inputs →
  isGintegrable (λ m => ⟦sumCosts m (eloss::costs)⟧) inputs (integrate_mvn_kl eloss nodes) Dvec.head →
  isGintegrable (λ m => ⟦sumCosts m (eloss::costs)⟧) inputs nodes Dvec.head →
E (graph.toDist (λ env₀ => ⟦sumCosts env₀ (eloss::costs)⟧) inputs (integrate_mvn_kl eloss nodes)) Dvec.head
=
E (graph.toDist (λ env₀ => ⟦sumCosts env₀ (eloss::costs)⟧) inputs nodes) Dvec.head

| [],_,_,_,_,_,_,_ ,_ => rfl

-- EQ2 (a)
| (⟨(rname, rshape), [], Operator.det op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => by
  simp only [graph.toDist, Operator.toDist, integrate_mvn_kl]
  simp only [integrate_mvn_kl_pre] at H_pre
  simp only [E.E_bind, E.E_ret]
  have H_pre_next : integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs nil inputs)) inputs) := H_pre
  have H_ps_in_env_next : allParentsInEnv (env.insert (rname, rshape) (op.f (env.getKs nil inputs)) inputs) nodes := H_ps_in_env.right _
  exact (integrate_mvn_kl_correct _ _ _ _ H_eloss_not_cost H_pre_next (H_uids.right _) H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
-- EQ2 (b)
| (⟨(rname, rshape), [], Operator.rand op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ3 (a)
| (⟨(rname, rshape), [(pname, pshape)], Operator.det op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => by
  simp only [graph.toDist, Operator.toDist, integrate_mvn_kl]
  simp only [integrate_mvn_kl_pre] at H_pre
  simp only [E.E_bind, E.E_ret]
  have H_pre_next : integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs [(pname, pshape)] inputs)) inputs) := H_pre
  have H_ps_in_env_next : allParentsInEnv (env.insert (rname, rshape) (op.f (env.getKs [(pname, pshape)] inputs)) inputs) nodes := H_ps_in_env.right _
  exact (integrate_mvn_kl_correct _ _ _ _ H_eloss_not_cost H_pre_next (H_uids.right _) H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
-- EQ3 (b)
| (⟨(rname, rshape), [(pname, pshape)], Operator.rand op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ4
| (⟨(rname, rshape), [(pname₁, pshape₁), (pname₂, pshape₂)], Operator.det op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => by
  simp only [graph.toDist, Operator.toDist, integrate_mvn_kl]
  simp only [integrate_mvn_kl_pre] at H_pre
  simp only [E.E_bind, E.E_ret]
  have H_pre_next : integrate_mvn_kl_pre eloss nodes (env.insert (rname, rshape) (op.f (env.getKs [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs) := H_pre
  have H_ps_in_env_next : allParentsInEnv (env.insert (rname, rshape) (op.f (env.getKs [(pname₁, pshape₁), (pname₂, pshape₂)] inputs)) inputs) nodes := H_ps_in_env.right _
  exact (integrate_mvn_kl_correct _ _ _ _ H_eloss_not_cost H_pre_next (H_uids.right _) H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)

-- EQ5
| [⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩],inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ6
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [], op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ7
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃)], op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ8
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄)], op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ9
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], Operator.det (det.op.mk _ _ _ _ _ _ _)⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ11
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), [(pname₃, shape₃), (pname₄, shape₄), (pname₅, shape₅)], Operator.rand op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ12
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, []), ((pname₃, shape₃)::(pname₄, shape₄)::(pname₅, shape₅)::parent::parents), op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ13
| (⟨(rname, .(shape)), [(pname₁, .(shape)), (pname₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩
  ::⟨(rname₂, (shape₂ :: shapes₂)), parents, op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), Operator.det op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => by
  simp only [graph.toDist, Operator.toDist, integrate_mvn_kl]
  simp only [integrate_mvn_kl_pre] at H_pre
  simp only [E.E_bind, E.E_ret]
  have H_pre_next : integrate_mvn_kl_pre eloss nodes (env.insert (rname₂, shape₂) (op.f (env.getKs ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents) inputs)) inputs) := H_pre
  have H_ps_in_env_next : allParentsInEnv (env.insert (rname₂, shape₂) (op.f (env.getKs ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents) inputs)) inputs) nodes := H_ps_in_env.right _
  exact (integrate_mvn_kl_correct _ _ _ _ H_eloss_not_cost H_pre_next (H_uids.right _) H_ps_in_env_next H_pdfs_exist_at H_kl_gint H_gint)
| (⟨(rname₂, shape₂), ((pname₃, shape₃)::(pname₄, shape₄)::parent::parents), Operator.rand op⟩::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => False.rec _ H_pre

-- EQ10
| (⟨(z, .(shape)), [(μ, .(shape)), (σ, .(shape))], Operator.rand (rand.op.mvn shape)⟩
 ::⟨(el, []), [(μ', .(shape')), (σ', .(shape')), (z', .(shape'))], Operator.det (det.op.mvn_empirical_kl shape')⟩
 ::nodes),inputs,H_eloss_not_cost,H_pre,H_uids,H_ps_in_env,H_pdfs_exist_at,H_kl_gint,H_gint => by
  have H_ok : μ = μ' ∧ σ = σ' ∧ z = z' ∧ shape = shape' ∧ eloss = el ∧ σ ≠ μ := H_pre.left
  let ⟨ H_μ, H_σ, H_z, H_shape, H_eloss_eq_el, H_σ_neq_μ⟩ := H_ok
  subst H_μ H_σ H_z H_shape H_eloss_eq_el
  dsimp only [graph.toDist, Operator.toDist, integrate_mvn_kl]
  simp only [E.E_bind, E.E_ret]
  -- dsimp only [Dvec.head]

  have H_μ_in : env.hasKey (μ, shape) inputs := H_ps_in_env.left (μ, shape) (List.mem_cons_self)
  have H_σ_in : env.hasKey (σ, shape) inputs := H_ps_in_env.left (σ, shape) (List.mem_cons_of_mem _ (List.mem_cons_self))
  have H_z_nin : ¬ env.hasKey (z, shape) inputs := H_uids.left
  have H_eloss_nin : ¬ env.hasKey (eloss, []) inputs := H_pre.right.left

  have H_μ_neq_z : (μ, shape) ≠ (z, shape) := env_in_nin_ne H_μ_in H_z_nin
  have H_σ_neq_z : (σ, shape) ≠ (z, shape) := env_in_nin_ne H_σ_in H_z_nin
  have H_μ_neq_eloss : (μ, shape) ≠ (eloss, []) := env_in_nin_ne H_μ_in H_eloss_nin
  have H_σ_neq_eloss : (σ, shape) ≠ (eloss, []) := env_in_nin_ne H_σ_in H_eloss_nin

  have H_eloss_neq_z : (eloss, []) ≠ (z, shape) := ne_of_not_mem_cons H_pre.right.right.left
  have H_eloss_nin_nodes : (eloss, []) ∉ map Node.ref nodes := not_mem_of_not_mem_cons H_pre.right.right.left


  dsimp only  [env.getKs]
  unfold det.op.f ops.mvn_kl ops.mvn_kl.f  Dvec.head2 Dvec.head3

  -- set mvn_kl := (((ops.mvn_kl shape).f (env.get (μ, shape) inputs ::: env.get (σ, shape) inputs ::: Dvec.dnil))::: Dvec.dnil).head

  simp only  [env.get_insert_diff _ _ (H_σ_neq_eloss)]
  simp only  [env.get_insert_diff _ _ (H_μ_neq_eloss)]
  simp only  [env.get_insert_diff _ _ H_μ_neq_z]
  simp only  [env.get_insert_diff _ _ H_σ_neq_z]
  simp only  [env.get_insert_same]
  simp only [ @env.insert_insert_flip _ _ _ _ inputs (Ne.symm H_eloss_neq_z)]


  dsimp only [sumCosts, sumr, map]
  let k₁ : Env → TReal := λ (env₀ : Env) => env.get (eloss, []) env₀
  let k₂ : Env → TReal := λ (env₀ : Env) => sumr (map (λ (cost : ID) => env.get (cost, []) env₀) costs)

  let m_lhs_k_add : Dvec T [shape] → Env := λ (x : Dvec T [shape]) => env.insert (eloss, []) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
                                                                             (env.insert (z, shape) (Dvec.head x) inputs)

  let k₁ : Env → TReal := λ (m : Env) => env.get (eloss, []) m
  let k₂ : Env → TReal := λ (m : Env) => sumr (map (λ (cost : ID) => env.get (cost, []) m) costs)
  let m_lhs_k_add : Dvec T [shape] → Env := λ (x : Dvec T [shape]) => env.insert (eloss, [])
          ((env.get (μ, shape) inputs ::: env.get (σ, shape) inputs ::: Dvec.dnil).head.mvn_kl
                (env.get (σ, shape) inputs) :::
              Dvec.dnil).head
          (env.insert (z, shape) x.head inputs)


  have H_lhs_kint₁ : ∀ (x : Dvec T [shape]), isGintegrable (λ m => k₁ m ::: Dvec.dnil) (m_lhs_k_add x) nodes (Dvec.head) := by sorry

  have H_lhs_kint₂ : ∀ (x : Dvec T [shape]), isGintegrable (λ m => k₂ m ::: Dvec.dnil) (m_lhs_k_add x) nodes (Dvec.head) := by sorry
  -- have H₁ := (λ (x : Dvec T [shape]) => E.E_k_add k₁ k₂ (m_lhs_k_add x) nodes (H_lhs_kint₁ x) (H_lhs_kint₂ x))
  -- simp only [H₁]
  conv =>
    pattern (E  _ Dvec.head)
    rw [E.E_k_add _ _ _ _ (H_lhs_kint₁ x) (H_lhs_kint₂ x)]


  let m_rhs_k_add : Dvec T [shape] → Env := λ (x : Dvec T [shape]) => env.insert (eloss, [])
      ((env.get (μ, shape) inputs ::: env.get (σ, shape) inputs ::: x.head ::: Dvec.dnil).head.mvn_empirical_kl
            (env.get (σ, shape) inputs) x.head :::
          Dvec.dnil).head
      (env.insert (z, shape) x.head inputs)
  have H_rhs_kint₁: ∀ (x : Dvec T [shape]), isGintegrable (λ m => k₁ m ::: Dvec.dnil) (m_rhs_k_add x) nodes (Dvec.head) := by sorry
  have H_rhs_kint₂: ∀ (x : Dvec T [shape]), isGintegrable (λ m => k₂ m ::: Dvec.dnil) (m_rhs_k_add x) nodes (Dvec.head) := by sorry

  conv =>
    rhs
    pattern (E _  Dvec.head)
    rw [E.E_k_add _ _ _ _ (H_rhs_kint₁ x) (H_rhs_kint₂ x)]




  set d_base := sprog.prim (rand.op.mvn shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧
  set lhs_f₁ := λ x => E (graph.toDist (λ (m : Env) => k₁ m ::: Dvec.dnil) (m_lhs_k_add x) nodes) Dvec.head
  set lhs_f₂ := λ x => E (graph.toDist (λ (m : Env) => k₂ m ::: Dvec.dnil) (m_lhs_k_add x) nodes) Dvec.head

  have H_E_kl_add :
  ∀ x, E (graph.toDist (λ (m : Env) => ⟦env.get (eloss, []) m + sumr (map (λ (cost : ID) => env.get (cost, []) m) costs)⟧)
              (env.insert (z, shape) x
                          (env.insert (eloss, []) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
              nodes)
        Dvec.head
  =
  E (graph.toDist (λ (m : Env) => ⟦k₁ m⟧)
              (env.insert (z, shape) x
                          (env.insert (eloss, @nil ℕ) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
              nodes)
        Dvec.head
  +
  E (graph.toDist (λ (m : Env) => ⟦k₂ m⟧)
              (env.insert (z, shape) x
                          (env.insert (eloss, @nil ℕ) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape)) inputs))
              nodes)
        Dvec.head := by sorry
  have H_lhs_eint₁ : E.is_eintegrable d_base lhs_f₁ := by sorry
  have H_lhs_eint₂ : E.is_eintegrable d_base lhs_f₂ := by sorry

  erw [E.E_add d_base lhs_f₁ lhs_f₂ H_lhs_eint₁ H_lhs_eint₂]

  set rhs_f₁ := λ x => E (graph.toDist (λ (m : Env) => ⟦k₁ m⟧) (m_rhs_k_add x) nodes) Dvec.head
  set rhs_f₂ := λ x => E (graph.toDist (λ (m : Env) => ⟦k₂ m⟧) (m_rhs_k_add x) nodes) Dvec.head

  dsimp [graph.toDist, Operator.toDist, isGintegrable, integrate_mvn_kl, Dvec.head] at H_gint
  simp only [E.E_bind, E.E_ret, det.op.f, Dvec.head, env.getKs, sumCosts] at H_gint
  simp only [env.get_insert_diff, env.get_insert_same, H_σ_neq_eloss, H_μ_neq_eloss, H_eloss_neq_z] at H_gint

  have H_rhs_eint₁ : E.is_eintegrable d_base rhs_f₁ := by sorry
  have H_rhs_eint₂ : E.is_eintegrable d_base rhs_f₂ := by sorry

  erw [E.E_add d_base rhs_f₁ rhs_f₂ H_rhs_eint₁ H_rhs_eint₂]

  have H_term₁_lhs :
  ∀ (x : Dvec T [shape]),
  E (graph.toDist (λ (m : Env) => ⟦(λ (m : Env) => env.get (eloss, []) m) m⟧)
                 (env.insert (eloss, []) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
                              (env.insert (z, shape) (Dvec.head x) inputs))
                 nodes)
   Dvec.head
=
T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) := by sorry

  have H_term₁_rhs :
  ∀ (x : Dvec T [shape]),
  E (graph.toDist (λ (m : Env) => ⟦(λ (m : Env) => env.get (eloss, []) m) m⟧)
                 (env.insert (eloss, [])
                   (T.mvn_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (Dvec.head x))
               (env.insert (z, shape) (Dvec.head x) inputs))
            nodes)
         Dvec.head
=
T.mvn_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (Dvec.head x) := by sorry

  have H_term₁ :
  E (sprog.prim (rand.op.mvn shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧)
    (λ (x : Dvec T [shape]) =>
       E
         (graph.toDist (λ (m : Env) => ⟦(λ (m : Env) => env.get (eloss, []) m) m⟧)
            (env.insert (eloss, []) (T.mvn_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape))
               (env.insert (z, shape) (Dvec.head x) inputs))
            nodes)
         Dvec.head)
= E (sprog.prim (rand.op.mvn shape) ⟦env.get (μ, shape) inputs, env.get (σ, shape) inputs⟧)
    (λ (x : Dvec T [shape]) =>
         E (graph.toDist (λ (m : Env) => ⟦(λ (m : Env) => env.get (eloss, []) m) m⟧)
                          (env.insert (eloss, [])
                                       (T.mvn_empirical_kl (env.get (μ, shape) inputs : T shape) (env.get (σ, shape) inputs : T shape) (Dvec.head x))
                                       (env.insert (z, shape) (Dvec.head x) inputs))
            nodes)
         Dvec.head) := by sorry
  erw [H_term₁]
  apply congr_arg
  apply congr_arg
  apply funext
  intro x
  have H_ps_in_env : allParentsInEnv (env.insert (z, shape) (Dvec.head x) inputs) nodes := by apply H_pre.right.right.right.right
  -- dsimp
  unfold lhs_f₂ rhs_f₂
  erw [to_dist_congr_insert H_ps_in_env (env_not_has_key_insert H_eloss_neq_z H_eloss_nin) H_eloss_nin_nodes H_eloss_not_cost]
  erw [to_dist_congr_insert H_ps_in_env (env_not_has_key_insert H_eloss_neq_z H_eloss_nin) H_eloss_nin_nodes H_eloss_not_cost]







def integrate_kl_pre : Graph → Env → Prop
| g, m => integrate_mvn_kl_pre (g.costs.head!) g.nodes m

noncomputable def integrate_kl : Graph → Graph
| g => ⟨integrate_mvn_kl (g.costs.head!) g.nodes, g.costs, g.targets, g.inputs⟩

end certigrad
