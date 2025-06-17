/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Certified graph transformation that "reparameterizes" a specific occurrence of a stochastic choice.
-/
import CertiGrad.Util
import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.ComputeGrad
import CertiGrad.Graph
import CertiGrad.Tactics
import CertiGrad.Ops
import CertiGrad.Predicates
import CertiGrad.ExpectedValue

import CertiGrad.Lemmas
import CertiGrad.Env

namespace certigrad
open List
open util_list

section algebra
open T

lemma mvn_transform {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
  mvn_pdf μ σ x = (prod σ⁻¹) * mvn_pdf 0 1 ((x - μ) / σ) := by
  calc mvn_pdf μ σ x
    = prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) := rfl
    _ = prod ((sqrt (2 * pi shape) * σ)⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) := by rw [sqrt_mul, sqrt_square]
    _ = prod (((sqrt (2 * pi shape))⁻¹ * σ⁻¹) * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) := by rw [T.mul_inv_pos (sqrt_pos two_pi_pos) H_σ]
    _ = (prod σ⁻¹) * prod ((sqrt (2 * pi shape))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ))) := by simp [prod_mul]; ring
    _ = (prod σ⁻¹) * prod ((sqrt ((2 * pi shape) * square 1))⁻¹ * exp ((- 2⁻¹) * (square ((((x - μ) / σ) - 0) / 1)))) := by simp [T.div_one, square]
    _ = (prod σ⁻¹) * mvn_pdf 0 1 ((x - μ) / σ) := rfl

end algebra

open sprog

lemma mvn_reparam_same {shape oshape : S} {μ σ : T shape} (f : Dvec T [shape] → T oshape) (H_σ_pos : σ > 0) :
  E (prim (rand.op.mvn shape) ⟦μ, σ⟧) f =
    E (bind (prim (rand.op.mvn_std shape) ⟦⟧) (fun (x : Dvec T [shape]) => ret ⟦(x.head * σ) + μ⟧)) f := by
  -- simp only [E.E_bind, E.E_ret]
  simp [E, rand.op.pdf, T.dintegral, Dvec.head, rand.pdf.mvn, rand.pdf.mvn_std]
  simp only [fun x => mvn_transform μ σ x H_σ_pos]

  have H : ∀ (x : T shape), ((σ * x + μ -μ) / σ) = x := by
    intro x
    simp [T.div_mul_inv]
    have H: σ * x * σ⁻¹ = x * (σ * σ⁻¹) := by ring
    simp [H, T.mul_inv_cancel H_σ_pos]

  let g : T shape → T oshape := fun (x : T shape) => T.mvn_pdf 0 1 ((x - μ) / σ) • f ⟦x⟧
  have H_rhs : ∀ (x : T shape), T.mvn_pdf 0 1 x • f ⟦x * σ + μ⟧ = g (σ * x + μ) | x => by simp only [g, H, mul_comm]
  rw [funext H_rhs, T.integral_scale_shift_var g]
  unfold g
  simp only [T.smul_group]

def reparameterize_pre (eshape : S) : List Node → Env → Prop
| [], inputs => True
| (⟨⟨ref, shape⟩, [⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩], Operator.rand (rand.op.mvn .(shape))⟩::nodes), inputs =>
  eshape = shape ∧ σ ≠ μ ∧ 0 < env.get (σ, shape) inputs
| (⟨ref, parents, Operator.det op⟩::nodes), inputs => reparameterize_pre eshape nodes (env.insert ref (op.f (env.getKs parents inputs)) inputs)
| (⟨ref, parents, Operator.rand op⟩::nodes), inputs => ∀ x, reparameterize_pre eshape nodes (env.insert ref x inputs)

noncomputable def reparameterize (fname : ID) : List Node → List Node
| [] => []

| (⟨⟨ident, shape⟩, [⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩], Operator.rand (rand.op.mvn .(shape))⟩::nodes) =>
  (⟨(fname, shape), [],                                       Operator.rand (rand.op.mvn_std shape)⟩
  ::⟨(ident, shape),   [(fname, shape), (σ, shape), (μ, shape)], Operator.det (ops.mul_add shape)⟩
  ::nodes)
| (n :: nodes) => n :: reparameterize fname nodes

theorem reparameterize_correct (costs : List ID) :
  ∀ (nodes : List Node) (inputs: Env) (fref : Reference),
    reparameterize_pre fref.2 nodes inputs →
    uniqIds nodes inputs →
    allParentsInEnv inputs nodes →
    ¬ env.hasKey fref inputs → fref ∉ map Node.ref nodes →
    fref.1 ∉ costs →
    E (graph.toDist (fun env₀ => ⟦sumCosts env₀ costs⟧) inputs (reparameterize fref.1 nodes)) Dvec.head =
    E (graph.toDist (fun env₀ => ⟦sumCosts env₀ costs⟧) inputs nodes) Dvec.head
| [], _ , _, _, _, _, _, _, _ => rfl
| (⟨(ident, shape), [ ⟨μ, .(shape)⟩, ⟨σ, .(shape)⟩ ], Operator.rand (rand.op.mvn .(shape))⟩ :: nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
        unfold reparameterize
        have H_eshape : fref.2 = shape := H_pre.left
        have H_fref : fref = (fref.1, shape) := by cases fref; dsimp at H_eshape; rw [H_eshape]
        have H_σ_μ : σ ≠ μ := H_pre.right.left
        have H_μ_in : env.hasKey (μ, shape) inputs := H_ps_in_env.left (μ, shape) (by simp)
        have H_σ_in : env.hasKey (σ, shape) inputs := H_ps_in_env.left (σ, shape) (by simp)
        have H_ident_nin : ¬ env.hasKey (ident, shape) inputs := H_uids.left
        have H_μ_neq_ident : (μ, shape) ≠ (ident, shape) := env_in_nin_ne H_μ_in H_ident_nin
        have H_σ_neq_ident : (σ, shape) ≠ (ident, shape) := env_in_nin_ne H_σ_in H_ident_nin
        have H_μ_neq_fref : (μ, shape) ≠ (fref.1, shape) := Eq.recOn H_fref (env_in_nin_ne H_μ_in H_fresh₁)
        have H_σ_neq_fref : (σ, shape) ≠ (fref.1, shape) := Eq.recOn H_fref (env_in_nin_ne H_σ_in H_fresh₁)
        have H_ident_neq_fref : (ident, shape) ≠ (fref.1, shape) := Eq.recOn H_fref (mem_not_mem_neq mem_of_cons_same H_fresh₂)

        simp only [graph.toDist, Operator.toDist, env.getKs]
        simp only [E.E_bind, E.E_ret]
        erw [mvn_reparam_same _ H_pre.right.right]
        simp only [E.E_ret, E.E_bind]
        apply congrArg
        apply funext
        intro x
        rw [env.insert_insert_flip _ _ _ H_ident_neq_fref]
        let fval : T shape := Dvec.head x
        let fval_inputs: Env := env.insert (ident, shape)
          (det.op.f (ops.mul_add shape)
            ⟦Dvec.head x, (env.get (σ, shape) inputs : T shape), (env.get (μ, shape) inputs : T shape)⟧)
          inputs
        have H_ps_in_env_next : allParentsInEnv fval_inputs nodes := H_ps_in_env.right _
        have H_fresh₁_next : ¬ env.hasKey (fref.1, shape) fval_inputs := by
            have H_fref_neq_ident : (fref.1, shape) ≠ (ident, shape) := by
              exact Ne.symm H_ident_neq_fref
            apply env_not_has_key_insert
            exact H_fref_neq_ident
            rw [H_fref] at H_fresh₁
            exact H_fresh₁
        have H_fresh₂_next : (fref.1, shape) ∉ nodes.map Node.ref := Eq.recOn H_fref (not_mem_of_not_mem_cons H_fresh₂)

        simp only [env.get_insert_same, env.get_insert_diff  _ _ H_σ_neq_fref, env.get_insert_diff  _ _ H_μ_neq_fref]
        erw [@to_dist_congr_insert costs nodes fval_inputs (fref.1, shape) fval H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost]
        simp only [fval_inputs]
        congr
| (⟨(ref, shape), [], Operator.det op⟩::nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
      unfold reparameterize graph.toDist
      simp only [E.E_bind, E.E_ret]
      let x : T shape := op.f (env.getKs [] inputs)
      have H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre
      have H_ps_in_env_next : allParentsInEnv (env.insert (ref, shape) x inputs) nodes := H_ps_in_env.right x
      have H_fresh₁_next : ¬ env.hasKey fref (env.insert (ref, shape) x inputs) := env_not_has_key_insert (ne_of_not_mem_cons H_fresh₂) H_fresh₁
      have H_fresh₂_next : fref ∉ nodes.map Node.ref := not_mem_of_not_mem_cons H_fresh₂
      apply (reparameterize_correct _ _ _ fref H_pre_next (H_uids.right _) H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost)
| (⟨(ref, shape), [], Operator.rand op⟩::nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
    unfold reparameterize graph.toDist
    simp only [E.E_bind]
    apply congrArg
    apply funext
    intro x
    have H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) (Dvec.head x) inputs) := by apply H_pre
    have H_ps_in_env_next : allParentsInEnv (env.insert (ref, shape) (Dvec.head x) inputs) nodes := H_ps_in_env.right x.head
    have H_fresh₁_next : ¬ env.hasKey fref (env.insert (ref, shape) (Dvec.head x) inputs) := env_not_has_key_insert (ne_of_not_mem_cons H_fresh₂) H_fresh₁
    have H_fresh₂_next : fref ∉ nodes.map Node.ref := not_mem_of_not_mem_cons H_fresh₂
    apply (reparameterize_correct _  _  _ fref H_pre_next (H_uids.right _) H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost)
| (⟨(ref, shape), [(parent₁, shape₁)], Operator.det op⟩::nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
    unfold reparameterize graph.toDist
    simp only [E.E_bind, E.E_ret]
    let x : T shape := det.op.f op (env.getKs [(parent₁, shape₁)] inputs)
    have H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre
    have H_ps_in_env_next : allParentsInEnv (env.insert (ref, shape) x inputs) nodes := H_ps_in_env.right x
    have H_fresh₁_next : ¬ env.hasKey fref (env.insert (ref, shape) x inputs) := env_not_has_key_insert (ne_of_not_mem_cons H_fresh₂) H_fresh₁
    have H_fresh₂_next : fref ∉ nodes.map Node.ref := not_mem_of_not_mem_cons H_fresh₂
    apply (reparameterize_correct _ _ _ fref H_pre_next (H_uids.right _) H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost)

| (⟨(ref, shape), [(parent₁, shape₁), (parent₂, shape₂)], Operator.det op⟩::nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
    unfold reparameterize graph.toDist
    simp only [E.E_bind, E.E_ret]
    let x : T shape := det.op.f op (env.getKs [(parent₁, shape₁), (parent₂, shape₂)] inputs)
    have H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre
    have H_ps_in_env_next : allParentsInEnv (env.insert (ref, shape) x inputs) nodes := H_ps_in_env.right x
    have H_fresh₁_next : ¬ env.hasKey fref (env.insert (ref, shape) x inputs) := env_not_has_key_insert (ne_of_not_mem_cons H_fresh₂) H_fresh₁
    have H_fresh₂_next : fref ∉ nodes.map Node.ref := not_mem_of_not_mem_cons H_fresh₂
    apply (reparameterize_correct _ _ _ fref H_pre_next (H_uids.right _) H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost)

| (⟨(ref, shape), (parent₁, shape₁) :: (parent₂, shape₂) :: (parent₃, shape₃) :: parents, Operator.det op⟩::nodes), inputs, fref, H_pre, H_uids, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
  unfold reparameterize graph.toDist
  simp only [E.E_bind, E.E_ret]
  let x : T shape := det.op.f op (env.getKs ((parent₁, shape₁) :: (parent₂, shape₂) :: (parent₃, shape₃) :: parents) inputs)
  have H_pre_next : reparameterize_pre fref.2 nodes (env.insert (ref, shape) x inputs) := by apply H_pre
  have H_ps_in_env_next : allParentsInEnv (env.insert (ref, shape) x inputs) nodes := H_ps_in_env.right x
  have H_fresh₁_next : ¬ env.hasKey fref (env.insert (ref, shape) x inputs) := env_not_has_key_insert (ne_of_not_mem_cons H_fresh₂) H_fresh₁
  have H_fresh₂_next : fref ∉ nodes.map Node.ref := not_mem_of_not_mem_cons H_fresh₂
  apply (reparameterize_correct _ _ _ fref H_pre_next (H_uids.right _) H_ps_in_env_next H_fresh₁_next H_fresh₂_next H_not_cost)

noncomputable def reparam (g : Graph) : Graph :=
  Graph.mk (reparameterize (ID.str Label.ε) g.nodes) g.costs g.targets g.inputs

end certigrad
