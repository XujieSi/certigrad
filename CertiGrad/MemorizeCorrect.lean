/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that the memoization part of stochastic backpropagation is correct.
-/
import CertiGrad.Graph
import CertiGrad.Estimators
import CertiGrad.Predicates
import CertiGrad.ComputeGrad

import Mathlib.Data.List.Nodup
namespace certigrad
namespace theorems
open List

lemma step_congr (costs : List ID) (callback₁ callback₂ : List Node → Π (tgt : Reference), T tgt.2)
                 (nodes : List Node) (m : Env) (tgt : Reference) :
   ∀ (n : Node)
    (H_callback_tgt : callback₁ nodes tgt = callback₂ nodes tgt)
    (H_callback_node : callback₁ nodes n.ref = callback₂ nodes n.ref),
    computeGradStep costs callback₁ (n::nodes) m tgt = computeGradStep costs callback₂ (n::nodes) m tgt
| ⟨ref, parents, Operator.det op⟩, H_callback_tgt, H_callback_node => by
  simp only [computeGradStep]
  rw [H_callback_tgt, H_callback_node]

| ⟨ref, parents, Operator.rand op⟩, H_callback_tgt, H_callback_node => by
  simp only [computeGradStep]
  rw [H_callback_tgt]

lemma step_correct {costs : List ID} {callback : List Node → Π (tgt : Reference), T tgt.2}
              {nodes : List Node} {m : Env} {tgt : Reference} :
  ∀ {n : Node}
    (H_callback_tgt : callback nodes tgt = computeGradSlow costs nodes m tgt)
    (H_callback_node : callback nodes n.ref = computeGradSlow costs nodes m n.ref),
    computeGradStep costs callback (n::nodes) m tgt = computeGradSlow costs (n::nodes) m tgt

| ⟨ref, parents, Operator.det op⟩, H_callback_tgt, H_callback_node => by
  simp only [computeGradStep, computeGradSlow]
  rw [H_callback_tgt, H_callback_node]

| ⟨ref, parents, Operator.rand op⟩, H_callback_tgt, H_callback_node => by
  simp only [computeGradStep, computeGradSlow]
  rw [H_callback_tgt]

open util_list
lemma strip_foldr_base {costs : List ID} {m : Env} :
      Π {tgts : List Reference} {tgt₀ : Reference} {idx : ℕ},
        at_idx tgts idx tgt₀ →
       Nodup tgts →
env.get tgt₀
         (foldr (λ (ref : Reference) (dict₀ : Env) =>
                    (env.insert ref
                                 (computeGradStep costs (λ (nodes' : List Node) (tgt' : Reference) => T.error "backprop-end") [] m ref)
                                 dict₀))
                 env.mk
                 tgts)
=
computeGradStep costs (λ (nodes : List Node) (ref : Reference) => env.get ref env.mk) [] m tgt₀
| [], _, _, H_at_idx, _ => False.rec _ (Nat.not_lt_zero _ H_at_idx.left)

| (tgt::tgts), tgt₀, 0, H_at_idx, H_nodup => by
    have H_eq : tgt = tgt₀ := at_idx_inj at_idx_0 H_at_idx
    rw [←H_eq]
    simp only [foldr]
    rw [env.get_insert_same]
    rfl

| (tgt::tgts), tgt₀, idx+1, H_at_idx, H_nodup => by

    cases H_nodup with
      | cons h_not_mem tail_nodup =>
        have H_at_idx_next : at_idx tgts idx tgt₀ := at_idx_of_cons H_at_idx
        have H_neq : tgt₀ ≠ tgt := by
           have mem_tgt₀ : tgt₀ ∈ tgts := mem_of_at_idx H_at_idx_next
           exact Ne.symm (h_not_mem tgt₀ mem_tgt₀)
        dsimp [foldr]
        rw [env.get_insert_diff _ _ H_neq]
        exact (strip_foldr_base H_at_idx_next tail_nodup)


lemma strip_foldr_step {costs : List ID} {nodes : List Node} {m : Env} {old_dict : Env} :
  Π {tgts : List Reference} {tgt₀ : Reference} {idx : Nat},
    at_idx tgts idx tgt₀ →
    Nodup tgts →
    env.get tgt₀
             (foldr (λ (tgt' : Reference) (dict' : Env)=>
                       (env.insert tgt'
                                    (computeGradStep costs (λ (nodes : List Node) (ref : Reference) => env.get ref old_dict)
                                                       nodes m tgt')
                                    dict'))
                    env.mk
                    tgts)
    =
    computeGradStep costs (λ (nodes : List Node) (tgt : Reference) => env.get tgt old_dict) nodes m tgt₀
| [], _, _, H_idx, _ => False.rec _ (Nat.not_lt_zero _ H_idx.left)

| (tgt::tgts), tgt₀, 0, H_at_idx, H_nodup => by
    have H_eq : tgt = tgt₀ := at_idx_inj at_idx_0 H_at_idx
    rw [←H_eq]
    simp only [foldr]
    rw [env.get_insert_same]

| (tgt::tgts), tgt₀, idx+1, H_at_idx, H_nodup => by
      cases H_nodup with
        -- | nil => trivial -- impossible
        | cons h_not_mem tail_nodup =>
            have H_at_idx_next : at_idx tgts idx tgt₀ := at_idx_of_cons H_at_idx
            have H_neq : tgt₀ ≠ tgt := by
              have mem_tgt₀ : tgt₀ ∈ tgts := mem_of_at_idx H_at_idx_next
              exact Ne.symm (h_not_mem tgt₀ mem_tgt₀)
            dsimp only [foldr]
            rw [env.get_insert_diff _ _ H_neq]
            exact (strip_foldr_step H_at_idx_next tail_nodup)


lemma memoize_correct (costs : List ID) :
  ∀ (nodes : List Node) (m : Env) {tgts : List Reference},
  ∀ {tgt₀ : Reference} {idx : Nat}, at_idx tgts idx tgt₀ →
  Nodup (tgts ++ map Node.ref nodes) →
  env.get tgt₀ (backpropCore costs nodes m tgts)
  =
  computeGradSlow costs nodes m tgt₀

| _, _ , [], _, _, H_at_idx, _ => False.rec _ (Nat.not_lt_zero _ H_at_idx.left)

| [] , m, tgt::tgts, tgt₀, idx, H_at_idx, H_nodup => by
  have H_nodup_tgts : Nodup (tgt::tgts) := by
    rw [List.nodup_append_comm] at H_nodup
    exact H_nodup
  unfold backpropCore backpropCoreHelper computeInitDict
  rw [strip_foldr_base H_at_idx H_nodup_tgts]
  dsimp [computeGradStep]
  unfold computeGradSlow
  rfl
  -- rw [sumr]
  -- simp only [sumr_sumr₁]
  -- rw [sumr]
  -- rfl

| (n::nodes), m, tgt::tgts, tgt₀, idx, H_at_idx, H_nodup => by
  have H_nodup_tgts : Nodup (tgt::tgts) := Nodup.of_append_left H_nodup
  have H_nodup_n : Nodup ((n.ref :: tgt :: tgts) ++ map Node.ref nodes) := nodup_append_swap H_nodup


  have H_at_idx_tgt₀ : at_idx (n.ref :: tgt :: tgts) (idx+1) tgt₀ := at_idx_cons H_at_idx
  have H_at_idx_n : at_idx (n.ref :: tgt :: tgts) 0 n.ref := at_idx_0
  unfold backpropCore backpropCoreHelper computeInitDict
  rw [strip_foldr_step H_at_idx H_nodup_tgts]
  simp only [computeGradStep, computeGradSlow]
  apply step_correct
  apply (memoize_correct _ _ _ H_at_idx_tgt₀ H_nodup_n)
  apply (memoize_correct _ _ _ H_at_idx_n H_nodup_n)

end theorems
end certigrad
