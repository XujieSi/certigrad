/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic computation graphs.
-/
-- import .det .rand .util .id .sprog .env .reference

import CertiGrad.Det
import CertiGrad.Rand
import CertiGrad.Util
import CertiGrad.Id
import CertiGrad.Sprog
import CertiGrad.Env
import CertiGrad.Reference

namespace certigrad

inductive Operator (ishapes : List S) (oshape : S) : Type
| det : det.op ishapes oshape → Operator ishapes oshape
| rand : rand.op ishapes oshape → Operator ishapes oshape

noncomputable
def Operator.to_dist (m : Env) : ∀ {parents : List Reference} {oshape : S}, Operator parents.p2 oshape → sprog [oshape]
| parents, _, (det op)   => sprog.ret ⟦op.f (env.get_ks parents m)⟧
| parents, _, (rand op) => sprog.prim op (env.get_ks parents m)


structure Node : Type where
  ref : Reference
  parents : List (ID × S)
  op : Operator parents.p2 ref.2

structure Graph : Type where
  nodes : List Node
  costs : List ID
  targets : List Reference
  inputs : List Reference


def uniq_ids : ∀ (nodes : List Node) (inputs : Env), Prop
| [], inputs => true
| (⟨ref, op, parents⟩ :: nodes), inputs =>
¬ env.has_key ref inputs ∧ ∀ (x : T ref.2), uniq_ids nodes (env.insert ref x inputs)



namespace graph

open sprog

noncomputable
def to_dist {fshapes : List S} (k : Env → Dvec T fshapes) : Env → List Node → sprog fshapes
| m, []            => ret (k m)
| m, (⟨ref, parents, op⟩::nodes) => bind (Operator.to_dist m op) fun (x : Dvec T [ref.2]) => to_dist k (env.insert ref x.head m) nodes


open List

lemma envs_match_helper {fshapes : List S} (k₁ k₂ : Env → Dvec T fshapes) : ∀ (inputs : Env) (nodes : List Node),
  ∀ (n : Node) (x : T n.ref.2),
    uniq_ids (n :: nodes) inputs →
    (∀ (m : Env), (∀ (ref : Reference), env.has_key ref inputs → env.get ref m = env.get ref inputs) → k₁ m = k₂ m) →
    ∀ (m : Env),
     (∀ (r : Reference), env.has_key r (env.insert n.ref x inputs) → env.get r m = env.get r (env.insert n.ref x inputs)) → k₁ m = k₂ m :=
fun inputs nodes n x H_uids H_k_eq m H_next_envs_agree =>
  let H_envs_agree : ∀ (ref' : Reference), env.has_key ref' inputs → env.get ref' m = env.get ref' inputs :=
  fun ref' H_inputs_contains_ref' =>
    let H_next_contains_name := env.has_key_insert H_inputs_contains_ref'
    let H_next_agree := H_next_envs_agree _ H_next_contains_name
    let H_ref'_neq_ref : ref' ≠ n.ref :=
    by
      --- Use recases to destruct the node structure---
      rcases n with ⟨ref, parents, op⟩
      -- |ref parents op =>
      dsimp [uniq_ids] at H_uids
      -- simp
      -- dsimp [uniq_ids] at H_uids
      -- dsimp
      intro H_eq
      subst H_eq
      exact H_uids.left H_inputs_contains_ref'
    by simp [env.get_insert_diff _ _ H_ref'_neq_ref] at H_next_agree; exact H_next_agree
  H_k_eq _ H_envs_agree

lemma to_dist_k_congr {fshapes : List S} (k₁ k₂ : Env → Dvec T fshapes) (inputs : Env) (nodes : List Node) :
  k₁ = k₂ → graph.to_dist k₁ inputs nodes = graph.to_dist k₂ inputs nodes := by
  intro H; rw [H]

lemma to_dist_congr {fshapes : List S} (k₁ k₂ : Env → Dvec T fshapes) :
  ∀ (inputs : Env) (nodes : List Node),
    uniq_ids nodes inputs →
    (∀ (m : Env), (∀ (ref : Reference), env.has_key ref inputs → env.get ref m = env.get ref inputs) → k₁ m = k₂ m) →
    graph.to_dist k₁ inputs nodes = graph.to_dist k₂ inputs nodes
| inputs, [], H_uids, H_k_eq =>
  have H_inputs_eq : ∀ (ref : Reference), env.has_key ref inputs → env.get ref inputs = env.get ref inputs :=
  fun _ _ => rfl
  -- unfold graph.to_dist; simp only [graph.to_dist]; -- not needed, just use definition
  by
    simp [to_dist, H_k_eq, H_inputs_eq]

    -- apply H_k_eq inputs H_inputs_eq
| inputs, (⟨ref, parents, op⟩::nodes), H_uids, H_k_eq =>
  have : ∀ (x : Dvec T [ref.2]), graph.to_dist k₁ (env.insert ref x.head inputs) nodes = graph.to_dist k₂ (env.insert ref x.head inputs) nodes :=
  -- In Lean 4, it is often necessary to specify implicit and explicit variables
  fun x => graph.to_dist_congr _ _ _ _ (H_uids.right _) (envs_match_helper k₁ k₂ _ _ _ _ H_uids H_k_eq)
  by
    simp [graph.to_dist]
    funext x
    exact this x
-- have to_dist k₁ inputs (⟨ref, parents, op⟩ :: nodes) = to_dist k₂ inputs (⟨ref, parents, op⟩ :: nodes) := by
--  have bind (Operator.to_dist inputs op) (fun (x : Dvec T [ref.2]) => to_dist k₁ (env.insert ref x.head inputs) nodes)
--      =
--      bind (Operator.to_dist inputs op) (fun (x : Dvec T [ref.2]) => to_dist k₂ (env.insert ref x.head inputs) nodes) := by
--         suffices ∀ (x : Dvec T [ref.2]), to_dist k₁ (env.insert ref x.head inputs) nodes = to_dist k₂ (env.insert ref x.head inputs) nodes from
--           congr_arg _ (funext this)
--         intro (x : Dvec T [ref.2])
--       have to_dist k₁ (env.insert ref x.head inputs) nodes = to_dist k₂ (env.insert ref x.head inputs) nodes := by
--         exact to_dist_congr _ _ (H_uids.right _) (envs_match_helper k₁ k₂ _ _ _ _ H_uids H_k_eq)
--     simp
lemma graph_to_dist_inputs_congr {fshapes : List S} (k : Env → Dvec T fshapes) (inputs₁ inputs₂ : Env) (nodes : List Node) :
  inputs₁ = inputs₂ → graph.to_dist k inputs₁ nodes = graph.to_dist k inputs₂ nodes := by
  intro H; rw [H]

end graph


end certigrad
