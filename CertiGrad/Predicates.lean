/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Predicates.
-/
import CertiGrad.Util
import CertiGrad.Id
import CertiGrad.Reference
import CertiGrad.Graph
import CertiGrad.ComputeGrad
import CertiGrad.Dvec

open List util_list dvec

namespace certigrad


-- Note that False is Prop in Lean 4 while false is Bool. --
def isDownstream (cost : ID) : Reference → List Node → Bool
| _, [] => false
| tgt, (⟨ref, parents, _⟩ :: nodes) =>
  if ref.1 = cost then true else (tgt ∈ parents ∧  isDownstream cost ref nodes) ∨ (isDownstream cost tgt nodes)

-- We don't need the following instance in Lean 4 anymore.--
-- instance decidableIsDownstream (cost : ID) : Π (tgt : Reference) (nodes : List Node), Decidable (isDownstream cost tgt nodes)
-- | _, [] => Decidable.isFalse (fun h => nomatch h)
-- | tgt, (⟨ref, parents, _⟩ :: nodes) =>
--   show Decidable (if ref.1 = cost then True else (tgt ∈ parents ∧ isDownstream cost ref nodes) ∨ isDownstream cost tgt nodes) from
--     have H₁ : Decidable (isDownstream cost ref nodes) := by apply decidableIsDownstream;
--     have H₂ : Decidable (isDownstream cost tgt nodes) := by apply decidableIsDownstream;


-- instance decidable_is_downstream (cost : ID) : Π (tgt : reference) (nodes : list node), decidable (is_downstream cost tgt nodes)
-- | _   [] := decidable.false

-- | tgt (⟨ref, parents, _⟩ :: nodes) :=
--   show decidable (if ref.1 = cost then true else (tgt ∈ parents ∧ is_downstream cost ref nodes) ∨ is_downstream cost tgt nodes), from
--   have H₁ : decidable (is_downstream cost ref nodes), from begin apply decidable_is_downstream end,
--   have H₂ : decidable (is_downstream cost tgt nodes), from begin apply decidable_is_downstream end,
--   by tactic.apply_instance




def allParentsInEnv : Π (inputs : Env) (nodes : List Node), Prop
| _, [] => true

| inputs, (⟨ref, parents, _⟩ :: nodes) =>
  (∀ (parent : Reference), parent ∈ parents → env.hasKey parent inputs)
  ∧ (∀ (x : T ref.2), allParentsInEnv (env.insert ref x inputs) nodes)

def allCostsScalars (costs : List ID) : ∀ (nodes : List Node), Prop
| [] => true
| (⟨ref, _, _⟩ :: nodes) => (ref.1 ∈ costs → ref.2 = []) ∧ allCostsScalars costs nodes

-- We group the decidable properties
structure wellFormedAt (costs : List ID) (nodes : List Node) (inputs : Env) (tgt : Reference) : Prop :=
  (uids : uniqIds nodes inputs)
  (psInEnv : allParentsInEnv inputs nodes)
  (costsScalars : allCostsScalars costs nodes)
  (m_contains_tgt : env.hasKey tgt inputs)
  (tgt_cost_scalar : tgt.1 ∈ costs → tgt.2 = [])

def gradsExistAt : List Node → Env → Reference → Prop
| [], _, _ => true

| (⟨ref, parents, Operator.det op⟩ :: nodes), m, tgt =>
  let m' := env.insert ref (op.f (env.getKs parents m)) m
  gradsExistAt nodes m' tgt
  ∧ (tgt ∈ parents → op.pre (env.getKs parents m) ∧ gradsExistAt nodes m' ref)

| (⟨ref, parents, Operator.rand op⟩ :: nodes), m, tgt =>
  let m' := (λ (y : T ref.2) => env.insert ref y m)
  (tgt ∈ parents → op.pre (env.getKs parents m)) ∧ (∀ y, gradsExistAt nodes (m' y) tgt)

def pdfsExistAt : List Node → Env → Prop
| [], _ => true

| (⟨ref, parents, Operator.det op⟩ :: nodes), m => pdfsExistAt nodes (env.insert ref (op.f (env.getKs parents m)) m )

| (⟨ref, parents, Operator.rand op⟩ :: nodes), m =>
  let m' := (λ (y : T ref.2) => env.insert ref y m)
  (op.pre (env.getKs parents m)) ∧ (∀ y, pdfsExistAt nodes (m' y))

-- TODO(dhs): these conditions are really nitty-gritty
noncomputable def canDifferentiateUnderIntegrals (costs : List ID) : List Node → Env → Reference → Prop
| [], _, _ => true

| (⟨ref, parents, Operator.det op⟩ :: nodes), inputs, tgt =>
  let inputs' := env.insert ref (op.f (env.getKs parents inputs)) inputs
  canDifferentiateUnderIntegrals costs nodes inputs' tgt
  ∧ (tgt ∈ parents → canDifferentiateUnderIntegrals costs nodes (env.insert ref (op.f (env.getKs parents inputs)) inputs) ref)

| (⟨ref, parents, Operator.rand op⟩ :: nodes), inputs, tgt =>
  let θ : T tgt.2 := env.get tgt inputs
  let g : T ref.2 → T tgt.2 → TReal :=
  (λ (x : T ref.2) (θ₀ : T tgt.2) =>
      E (graph.toDist (λ (inputs : Env) => ⟦sumCosts inputs costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        Dvec.head)
  let next_inputs := (λ (y : T ref.2) => env.insert ref y inputs)
-- Note: these conditions are redundant, but it is convenient to collect all the variations we need in one place
 (T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => op.pdf (env.getKs parents (env.insert tgt θ₀ inputs)) x • g x θ₀) θ

    ∧ (T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => ∇ (λ (θ₁ : T (tgt.snd)) => op.pdf (env.getKs parents (env.insert tgt θ₁ inputs)) x • g x θ₁) θ₀) θ
       ∧ T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => ∇ (λ (θ₁ : T (tgt.snd)) => op.pdf (env.getKs parents (env.insert tgt θ inputs)) x • g x θ₁) θ₀) θ)
    ∧ (∀ (idx : ℕ), at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx) x • g x θ) θ)
   ∧ (∀ (idx : ℕ),  at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) =>
                                         ∇ (λ (θ₀ : T (tgt.snd)) => op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx) x • g x θ) θ₀) θ))
∧ (∀ y, canDifferentiateUnderIntegrals costs nodes (next_inputs y) tgt)

def allPdfsStd : Π (nodes : List Node), Prop
| [] => true
| (⟨ref, parents, Operator.det op⟩ :: nodes) => allPdfsStd nodes
| (⟨(ref, .(shape)), [], Operator.rand (rand.op.mvn_std shape)⟩ :: nodes) => allPdfsStd nodes
| (⟨(ref, .(shape)), [(parent₁, .(shape)), (parent₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩ :: nodes) => false

lemma allPdfsStdDet : Π (ref : Reference) (parents : List Reference) (op : det.op parents.p2 ref.2) (nodes : List Node),
  allPdfsStd (⟨ref, parents, Operator.det op⟩ :: nodes) = allPdfsStd nodes
| (i, s), [], op, nodes => rfl
| (i, s), [(i', s')], op, nodes => rfl
| (i, s), [(i', s'), (i'', s'')], op, nodes => rfl
| (i, s), ((i', s') :: (i'', s'') :: a :: iss), op, nodes => rfl

noncomputable def canDiffUnderIntegralsPdfsStd (costs : List ID) : Π (nodes : List Node) (m : Env) (tgt : Reference), Prop
| [], _, _ => true

| (⟨ref, parents, Operator.det op⟩ :: nodes), inputs, tgt =>
  let inputs' := env.insert ref (op.f (env.getKs parents inputs)) inputs
  canDiffUnderIntegralsPdfsStd costs nodes inputs' tgt
  ∧ (tgt ∈ parents → canDiffUnderIntegralsPdfsStd costs nodes (env.insert ref (op.f (env.getKs parents inputs)) inputs) ref)

  | (⟨ref, parents, Operator.rand op⟩ :: nodes), inputs, tgt =>
  let θ : T tgt.2 := env.get tgt inputs
  let g : T ref.2 → T tgt.2 → TReal :=
  (λ (x : T ref.2) (θ₀ : T tgt.2) =>
      E (graph.toDist (λ (inputs : Env) => ⟦sumCosts inputs costs⟧)
                       (env.insert ref x (env.insert tgt θ₀ inputs))
                       nodes)
        Dvec.head)
  let next_inputs := (λ (y : T ref.2) => env.insert ref y inputs)

 (T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => T.mvn_pdf 0 1 x • g x θ₀) θ
    ∧ T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => ∇ (λ (θ₁ : T (tgt.snd)) => T.mvn_pdf 0 1 x • g x θ₁) θ₀) θ)
∧ (∀ y, canDiffUnderIntegralsPdfsStd costs nodes (next_inputs y) tgt)

end certigrad
