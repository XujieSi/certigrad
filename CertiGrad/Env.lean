/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Environments.
-/
-- import data.hash_map library_dev.data.list.sort .tensor .id .util .Reference

-- data.hash_map is from mathlib3
-- https://leanprover-community.github.io/mathlib_docs/data/hash_map.html#hash_map
-- hash_map (α : Type u) [decidable_eq α] (β : α → Type v)
import CertiGrad.Tensor
import CertiGrad.Id
import CertiGrad.Util
import CertiGrad.Reference

-- import Std.Hash
-- import Lean.Data.HashMap

-- import Std.Data.DHashMap
-- import Batteries.Data.HashMap

namespace certigrad



def preEnv : Type := Std.DHashMap Reference (λ (ref : Reference) => T ref.2)

-- def pre_env  : Type := Lean.HashMap (ref : Reference) (T ref.2)
-- def pre_env {ref : Reference} : Type := Lean.HashMap Reference (T ref.2)

attribute [reducible] preEnv

namespace pre_env

-- definition eqv (m₁ m₂ : pre_env) : Prop :=
-- ∀ (ref : Reference), m₁^.find ref = m₂^.find ref

def eqv (m₁ m₂ : preEnv) : Prop :=
-- ∀ (ref : Reference), m₁.get! ref = m₂.get! ref
∀ (ref : Reference), m₁.get? ref = m₂.get? ref


-- local infix ~ := eqv
local infix : 50 "~" => eqv

-- definition eqv.refl (m : pre_env) : m ~ m :=
-- assume ref, rfl

theorem eqv.refl (m : preEnv) : m ~ m := by
  intro ref
  rfl

-- definition eqv.symm (m₁ m₂ : pre_env) : m₁ ~ m₂ → m₂ ~ m₁ :=
-- assume H ref, eq.symm (H ref)

theorem eqv.symm (m₁ m₂ : preEnv) : m₁ ~ m₂ → m₂ ~ m₁ := by
  intro h ref
  apply Eq.symm (h ref)


-- definition eqv.trans (m₁ m₂ m₃ : pre_env) : m₁ ~ m₂ → m₂ ~ m₃ → m₁ ~ m₃ :=
-- assume H₁ H₂ ref, eq.trans (H₁ ref) (H₂ ref)

theorem eqv.trans (m₁ m₂ m₃ : preEnv) : m₁ ~ m₂ → m₂ ~ m₃ → m₁ ~ m₃ := by
  intros h1 h2 ref
  apply Eq.trans (h1 ref) (h2 ref)

-- instance pdmap.eqv_setoid : setoid pre_env :=
-- setoid.mk eqv (mk_equivalence eqv eqv.refl eqv.symm eqv.trans)

instance pdmap.eqv_setoid : Setoid preEnv where
  r := eqv
  iseqv := ⟨eqv.refl, @eqv.symm, @eqv.trans⟩

end pre_env

-- def env : Type := quot pre_env.eqv
-- https://leanprover.github.io/reference/lean_reference.pdf
-- in Lean3, `quot r` wraps a relation as a new type, defined as follows:
-- constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
-- constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r

-- `quot` implemented in `lean/library/init/core.lean`
-- https://github.com/leanprover-community/lean/blob/cce7990ea86a78bdb383e38ed7f9b5ba93c60ce0/library/init/core.lean

-- Lean 4, `Quot` implemented in `lean4/src/Init/Core.lean`
abbrev  Env := Quot pre_env.eqv

namespace env

-- instance isSetoid (α) : Setoid (Std.DHashMap Reference α) where
--   r := pre_env.eqv

-- def mk : env := quotient.mk (mk_hash_map Reference.hash)

-- def mk : Env := .mk (Lean.mkHashMap (α := Reference))

def mk : Env := Quotient.mk certigrad.pre_env.pdmap.eqv_setoid Std.DHashMap.empty --Batteries.mkHashMap --Std.DHashMap.empty

noncomputable
def get (ref : Reference) (q : Env) : T ref.2 :=
  Quotient.liftOn q
  (λ (m : preEnv) =>
    match m.get? ref with
    | none => default
    | some x => x
  )
  -- sorry
  (by
    intro m₁ m₂ H_eqv
    have H1 : m₁.get? ref = m₂.get? ref := by apply H_eqv
    simp [H1])


-- def get (ref : Reference) (q : env) : T ref.2 := quotient.lift_on q
-- (λ (m : preEnv),
--   match m^.find ref with
--   | none := default _
--   | some x := x
--   end)
-- begin intros m₁ m₂ H_eqv, simp [H_eqv ref] end

-- set_option trace.Meta.Tactic.simp.rewrite true

def insert (ref : Reference) (x : T ref.2) (q : Env) : Env :=
  Quotient.liftOn q
  (λ (m : preEnv) => Quotient.mk certigrad.pre_env.pdmap.eqv_setoid $ m.insert ref x)
  (by
    intro m₁ m₂ H_eqv
    simp
    apply Quotient.sound
    intro ref'
    cases (Decidable.em (ref = ref')) --with H_eq H_neq
    case a.inl H =>
      subst H
      -- set_option trace.Meta.Tactic.simp.rewrite true
      simp
    case a.inr H =>
      -- set_option trace.Meta.Tactic.simp.rewrite true
      rw [Std.DHashMap.get?_insert]
      simp [H]
      rw [Std.DHashMap.get?_insert]
      simp [H]

      apply H_eqv
  )

-- #print insert

-- def insert (ref : Reference) (x : T ref.2) (q : env) : env := quotient.lift_on q
-- (λ (m : pre_env), quotient.mk $ m^.insert ref x)
-- begin
-- intros m₁ m₂ H_eqv, dsimp, apply quotient.sound,
-- intros ref',
-- cases (decidable.em (ref = ref')) with H_eq H_neq,
-- simp [hash_map.find_insert, dif_ctx_simp_congr, H_eq, dif_pos],
-- simp [hash_map.find_insert, dif_ctx_simp_congr, H_neq, dif_neg, H_eqv ref'],
-- end

def hasKey (ref : Reference) (q : Env) : Prop :=
  Quotient.liftOn q (fun (m : preEnv) => (m.get? ref).isSome)
    (by
      intros m₁ m₂ H_eqv
      dsimp
      rw [H_eqv ref]
    )

noncomputable
def getKs : ∀ (refs : List Reference) (m : Env), Dvec T refs.p2
| [],          m => ⟦⟧
| (ref::refs), m => Dvec.dcons (get ref m) (getKs refs m)

def insertAll : ∀ (refs : List Reference) (vs : Dvec T refs.p2), Env
| [],      ⟦⟧        => certigrad.env.mk
| (k::ks), (v:::vs) => certigrad.env.insert k v (insertAll ks vs)



@[simp] lemma get_def (ref : Reference) (m : preEnv) :
  get ref (Quotient.mk pre_env.pdmap.eqv_setoid m) = match m.get? ref with | none => default | some x => x := rfl

@[simp] lemma insert_def {ref : Reference} {x : T ref.2} (m : preEnv) :
  insert ref x (Quotient.mk pre_env.pdmap.eqv_setoid m) = Quotient.mk pre_env.pdmap.eqv_setoid (m.insert ref x) :=
  by apply Quotient.sound; apply pre_env.eqv.refl

@[simp] lemma hasKey_def (ref : Reference) (m : preEnv) :
  hasKey ref (Quotient.mk pre_env.pdmap.eqv_setoid m) = (m.get? ref).isSome := rfl

lemma not_hasKey_empty (ref : Reference) : ¬ hasKey ref mk := by
  simp [mk, hasKey]

lemma hasKey_insert {ref₁ ref₂ : Reference} {x₂ : T ref₂.2} {m : Env} :
  hasKey ref₁ m → hasKey ref₁ (insert ref₂ x₂ m) :=
  Quotient.inductionOn m fun m' H_hasKey =>
    if h : ref₂ = ref₁ then
      by
        subst h
        simp [insert, hasKey, Std.DHashMap.get?_insert]
    else
      by
        simp [insert, hasKey, Std.DHashMap.get?_insert, h]
        exact H_hasKey

lemma hasKey_insert_same (ref : Reference) {x : T ref.2} (m : Env) : hasKey ref (insert ref x m) :=
  Quotient.inductionOn m fun m' =>
    by
      simp [insert, hasKey]

lemma hasKey_insert_diff {ref₁ ref₂ : Reference} {x₂ : T ref₂.2} {m : Env} :
  ref₁ ≠ ref₂ → hasKey ref₁ (insert ref₂ x₂ m) → hasKey ref₁ m :=
  Quotient.inductionOn m fun m' H_neq H_hk =>
    by
      simp [insert, hasKey] at H_hk
      rw [Std.DHashMap.get?_insert] at H_hk
      cases h : (ref₂ == ref₁) with
      | true =>
        exfalso
        apply H_neq
        apply BEq.symm at h
        simp at h
        exact h
      | false =>
        simp only [h] at H_hk
        exact H_hk

lemma get_insert_same (ref : Reference) (x : T ref.2) (m : Env) : get ref (insert ref x m) = x :=
  Quotient.inductionOn m fun m' =>
    by
      simp [insert, get]

lemma get_insert_diff {ref₁ ref₂ : Reference} (x₂ : T ref₂.2) (m : Env) :
  ref₁ ≠ ref₂ → get ref₁ (insert ref₂ x₂ m) = get ref₁ m :=
  Quotient.inductionOn m fun m' H_neq =>
    by
      simp [insert, get]
      simp at H_neq
      have H:  ¬ (ref₂ = ref₁) := fun h_eq => H_neq (Eq.symm h_eq)
      simp [Std.DHashMap.get?_insert, H]


lemma insert_get_same {ref : Reference} {m : Env} : hasKey ref m → insert ref (get ref m) m = m :=
  Quotient.inductionOn m fun m' H_hasKey =>
    by
      simp [insert, get]
      apply Quotient.sound
      intro ref'
      -- Note: Lean does not automatically use symmetry of equality in `simp` here,
      -- so we explicitly handle `ref = ref'` as `ref' = ref` when simplifying.
      by_cases h : ref = ref'
      ·
        subst h
        cases H_get: Std.DHashMap.get? m' ref with
        | none =>
          simp
          simp at H_hasKey
          -- have H: ∃ v:T ref.2, Std.DHashMap.get? m' ref = some v := by exact Option.isSome_iff_exists.mp H_hasKey
          rw [H_get] at H_hasKey
          contradiction
          -- intro H: Std.DHashMap.get? m' ref = none
          -- exfalso
          -- apply H_has_key
          -- exact H
        | some =>
          simp
      ·
        simp [Std.DHashMap.get?_insert, h]
        -- simp [h]

lemma insert_insert_flip {ref₁ ref₂ : Reference} (x₁ : T ref₁.2) (x₂ : T ref₂.2) (m : Env) :
  ref₁ ≠ ref₂ → insert ref₁ x₁ (insert ref₂ x₂ m) = insert ref₂ x₂ (insert ref₁ x₁ m) :=
  Quotient.inductionOn m fun m' H_neq =>
    by
      simp [insert]
      apply Quotient.sound

      -- The following should be remembered --
      -- have H:  ¬ (ref₂ = ref₁) := fun h_eq => H_neq (Eq.symm h_eq)
      intro ref
      -- have H₁:  ¬ (ref₂ = ref) := fun h_eq => H_neq (Eq.symm h_eq)
      cases Decidable.em (ref₁ = ref) with
      | inl H_eq₁ =>
          simp [H_eq₁, Std.DHashMap.get?_insert]
          cases Decidable.em (ref₂ = ref) with
          | inl H_eq₂ =>
            exfalso
            simp [H_eq₁, H_eq₂] at H_neq
          | inr H_neq₂=>
            simp [H_neq₂]
      | inr H_neq₁ =>
          simp [H_neq₁, Std.DHashMap.get?_insert]




lemma insert_insert_same (ref : Reference) (x₁ x₂ : T ref.2) (m : Env) :
  insert ref x₁ (insert ref x₂ m) = insert ref x₁ m :=
  Quotient.inductionOn m fun m' =>
    by
      -- simp [insert]
      clear m
      simp
      apply Quotient.sound
      intro ref'
      cases Decidable.em (ref = ref') with
      | inl H_eq =>
        subst H_eq
        simp
      | inr H_neq =>
        simp [Std.DHashMap.get?_insert, H_neq]


lemma get_ks_env_eq (m₁ m₂ : Env) :
  ∀ (refs : List Reference), (∀ (ref : Reference), ref ∈ refs → get ref m₁ = get ref m₂) → getKs refs m₁ = getKs refs m₂ := by
  intro refs h
  induction refs with
  | nil => rfl
  | cons ref refs ih =>
    simp [getKs]
    have h_head : get ref m₁ = get ref m₂ := by simp [h]
    have h_tail : ∀ (r : Reference), r ∈ refs → get r m₁ = get r m₂ := by
      intros r hr
      exact h r (List.mem_cons_of_mem _ hr)
    rw [h_head, ih h_tail]


  -- have H_get : get ref m₁ = get ref m₂ :=
  --   H ref (List.mem_cons_self _ _)

  -- have H_pre : ∀ (x : Reference), x ∈ refs → get x m₁ = get x m₂ := by
  --   intro x hx
  --   exact H x (List.mem_cons_of_mem _ hx)

  --   dsimp [get_ks]
  -- by rw [H_get, get_ks_env_eq _ H_pre]

lemma get_ks_insert_diff :
  ∀ {refs : List Reference} {ref : Reference} {x : T ref.2} {m : Env}, ref ∉ refs → getKs refs (insert ref x m) = getKs refs m := by
  intros refs ref x m hnotin
  induction refs with
  | nil => rfl
  | cons ref' refs' ih =>
    simp [getKs]
    have hneq : ref' ≠ ref := by
        -- simp []
      intro heq
      subst heq
      simp at hnotin
      -- contradiction
      -- exact hnotin (List.mem_cons_self _ _)
    have hnotin' : ref ∉ refs' := by
      intro hmem
      exact hnotin (List.mem_cons_of_mem _ hmem)
    rw [get_insert_diff x m hneq, ih hnotin']

-- open Dvec

lemma get_ks_insert_same {ref : Reference} {refs : List Reference} {x : T ref.2} {m : Env} :
  getKs (ref :: refs) (insert ref x m) = Dvec.dcons (get ref (insert ref x m)) (getKs refs (insert ref x m)) :=
  rfl

-- lemma insert_all_nil : insert_all [] Dvec.dnil = mk := by
--   simp [insert_all]

-- lemma insert_all_cons {ref : Reference} {x : T ref.2} {refs : List Reference} {vs : Dvec T refs.p2} :
--   insert_all (ref :: refs) (x ::: vs) = insert ref x (insert_all refs vs) := by
--   simp [insert_all]


lemma dvec_update_at_env {refs : List Reference} {idx : ℕ} (m : Env)(h: idx < refs.length) :
  refs[idx]? = some ref → dvec.update_at (get ref m) (getKs refs m) idx = getKs refs m := by
    sorry
--     sorry
  -- intro H_at_idx
  -- induction refs with
  -- | nil => rfl
  -- | cons ref' refs' ih =>
  --   cases idx with
  --   | zero =>
  --     simp [get_ks, dvec.update_at, Dvec.dcons]
  --     intro H₁
  --     -- have H₂: get ref m = get ref m := by rfl
  --     simp [H₁, H₂]
  --   | succ idx' =>
  --     have h' : idx' < refs'.length := by
  --       simp at h
  --       exact Nat.lt_of_succ_lt_succ h
  --     simp [get_ks, dvec.update_at]
      -- rw [ih h']
      -- simp [dvec.update_at, get_ks]
      -- simp [dif_ctx_simp_congr, dif_pos]


lemma dvec_get_get_ks {refs : List Reference} {idx : ℕ} {h: idx < refs.length}(m : Env):
      refs[idx]? = some ref  →
      dvec.get ref.2 _ (getKs refs m) idx = get ref m:= by sorry

--       intro H_at_idx
--       have H_elem_at_idx : List.elem_at_idx refs idx ref :=  exact list.elem_at_idx_of_at_idx H_at_idx
--       induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH
--       { dunfold get_ks, erw dvec.get.equations._eqn_2, simp [dif_ctx_simp_congr, dif_pos] }
--       { dunfold get_ks, erw dvec.get.equations._eqn_3, exact IH (list.at_idx_of_cons H_at_idx) }
