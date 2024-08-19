/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Identifiers.
-/
import CertiGrad.Util
import CertiGrad.Label

namespace certigrad

inductive ID : Type
| str : Label → ID
| nat : Nat → ID
deriving DecidableEq

namespace ID

-- instance : decidable_eq ID := by tactic.mk_dec_eq_instance

/-
@[inline] def Bool.decEq (a b : Bool) : Decidable (Eq a b) :=
   match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl
-/
-- @[inline] def ID.decEq (a b : ID) :  Decidable (Eq a b) :=
--   match a, b with
--     | str x, str y =>
--     -- by cases ( h0 : x=y) with
--     -- | isTrue h => trivial
--     -- | isFalse h =>

--       -- if (h : x = y) then by apply isTrue
--       -- else by apply isFalse
--     | str _, nat _ => isFalse
--     | nat x, nat y => x = y
--     | nat _, str _ => isFalse

-- instance : DecidableEq ID := by tactic.mk_dec_eq_instance

instance : Inhabited ID where
  default := ID.str Label.default

private def add : ID → ID → ID
| (ID.nat n₁), (ID.nat n₂) => ID.nat (n₁ + n₂)
| _ ,          _           => default

-- def to_str : ID → String
-- | (str l) => toString l
-- | (nat n) => "#" ++ toString n

-- instance : has_to_string ID := ⟨to_str⟩

instance : ToString ID where
  toString : ID -> String
    | (str l) => toString l
    | (nat n) => "#" ++ toString n


-- def less_than : ID → ID → Prop
-- | (nat n)  (str s) => true
-- | (str s)  (nat n) => false
-- | (nat n₁) (nat n₂) => n₁ < n₂
-- | (str s₁) (str s₂) => s₁ < s₂

-- instance : has_lt ID := ⟨less_than⟩

instance : LT ID where
  lt : ID → ID → Prop
  | (nat n),  (str s) => True
  | (str s),  (nat n) => False
  | (nat n₁), (nat n₂) => n₁ < n₂
  | (str s₁), (str s₂) => s₁ < s₂

-- instance decidable_less_than : Π (x y : ID), decidable (x < y)
-- | (nat n)  (str s) => decidable.true
-- | (str s)  (nat n) => decidable.false
-- | (nat n₁) (nat n₂) => show decidable (n₁ < n₂), by apply_instance
-- | (str s₁) (str s₂) => by apply label.decidable_less_than

end ID

theorem id_str_ne_nat (x : Label) (n : Nat) : (ID.str x ≠ ID.nat n) = True := by
  apply pextt
  intro H
  injection H

theorem id_nat_ne_str (x : Label) (n : Nat) : (ID.nat n ≠ ID.str x) = True := by
  apply pextt
  intro H
  injection H

-- begin apply pextt, intro H, injection H end

set_option trace.split.failure true

theorem id_str_ne_str (x₁ x₂ : Label) : (ID.str x₁ ≠ ID.str x₂) = (x₁ ≠ x₂) := by
  apply propext
  constructor -- apply Iff.intro
  . intro H
    intro h1
    rw [h1] at H
    trivial
  . intro H
    intro h1
    injection h1
    trivial

-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- intros H_ne H_eq,
-- injection H_eq with H,
-- exact H_ne H
-- end

theorem id_nat_ne_nat (n₁ n₂ : Nat) : (ID.nat n₁ ≠ ID.nat n₂) = (n₁ ≠ n₂) := by
  apply propext
  apply Iff.intro
  . intro H
    intro h1
    rw [h1] at H
    trivial
  . intro H
    intro h1
    injection h1
    trivial

-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- intros H_ne H_eq,
-- injection H_eq with H,
-- exact H_ne H
-- end

end certigrad
