/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Labels.

Note: this file is just because strings are slow and cumbersome in current Lean.
-/

-- import .tactics

import Lean
open Lean Elab

namespace certigrad

inductive Label : Type
  | default
  | batch_start
  | W_encode | W_encode₁ | W_encode₂ | h_encode | W_encode_μ | W_encode_logσ₂
  | W_decode | W_decode₁ | W_decode₂ | h_decode | W_decode_p
  | μ | σ | σ₂ | log_σ₂ | z | encoding_loss | decoding_loss | ε | x | p | x_all
deriving DecidableEq

namespace label

-- instance : decidable_eq label := by tactic.mk_dec_eq_instance

-- instance : DecidableEq Label := by
--   intro a b
--   cases a <;> cases b <;> (first | apply isTrue <;> rfl | apply isFalse <;> intro h <;> contradiction)

  -- apply isTrue <;> rfl
  -- apply isFalse <;> intro h <;> contradiction



open Label

instance : ToString Label where
  toString : Label → String
    | Label.default => "<default>"
    | batch_start => "batch_start"
    | W_encode => "W_encode"
    | W_encode₁ => "W_encode_1"
    | W_encode₂ => "W_encode_2"
    | h_encode => "h_encode"
    | W_encode_μ => "W_encode_mu"
    | W_encode_logσ₂ => "W_encode_logs₂"
    | W_decode => "W_decode"
    | W_decode₁ => "W_decode_1"
    | W_decode₂ => "W_decode_2"
    | h_decode => "h_decode"
    | W_decode_p => "W_decode_p"
    | μ => "mu"
    | σ => "sigma"
    | σ₂ => "sigma_sq"
    | log_σ₂ => "log_s₂"
    | z => "z"
    | encoding_loss => "encoding_loss"
    | decoding_loss => "decoding_loss"
    | ε => "eps"
    | x => "x"
    | p => "p"
    | x_all => "x_all"


-- instance : has_to_string label => ⟨to_str⟩

def to_nat : Label → Nat
| Label.default => 0
| batch_start => 1
| W_encode => 2
| W_encode₁ => 3
| W_encode₂ => 4
| h_encode => 5
| W_encode_μ => 6
| W_encode_logσ₂ => 7
| W_decode => 8
| W_decode₁ => 9
| W_decode₂ => 10
| h_decode => 11
| W_decode_p => 12
| μ => 13
| σ => 14
| σ₂ => 15
| log_σ₂ => 16
| z => 17
| encoding_loss => 18
| decoding_loss => 19
| ε => 20
| x => 21
| p => 22
| x_all => 23


-- section proofs

-- open tactic

-- meta def prove_neq_case_core : tactic unit :=
-- do H ← intro `H,
--    dunfold_at [`certigrad.label.to_nat] H,
--    H ← get_local `H,
--    (lhs, rhs) ← infer_type H >>= match_eq,
--    nty ← mk_app `ne [lhs, rhs],
--    assert `H_not nty,
--    solve1 prove_nats_neq,
--    exfalso,
--    get_local `H_not >>= λ H_not, exact (expr.app H_not H)

-- lemma eq_of_to_nat_eq {x y : label} : x = y → to_nat x = to_nat y :=
-- begin
-- intro H,
-- subst H,
-- end

-- lemma to_nat_eq_of_eq {x y : label} : to_nat x = to_nat y → x = y :=
-- begin
-- cases x,
-- all_goals { cases y },
-- any_goals { intros, reflexivity },
-- all_goals { prove_neq_case_core }
-- end

-- lemma neq_of_to_nat {x y : label} : (x ≠ y) = (x^.to_nat ≠ y^.to_nat) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- exact H_ne (to_nat_eq_of_eq H_eq),
-- intros H_ne H_eq,
-- exact H_ne (eq_of_to_nat_eq H_eq)
-- end

-- end proofs

-- def less_than (x y : label) : Prop := x^.to_nat < y^.to_nat
-- instance : has_lt label := ⟨less_than⟩

instance : LT Label where
  lt : Label → Label → Prop
    | l1, l2 => (to_nat l1) < (to_nat l2)

-- instance decidable_less_than (x y : label) : decidable (x < y) := by apply nat.decidable_lt

end label
end certigrad
