/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Tensors and basic tensor operations.
-/
-- import .util .rng .Dvec .id
import CertiGrad.Util
import CertiGrad.Rng
import CertiGrad.Dvec
import CertiGrad.Id

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.Ring.Defs
-- run_cmd mk_simp_attr `cgsimp

namespace certigrad


-- @[reducible] def S : Type := list ℕ

abbrev S := List Nat

axiom T (shape : S) : Type


-- notation `ℝ` := T []
-- notation:max "ℝ"  => T []
abbrev TReal := T ([] : S)

namespace T

-- Constants that compute (excluding const, lt, le)

axiom const (α : TReal) (shape : S) : T shape
axiom eps (shape : S) : T shape

axiom zero (shape : S) : T shape
axiom one (shape : S) : T shape
axiom pi (shape : S) : T shape

axiom neg {shape : S} (x : T shape) : T shape
axiom inv {shape : S} (x : T shape) : T shape
axiom log {shape : S} (x : T shape) : T shape
axiom exp {shape : S} (x : T shape) : T shape
axiom sqrt {shape : S} (x : T shape) : T shape
axiom tanh {shape : S} (x : T shape) : T shape

axiom add {shape : S} (x y : T shape) : T shape
-- axiom sub {shape : S} (x y : T shape) : T shape
noncomputable def sub {shape : S} (x y : T shape) : T shape := add x (neg y)

axiom mul {shape : S} (x y : T shape) : T shape
axiom div {shape : S} (x y : T shape) : T shape

axiom lt {shape : S} (x y : T shape) : Prop
axiom le {shape : S} (x y : T shape) : Prop

axiom pow {shape : S} (x : T shape) (α : TReal) : T shape
axiom of_nat (n : Nat) : TReal
axiom round (α : TReal) : Nat

axiom fail (shape : S) : T shape
axiom silent_fail (shape : S) : T shape
axiom error {shape : S} (s : String) : T shape

noncomputable instance {shape : S} : Inv (T shape) where
  inv := T.inv


-- Algebraic instances
-- @[inline, priority 10000] instance (shape : S) : has_zero (T shape) := ⟨T.zero shape⟩
-- @[inline, priority 10000] instance (shape : S) : has_one (T shape) := ⟨T.one shape⟩
-- @[inline, priority 10000] instance (shape : S) : has_neg (T shape) := ⟨T.neg⟩
-- @[inline, priority 10000] instance (shape : S) : has_add (T shape) := ⟨T.add⟩
-- @[inline, priority 10000] instance (shape : S) : has_mul (T shape) := ⟨T.mul⟩
-- @[inline, priority 10000] instance (shape : S) : has_lt (T shape) := ⟨T.lt⟩
-- @[inline, priority 10000] instance (shape : S) : has_le (T shape) := ⟨T.le⟩
-- @[inline, priority 10000] instance (shape : S) : has_inv (T shape) := ⟨T.inv⟩
-- @[inline, priority 10000] instance (shape : S) : has_div (T shape) := ⟨λ x y, x * y⁻¹⟩

-- instance (shape : S) : Zero (T shape) := ⟨T.zero shape⟩
-- instance (shape : S) : One (T shape) := ⟨T.one shape⟩

noncomputable instance (shape : S) : OfNat (T shape) 0 := ⟨T.zero shape⟩
noncomputable instance (shape : S) : OfNat (T shape) 1 := ⟨T.one shape⟩
-- noncomputable instance  : OfNat (T []) n := ⟨T.of_nat n⟩
noncomputable instance : OfNat TReal n := ⟨T.of_nat n⟩

noncomputable instance (shape : S) : Neg (T shape) := ⟨T.neg⟩
noncomputable instance (shape : S) : Add (T shape) := ⟨T.add⟩
noncomputable instance (shape : S) : Mul (T shape) := ⟨T.mul⟩
instance (shape : S) : LT (T shape) := ⟨T.lt⟩
instance (shape : S) : LE (T shape) := ⟨T.le⟩

-- instance (shape : S) : Inv (T shape) := ⟨T.inv⟩
noncomputable instance (shape : S) : Div (T shape) := ⟨λ x y => x * y⁻¹⟩
-- noncomputable instance (shape : S) : Div (T shape) := ⟨T.div⟩

namespace IL
-- Instance Lemmas
axiom add_comm {shape : S} : ∀ (x y : T shape), x + y = y + x
axiom add_assoc {shape : S} : ∀ (x y z : T shape), x + y + z = x + (y + z)
axiom zero_add {shape : S} : ∀ (x : T shape), 0 + x = x
axiom add_zero {shape : S} : ∀ (x : T shape), x + 0 = x
axiom add_left_neg {shape : S} : ∀ (x : T shape), -x + x = 0
axiom mul_comm {shape : S} : ∀ (x y : T shape), x * y = y * x
axiom mul_assoc  {shape : S} : ∀ (x y z : T shape), x * y * z = x * (y * z)
axiom one_mul {shape : S} : ∀ (x : T shape), 1 * x = x
axiom mul_one {shape : S} : ∀ (x : T shape), x * 1 = x
axiom left_distrib {shape : S} : ∀ (x y z : T shape), x * (y + z) = x * y + x * z
axiom right_distrib {shape : S} : ∀ (x y z : T shape), (x + y) * z = x * z + y * z
axiom le_refl {shape : S} : ∀ (x : T shape), x ≤ x
axiom le_trans {shape : S} : ∀ (x y z : T shape), x ≤ y → y ≤ z → x ≤ z
axiom le_antisymm {shape : S} : ∀ (x y : T shape), x ≤ y → y ≤ x → x = y
-- axiom le_of_lt {shape : S} : ∀ (x y : T shape), x < y → x ≤ y
-- axiom lt_of_lt_of_le {shape : S} : ∀ (x y z : T shape), x < y → y ≤ z → x < z
-- axiom lt_of_le_of_lt {shape : S} : ∀ (x y z : T shape), x ≤ y → y < z → x < z
-- axiom lt_irrefl {shape : S} : ∀ (x : T shape), ¬x < x
axiom add_le_add_left {shape : S} : ∀ (x y : T shape), x ≤ y → ∀ (z : T shape), z + x ≤ z + y
axiom add_lt_add_left {shape : S} : ∀ (x y : T shape), x < y → ∀ (z : T shape), z + x < z + y
axiom zero_ne_one {shape : S} : (0 : T shape) ≠ (1 : T shape)
axiom mul_nonneg {shape : S} : ∀ (x y : T shape), 0 ≤ x → 0 ≤ y → 0 ≤ x * y
axiom mul_pos {shape : S} : ∀ (x y : T shape), 0 < x → 0 < y → 0 < x * y
-- axiom le_iff_lt_or_eq {shape : S} : ∀ (x y : T shape), x ≤ y ↔ x < y ∨ x = y

axiom lt_iff_le_not_le {shape : S} : ∀ (a b : T shape), a < b ↔ a ≤ b ∧ ¬b ≤ a

axiom zero_mul {shape : S} : ∀ (x : T shape), 0 * x = 0
axiom mul_zero {shape : S} : ∀ (x : T shape), x * 0 = 0
axiom zero_le_one {shape : S} : (0 : T shape) ≤ (1 : T shape)

noncomputable def nsmul {shape : S} (n : Nat) (m : T shape) : (T shape) :=
  match n with
  | 0 => 0
  | n + 1 => add (nsmul n m) m

-- axiom zsmul {shape : S}: Int → (T shape) → (T shape)
noncomputable def zsmul {shape : S} (i : Int) (m : T shape) : (T shape) :=
  match i with
  | Int.ofNat n => nsmul n m
  | Int.negSucc n => neg (nsmul (n + 1) m)
end IL

-- @[inline] instance (shape : S) : ordered_comm_ring (T shape) :=
-- {
--   -- defs
--   zero := T.zero shape, one := T.one shape, add := T.add, neg := T.neg, mul := T.mul,
--   -- noncomputable defs
--   le := T.le, lt := T.lt,
--   -- axioms
--   add_comm := T.IL.add_comm, add_assoc := T.IL.add_assoc, zero_add := T.IL.zero_add,
--   add_zero := T.IL.add_zero, add_left_neg := T.IL.add_left_neg,
--   mul_comm := T.IL.mul_comm, mul_assoc := T.IL.mul_assoc, one_mul := T.IL.one_mul, mul_one := T.IL.mul_one,
--   left_distrib := T.IL.left_distrib, right_distrib := T.IL.right_distrib,
--   le_refl := T.IL.le_refl, le_trans := T.IL.le_trans, le_antisymm := T.IL.le_antisymm,
--   le_of_lt := T.IL.le_of_lt, lt_of_lt_of_le := T.IL.lt_of_lt_of_le, lt_of_le_of_lt := T.IL.lt_of_le_of_lt,
--   lt_irrefl := T.IL.lt_irrefl, add_le_add_left := T.IL.add_le_add_left, add_lt_add_left := T.IL.add_lt_add_left,
--   zero_ne_one := T.IL.zero_ne_one, mul_nonneg := T.IL.mul_nonneg, mul_pos := T.IL.mul_pos
-- }

noncomputable instance (shape : S) : OrderedCommRing (T shape) where
  zero := T.zero shape
  one := T.one shape
  add := T.add
  neg := T.neg
  mul := T.mul
  le := T.le
  lt := T.lt
  add_comm := T.IL.add_comm
  add_assoc := T.IL.add_assoc
  zero_add := T.IL.zero_add
  add_zero := T.IL.add_zero
  add_left_neg := T.IL.add_left_neg
  mul_comm := T.IL.mul_comm
  mul_assoc := T.IL.mul_assoc
  one_mul := T.IL.one_mul
  mul_one := T.IL.mul_one
  left_distrib := T.IL.left_distrib
  right_distrib := T.IL.right_distrib
  le_refl := T.IL.le_refl
  le_trans := T.IL.le_trans
  le_antisymm := T.IL.le_antisymm
  -- le_of_lt := T.IL.le_of_lt
  -- lt_of_lt_of_le := T.IL.lt_of_lt_of_le
  -- lt_of_le_of_lt := T.IL.lt_of_le_of_lt
  -- lt_irrefl := T.IL.lt_irrefl
  add_le_add_left := T.IL.add_le_add_left
  -- add_lt_add_left := T.IL.add_lt_add_left
  -- zero_ne_one := T.IL.zero_ne_one
  mul_nonneg := T.IL.mul_nonneg
  -- mul_pos := T.IL.mul_pos
  zero_mul := T.IL.zero_mul
  mul_zero := T.IL.mul_zero
  zero_le_one := T.IL.zero_le_one
  nsmul := T.IL.nsmul
  zsmul := T.IL.zsmul
  lt_iff_le_not_le := T.IL.lt_iff_le_not_le

-- @[inline] instance (shape : S) : has_sub (T shape) := by apply_instance
-- attribute [inline] ordered_comm_ring.to_ordered_ring ordered_ring.to_ring ring.to_add_comm_group add_comm_group.to_add_group algebra.sub

noncomputable instance (shape : S) : Sub (T shape) := ⟨T.sub⟩


-- We never want to do algebra with this
noncomputable def scalar_mul {shape : S} (α : TReal) (x : T shape) : T shape := const α shape * x

-- SMul is from mathlib4 Mathlib.Algebra.Algebra.Defs
noncomputable instance {shape : S} : SMul (TReal) (T shape) where
  smul := scalar_mul


axiom transpose {m n : Nat} (M : T [m, n]) : T [n, m]

axiom sum : {shape : S} →  T shape → TReal
axiom prod : {shape : S} →  T shape → TReal

axiom get_row {m n : Nat} (M : T [m, n]) (ridx : Nat) : T [n]
axiom sum_cols {nrows ncols : Nat} (M : T [nrows, ncols]) : T [nrows]
axiom get_col {m n : Nat} (M : T [m, n]) (cidx : Nat) : T [m]

axiom get_col_range {m n : Nat} (ncols : Nat) (M : T [m, n]) (cidx : Nat) : T [m, ncols]
axiom replicate_col {m : Nat} (v : T [m]) (n : Nat) : T [m, n]

axiom gemv {m n : Nat} (M : T [m, n]) (x : T [n]) : T [m]
axiom gemm {m n p : Nat} (M : T [m, n]) (N : T [n, p]) : T [m, p]

axiom append_col {n p : Nat} (N : T [n, p]) (x : T [n]) : T [n, p+1]

axiom sample_mvn : {shape : S} → (μ σ : T shape) → (rng : RNG) → T shape × RNG
axiom sample_uniform : (shape : S) →  (low high : TReal) →  (rng : RNG) → T shape × RNG

axiom toString {shape : S} : T shape → String

/- Other constants -/

axiom is_integrable : {shape₁ shape₂ : S} → (T shape₁ → T shape₂) → Prop
axiom integral : {shape₁ shape₂ : S} → (T shape₁ → T shape₂) → T shape₂

axiom is_uniformly_integrable_around : {shape₁ shape₂ shape₃ : S} → (f : T shape₁ → T shape₂ → T shape₃) → (θ : T shape₁) →  Prop

-- ω(exp -x²) ∧ o(exp x²)
axiom is_btw_exp₂ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop
axiom is_sub_quadratic {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) : Prop
axiom is_bounded_btw_exp₂_around {shape₁ shape₂ shape₃ : S} (f : (x : T shape₁) →  (θ : T shape₂) →  T shape₃) (θ : T shape₂) : Prop

-- continuously differentiable
axiom is_cdifferentiable : {ishape : S} →  (T ishape → TReal) → T ishape → Prop
axiom grad :  {ishape : S} →  (T ishape → TReal) → (T ishape → T ishape)
axiom D {ishape oshape : S} : (T ishape → T oshape) → T ishape → T (ishape ++ oshape)
axiom tmulT {ishape oshape : S} : T (ishape ++ oshape) → T oshape → T ishape
axiom is_continuous {ishape oshape : S} : (T ishape → T oshape) → T ishape → Prop

noncomputable def dintegral {oshape : S} :  {ishapes : List S} →  (Dvec T ishapes → T oshape) → T oshape
| [],                f => f Dvec.dnil
| (ishape::ishapes), f => integral (λ (x : T ishape) => @dintegral _ ishapes (λ (v : Dvec T ishapes) => f (x ::: v)))

noncomputable def is_dintegrable {oshape : S} : {ishapes : List S} → (Dvec T ishapes → T oshape) → Prop
| [], f => True
| (ishape::ishapes), f => is_integrable (λ (x : T ishape) =>  @dintegral _ ishapes (λ (v : Dvec T ishapes) => f (x ::: v)))
                         ∧ ∀ (x : T ishape), is_dintegrable (λ (v : Dvec T ishapes) => f (x ::: v))

/- Notation -/

-- notation `π` := pi []
-- notation `∫` := integral
-- notation `∇` := grad

notation:max "π"  => pi ([] : S)
notation:max "∫"  => integral
notation:max "∇"  => grad

/- Other instances -/

-- instance {shape : S} : has_to_string (T shape) := has_to_string.mk T.to_string
noncomputable instance {shape : S} : ToString (T shape) where
  toString := T.toString

-- @[inline] instance {shape : S} : inhabited (T shape) := ⟨T.zero shape⟩ -- ⟨silent_fail _⟩ --⟨T.zero shape⟩ (switch back once no course-of-values)
noncomputable instance {shape : S} : Inhabited (T shape) := ⟨T.zero shape⟩

-- @[inline] noncomputable instance {shape : S} : has_smul (TReal) (T shape) := ⟨scalar_mul⟩



/- Derived definitions -/

noncomputable def softplus {shape : S} (x : T shape) : T shape := log (exp x + 1)
noncomputable def sigmoid {shape : S} (x : T shape) : T shape := 1 / (1 + exp (- x))
noncomputable def dot {shape : S} (x y : T shape) : TReal := sum (x * y)

noncomputable def square {shape : S} (x : T shape) : T shape := x * x

-- def mvn_pdf {shape : S} (μ σ x : T shape) : TReal :=
--   prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))

noncomputable def mvn_pdf {shape : S} (μ σ x : T shape) : TReal :=
  prod ((sqrt (( (2 : TReal) • pi shape) * square σ))⁻¹ * exp ((- (2 : TReal)⁻¹) • (square $ (x - μ) / σ)))


-- def mvn_logpdf {shape : S} (μ σ x : T shape) : TReal :=
--   (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ))

noncomputable def mvn_logpdf {shape : S} (μ σ x : T shape) : TReal :=
  (- 2⁻¹) * sum (square ((x - μ) / σ) + log ( (2:TReal) • pi shape) + log (square σ))

noncomputable  def mvn_grad_logpdf_μ {shape : S} (μ σ x : T shape) : T shape :=
  (x - μ) / (square σ)

noncomputable def mvn_grad_logpdf_σ {shape : S} (μ σ x : T shape) : T shape :=
  square (x - μ) / (σ * square σ) - σ⁻¹

noncomputable def mvn_std_logpdf {shape : S} (x : T shape) : TReal := mvn_logpdf 0 1 x

noncomputable def mvn_kl {shape : S} (μ σ : T shape) : TReal :=
  (- 2⁻¹) * sum (1 + log (square σ) - square μ - square σ)

noncomputable def mvn_empirical_kl {shape : S} (μ σ z : T shape) : TReal :=
  mvn_logpdf μ σ z - mvn_std_logpdf z

noncomputable def bernoulli_neglogpdf {shape : S} (p z : T shape) : TReal :=
  - sum (z * log (eps shape + p) + (1 - z) * log (eps shape + (1 - p)))

-- def force {shape₁ : S} (x : T shape₁) (shape₂ : S) : T shape₂ :=
--   if H : shape₁ = shape₂ then eq.rec_on H x else T.error ("force-failed: " ++ _root_.to_string shape₁ ++ " != " ++ _root_.to_string shape₂)

end T
end certigrad
