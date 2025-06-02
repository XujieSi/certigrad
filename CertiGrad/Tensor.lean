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

abbrev S := List Nat

axiom T (shape : S) : Type

abbrev TReal := T ([] : S)

namespace T

-- Constants that compute (excluding const, lt, le)

axiom const (α : TReal) (shape : S) : T shape
axiom eps (shape : S) : T shape

axiom zero {shape : S} : T shape
axiom one {shape : S} : T shape
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


--- CommonRing axioms ---

def bit0 {α : Type u} [s₁ : Add α] (a  : α)             : α := a + a
def bit1 {α : Type u} [s₁ : One α] [s₂ : Add α] (a : α) : α := (bit0 a) + 1

noncomputable instance (shape : S) : Neg (T shape) := ⟨T.neg⟩
noncomputable instance (shape : S) : Add (T shape) := ⟨T.add⟩
noncomputable instance (shape : S) : Mul (T shape) := ⟨T.mul⟩
instance (shape : S) : LT (T shape) := ⟨T.lt⟩
instance (shape : S) : LE (T shape) := ⟨T.le⟩

-- instance (shape : S) : Inv (T shape) := ⟨T.inv⟩
noncomputable instance (shape : S) : Div (T shape) := ⟨λ x y => x * y⁻¹⟩


namespace IL
-- Instance Lemmas
axiom add_comm {shape : S} : ∀ (x y : T shape), x + y = y + x
axiom add_assoc {shape : S} : ∀ (x y z : T shape), x + y + z = x + (y + z)
axiom zero_add {shape : S} : ∀ (x : T shape), zero + x = x
axiom add_zero {shape : S} : ∀ (x : T shape), x + zero = x
axiom add_left_neg {shape : S} : ∀ (x : T shape), -x + x = zero
axiom mul_comm {shape : S} : ∀ (x y : T shape), x * y = y * x
axiom mul_assoc  {shape : S} : ∀ (x y z : T shape), x * y * z = x * (y * z)
axiom one_mul {shape : S} : ∀ (x : T shape), one * x = x
axiom mul_one {shape : S} : ∀ (x : T shape), x * one = x
axiom left_distrib {shape : S} : ∀ (x y z : T shape), x * (y + z) = x * y + x * z
axiom right_distrib {shape : S} : ∀ (x y z : T shape), (x + y) * z = x * z + y * z

axiom add_lt_add_left {shape : S} : ∀ (x y : T shape), x < y → ∀ (z : T shape), z + x < z + y
axiom zero_ne_one {shape : S} : (zero : T shape) ≠ (one : T shape)
axiom mul_nonneg {shape : S} : ∀ (x y : T shape), zero ≤ x → zero ≤ y → zero ≤ x * y
axiom mul_pos {shape : S} : ∀ (x y : T shape), zero < x → zero < y → zero < x * y
axiom zero_mul {shape : S} : ∀ (x : T shape), zero * x = zero
axiom mul_zero {shape : S} : ∀ (x : T shape), x * zero = zero

noncomputable def nsmul {shape : S} (n : Nat) (m : T shape) : (T shape) :=
  match n with
  | 0 => zero
  | n + 1 => add (nsmul n m) m

-- axiom zsmul {shape : S}: Int → (T shape) → (T shape)
noncomputable def zsmul {shape : S} (i : Int) (m : T shape) : (T shape) :=
  match i with
  | Int.ofNat n => nsmul n m
  | Int.negSucc n => neg (nsmul (n + 1) m)


--- PartialOrder axioms ---

axiom le_refl {shape : S} : ∀ (x : T shape), x ≤ x

axiom le_trans {shape : S} : ∀ (x y z : T shape), x ≤ y → y ≤ z → x ≤ z

axiom le_antisymm {shape : S} : ∀ (x y : T shape), x ≤ y → y ≤ x → x = y

axiom lt_iff_le_not_le {shape : S} : ∀ (a b : T shape), a < b ↔ a ≤ b ∧ ¬b ≤ a


--- IsOrderedRing axioms ---

axiom add_le_add_left {shape : S} : ∀ (x y : T shape), x ≤ y → ∀ (z : T shape), z + x ≤ z + y

axiom zero_le_one {shape : S} : (zero : T shape) ≤ (one : T shape)

axiom mul_le_mul_of_nonneg_left {shape : S} (a b c : T shape) : a ≤ b → zero ≤ c → c * a ≤ c * b

axiom mul_le_mul_of_nonneg_right {shape : S} (a b c : T shape) : a ≤ b → zero ≤ c → a * c ≤ b * c

end IL


-- CommRing --
noncomputable instance (shape : S) : CommRing (T shape) where
  zero := T.zero
  one := T.one
  add := T.add
  neg := T.neg
  mul := T.mul
  add_comm := T.IL.add_comm
  add_assoc := T.IL.add_assoc
  zero_add := T.IL.zero_add
  add_zero := T.IL.add_zero
  neg_add_cancel := T.IL.add_left_neg
  mul_comm := T.IL.mul_comm
  mul_assoc := T.IL.mul_assoc
  one_mul := T.IL.one_mul
  mul_one := T.IL.mul_one
  left_distrib := T.IL.left_distrib
  right_distrib := T.IL.right_distrib
  nsmul := T.IL.nsmul
  zero_mul := T.IL.zero_mul
  mul_zero := T.IL.mul_zero
  zsmul := T.IL.zsmul

-- PartialOrder --

noncomputable instance (shape : S) : PartialOrder (T shape) where
  le_refl := T.IL.le_refl
  le_trans := T.IL.le_trans
  le_antisymm := T.IL.le_antisymm
  lt_iff_le_not_le := T.IL.lt_iff_le_not_le

-- IsOrderedRing --

noncomputable instance (shape : S) : IsOrderedRing (T shape) where
  add_le_add_left := T.IL.add_le_add_left
  zero_le_one := T.IL.zero_le_one
  mul_le_mul_of_nonneg_right := T.IL.mul_le_mul_of_nonneg_right
  mul_le_mul_of_nonneg_left := T.IL.mul_le_mul_of_nonneg_left



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

/-
  f : T ishape -> TReal
  given input x (of T ishape), output a real

  grad_f: T ishape -> T ishape
  given a specific input x, compute gradients at that point
-/
axiom grad :  {ishape : S} →  (T ishape → TReal) → (T ishape → T ishape)
/-
  What's the meaning of D then?
  f :  T ishape -> T oshape

  D_f: T ishape -> T (ishape ++ oshape) ??

  D_f is a generalization of grad_f, where f's output is a TReal (i.e., T []) in grad_f
  while f of D_f output is `T oshape`

  when `oshape` is `[]`, D_f will degenerate to grad_f
-/
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
-- noncomputable instance {shape : S} : Inhabited (T shape) := ⟨T.zero shape⟩
noncomputable instance {shape : S} : Inhabited (T shape) := ⟨T.zero⟩

-- @[inline] noncomputable instance {shape : S} : has_smul (TReal) (T shape) := ⟨scalar_mul⟩



/- Derived definitions -/

noncomputable def softplus {shape : S} (x : T shape) : T shape := log (exp x + 1)
noncomputable def sigmoid {shape : S} (x : T shape) : T shape := 1 / (1 + exp (- x))
noncomputable def dot {shape : S} (x y : T shape) : TReal := sum (x * y)

noncomputable def square {shape : S} (x : T shape) : T shape := x * x

-- there are two different ways of interpreating `2` here
-- one is to treat it as a TReal number
-- another is to view it as an algebra operation, i.e., a + a

-- def mvn_pdf {shape : S} (μ σ x : T shape) : TReal :=
--   prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))

noncomputable def mvn_pdf {shape : S} (μ σ x : T shape) : TReal :=
  prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))

  -- prod ((sqrt (( 2 • pi shape) * square σ))⁻¹ * exp ((- (2 : TReal)⁻¹) • (square $ (x - μ) / σ)))
-- prod ((sqrt (( (2 : TReal) • pi shape) * square σ))⁻¹ * exp ((- (2 : TReal)⁻¹) • (square $ (x - μ) / σ)))


-- def mvn_logpdf {shape : S} (μ σ x : T shape) : TReal :=
--   (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ))

-- mvn means multivariate normal distribution (aka multivariate Gaussian distribution)
noncomputable def mvn_logpdf {shape : S} (μ σ x : T shape) : TReal :=
  (-2⁻¹) * sum (square ((x - μ) / σ) + log ( 2 * pi shape) + log (square σ))

-- (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 • pi shape) + log (square σ))

-- (- 2⁻¹) * sum (square ((x - μ) / σ) + log ( (2:TReal) • pi shape) + log (square σ))

noncomputable  def mvn_grad_logpdf_μ {shape : S} (μ σ x : T shape) : T shape :=
  (x - μ) / (square σ)


noncomputable def   mvn_grad_logpdf_σ {shape : S} (μ σ x : T shape) : T shape :=
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

noncomputable
def force {shape₁ : S} (x : T shape₁) (shape₂ : S) : T shape₂ :=
  if H : shape₁ = shape₂ then Eq.recOn H x
  else T.error ("force-failed: " ++  shape₁.toString ++ " != " ++  shape₂.toString)

end T
end certigrad
