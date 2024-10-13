/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of gradients.
-/
-- import .tensor .tfacts .tactics
import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tactics

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

import Lean
open Lean Elab Tactic Meta

namespace certigrad
namespace T

open util_list

-- is_cdifferentiable

axiom is_cdifferentiable_binary {shape : S} (k : T shape → T shape → TReal) (θ : T shape) :
  is_cdifferentiable (λ θ₀ => k θ₀ θ) θ → is_cdifferentiable (λ θ₀ => k θ θ₀) θ →
  is_cdifferentiable (λ θ₀ => k θ₀ θ₀) θ

-- axiom is_cdifferentiable_multiple_args {fshape : S} (tgt : Reference) (parents : List Reference) (m : env) (f : Dvec T parents.p2 → T fshape)
--                                       (θ : T tgt.2) (k : T fshape → TReal) :
--   (∀ (idx : ℕ) (H_idx_in_riota: idx ∈ riota (length parents)) (H_tgt_eq_dnth_idx : tgt = dnth parents idx),
--      is_cdifferentiable (λ θ₀ => k (f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx))) θ) →
--   is_cdifferentiable (λ θ₀ => k (f (env.get_ks parents (env.insert tgt θ₀ m)))) θ

axiom is_cdifferentiable_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → TReal) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x => f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => f x θ₁) θ₀) θ →
  is_cdifferentiable (λ θ₀ => ∫ (λ x => f x θ₀)) θ

axiom is_cdifferentiable_const {ishape : S} (θ : T ishape) (x : TReal) : is_cdifferentiable (λ (θ₀ : T ishape) => x) θ
axiom is_cdifferentiable_id (θ : TReal) : is_cdifferentiable (λ (θ₀ : TReal) => θ₀) θ

axiom is_cdifferentiable_exp {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (exp θ) → is_cdifferentiable (λ θ => k (exp θ)) θ

axiom is_cdifferentiable_log {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  is_cdifferentiable k (log θ) → is_cdifferentiable (λ θ => k (log θ)) θ

axiom is_cdifferentiable_sqrt {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (sqrt θ) → is_cdifferentiable (λ θ => k (sqrt θ)) θ

axiom is_cdifferentiable_inv {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  is_cdifferentiable k θ⁻¹ → is_cdifferentiable (λ θ => k θ⁻¹) θ

axiom is_cdifferentiable_scale {shape : S} (k : T shape → TReal) (α : TReal) (x : T shape) :
  is_cdifferentiable k (α • x) → is_cdifferentiable (λ x => k (α • x)) x

axiom is_cdifferentiable_neg {shape : S} (k : T shape → TReal) (θ : T shape) :
  is_cdifferentiable k (- θ) → is_cdifferentiable (λ θ => k (- θ)) θ

axiom is_cdifferentiable_add₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₁ => k (x₁ + x₂)) x₁

axiom is_cdifferentiable_add₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ + x₂) → is_cdifferentiable (λ x₂ => k (x₁ + x₂)) x₂

axiom is_cdifferentiable_sub₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₁ => k (x₁ - x₂)) x₁

axiom is_cdifferentiable_sub₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ - x₂) → is_cdifferentiable (λ x₂ => k (x₁ - x₂)) x₂

axiom is_cdifferentiable_mul₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₁ => k (x₁ * x₂)) x₁

axiom is_cdifferentiable_mul₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  is_cdifferentiable k (x₁ * x₂) → is_cdifferentiable (λ x₂ => k (x₁ * x₂)) x₂

axiom is_cdifferentiable_div₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₁ => k (x₁ / x₂)) x₁

axiom is_cdifferentiable_div₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  is_cdifferentiable k (x₁ / x₂) → is_cdifferentiable (λ x₂ => k (x₁ / x₂)) x₂

axiom is_cdifferentiable_sum (k : TReal → TReal) (shape : S) (x : T shape) :
  is_cdifferentiable k (sum x) → is_cdifferentiable (λ x => k (sum x)) x

axiom is_cdifferentiable_prod (k : TReal → TReal) (shape : S) (x : T shape) :
  is_cdifferentiable k (prod x) → is_cdifferentiable (λ x => k (prod x)) x

axiom is_cdifferentiable_square {shape : S} (k : T shape → TReal) (x : T shape) :
  is_cdifferentiable k (square x) → is_cdifferentiable (λ x => k (square x)) x

axiom is_cdifferentiable_gemm₁ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ M => k (gemm M N)) M

axiom is_cdifferentiable_gemm₂ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
  is_cdifferentiable k (gemm M N) → is_cdifferentiable (λ N => k (gemm M N)) N

axiom is_cdifferentiable_add_fs {shape : S} (f₁ f₂ : T shape → TReal) (θ : T shape):
  (is_cdifferentiable f₁ θ ∧ is_cdifferentiable f₂ θ) ↔ is_cdifferentiable (λ θ₀ => f₁ θ₀ + f₂ θ₀) θ

axiom is_cdifferentiable_scale_f {shape : S} (α : TReal) (f : T shape → TReal) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x => α • f x) θ

axiom is_cdifferentiable_fscale {shape : S} (f : T shape → TReal) (y : TReal) (θ : T shape):
  is_cdifferentiable f θ ↔ is_cdifferentiable (λ x => f x • y) θ

-- Provable
axiom is_cdifferentiable_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → TReal) :
  Π (xs : List X),
    (∀ (x : X), x ∈ xs → is_cdifferentiable (λ θ₀ => f θ₀ x) θ) →
    is_cdifferentiable (λ (θ₀ : T shape) => sumr (List.map (f θ₀) xs)) θ

--

axiom grad_binary {shape : S} (k : T shape → T shape → TReal) (θ : T shape) :
  is_cdifferentiable (λ θ₀ => k θ₀ θ) θ → is_cdifferentiable (λ θ₀ => k θ θ₀) θ →
  ∇ (λ θ₀ => k θ₀ θ₀) θ = ∇ (λ θ₀ => k θ₀ θ) θ + ∇ (λ θ₀ => k θ θ₀) θ

axiom grad_tmulT {ishape oshape : S} : ∀ (f : T ishape → T oshape) (k : T oshape → TReal) (θ : T ishape),
  ∇ (λ θ₀ => k (f θ₀)) θ = tmulT (D (λ θ₀ => f θ₀) θ) (∇ k (f θ))

-- axiom grad_chain_rule : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (g : T shape₂ → TReal) (θ : T shape₁),
--   ∇ (λ (θ₀ : T shape₁) => g (f θ₀)) θ = tmulT (D f θ) (∇ g (f θ))

lemma grad_chain_rule : ∀ {shape₁ shape₂ : S} (f : T shape₁ → T shape₂) (g : T shape₂ → TReal) (θ : T shape₁),
  ∇ (λ (θ₀ : T shape₁) => g (f θ₀)) θ = tmulT (D f θ) (∇ g (f θ)) := by exact grad_tmulT


-- See Lang (Page 340, Theorem 3.4)
-- f continuously differentiable
-- f and grad_2 f both uniformly integrable
axiom grad_integral : ∀ {ishape tshape : S} (f : T ishape → T tshape → TReal) (θ : T tshape),
  (∀ x, is_cdifferentiable (f x) θ) →
  is_uniformly_integrable_around (λ θ₀ x => f x θ₀) θ →
  is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => f x θ₁) θ₀) θ →
  ∇ (λ θ₀ => ∫ (λ x => f x θ₀)) θ = ∫ (λ x => ∇ (λ θ₀ => f x θ₀) θ)

lemma grad_congr {shape : S} {f g : T shape → TReal} {x : T shape} (H : ∀ x, f x = g x) : ∇ f x = ∇ g x := by
  rw [funext H]

axiom grad_const : ∀ {ishape : S} (θ : T ishape) (x : TReal), ∇ (λ (θ₀ : T ishape) => x) θ = 0
axiom grad_id : ∀ (θ : TReal), ∇ (λ θ => θ) θ = (1 : TReal)

axiom TReal_one : ∀ (θ : TReal), θ • 1 = θ

-- Unary
axiom grad_exp {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (exp θ)) θ = ∇ k (exp θ) * exp θ

axiom grad_log {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  ∇ (λ θ => k (log θ)) θ = ∇ k (log θ) / θ

axiom grad_sqrt {shape : S} (k : T shape → TReal) (θ : T shape) : θ > 0 →
  ∇ (λ θ => k (sqrt θ)) θ = ∇ k (sqrt θ) / (2 * sqrt θ)

axiom grad_scale {shape : S} (k : T shape → TReal) (α : TReal) (x : T shape) :
  ∇ (λ x => k (α • x)) x = α • ∇ k (α • x)

axiom grad_neg {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (- θ)) θ = - (∇ k (- θ))

-- Binary
axiom grad_add₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ + x₂)) x₁ = ∇ k (x₁ + x₂)

axiom grad_add₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ + x₂)) x₂ = ∇ k (x₁ + x₂)

axiom grad_sub₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ - x₂)) x₁ = ∇ k (x₁ - x₂)

axiom grad_sub₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ - x₂)) x₂ = - ∇ k (x₁ - x₂)

axiom grad_mul₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₁ => k (x₁ * x₂)) x₁ = ∇ k (x₁ * x₂) * x₂

axiom grad_mul₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) :
  ∇ (λ x₂ => k (x₁ * x₂)) x₂ = ∇ k (x₁ * x₂) * x₁

-- Note: can be proved from grad_binary and grad_mul*, but resulting theorem
-- would have `is_cdifferentiable k` as a pre-condition.
-- It is safe to avoid that here because of the symmetry of the function.
axiom grad_square {shape : S} (k : T shape → TReal) (x : T shape) :
  ∇ (λ x => k (square x)) x = ∇ k (square x) * 2 * x

axiom grad_div₁ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₁ => k (x₁ / x₂)) x₁ = ∇ k (x₁ / x₂) / x₂

axiom grad_div₂ {shape : S} (k : T shape → TReal) (x₁ x₂ : T shape) : square x₂ > 0 →
  ∇ (λ x₂ => k (x₁ / x₂)) x₂ = - (∇ k (x₁ / x₂) * x₁) / (square x₂)

-- Tensors
axiom grad_sum (k : TReal → TReal) (shape : S) (x : T shape) :
  ∇ (λ x => k (sum x)) x = ∇ k (sum x) • 1

axiom grad_dot₁ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₁ => dot x₁ x₂) x₁ = x₂
axiom grad_dot₂ {shape : S} (x₁ x₂ : T shape) : ∇ (λ x₂ => dot x₁ x₂) x₂ = x₁

axiom grad_gemm₁ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ M => k (gemm M N)) M = gemm (∇ k (gemm M N)) (transpose N)

axiom grad_gemm₂ {m p : ℕ} (k : T [m, p] → TReal) (n : ℕ) (M : T [m, n]) (N : T [n, p]) :
∇ (λ N => k (gemm M N)) N = gemm (transpose M) (∇ k (gemm M N))

-- Congruences
axiom grad_congr_pos {shape : S} (f g : T shape → TReal) (θ : T shape) :
  θ > 0 → (∀ (θ₀ : T shape), θ₀ > 0 → f θ₀ = g θ₀) → ∇ f θ = ∇ g θ

-- Compound
lemma grad_softplus {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (softplus θ)) θ = ∇ k (softplus θ) / (1 + exp (- θ)) := by
  have H : (exp θ) / (exp θ + 1) = 1 / (1 + exp (- θ)) :=
    calc (exp θ) / (exp θ + 1)
      = ((exp θ) / (exp θ + 1)) * ((exp θ)⁻¹ / (exp θ)⁻¹) := by simp [T.div_self (inv_pos (@exp_pos _ θ))]
    _ = ((exp θ * (exp θ)⁻¹) / ((exp θ + 1) * (exp θ)⁻¹)) := by simp [T.div_mul_div]
    _ = (1 / ((exp θ + 1) * (exp θ)⁻¹)) := by simp only [T.mul_inv_cancel (@exp_pos _ θ)]
    _ = 1 / ((exp θ * (exp θ)⁻¹) + 1 * (exp θ)⁻¹) := by simp only [right_distrib]
    _ = 1 / (1 + exp (- θ)) := by { simp only [T.mul_inv_cancel (@exp_pos _ θ), one_mul]; rw [exp_inv]}

  calc ∇ (λ θ => k (softplus θ)) θ
      = ∇ (λ θ => k (log (exp θ + 1))) θ := rfl
    _ = ∇ (λ θ => k (log (θ + 1))) (exp θ) * exp θ := by rw [T.grad_exp (λ θ => k (log (θ + 1)))]
    _ = ∇ (λ θ => k (log θ)) (exp θ + 1) * exp θ := by rw [T.grad_add₁ (λ θ => k (log θ))]
    _ = ∇ k (log (exp θ + 1)) / (exp θ + 1) * exp θ := by rw [T.grad_log k (exp θ + 1) (plus_one_pos exp_pos)]
    _ = ∇ k (softplus θ) * (exp θ / (exp θ + 1)) := by { rw [← T.mul_div_mul]; rfl}
    _ = ∇ k (softplus θ) * (1 / (1 + exp (- θ))) := by rw [H]
    _ = ∇ k (softplus θ) / (1 + exp (- θ)) := by simp [T.one_div_inv, T.div_mul_inv]


lemma grad_sigmoid {shape : S} (k : T shape → TReal) (θ : T shape) :
  ∇ (λ θ => k (sigmoid θ)) θ = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) :=
  have H_pre : 1 + exp (- θ) > 0 := by apply one_plus_pos exp_pos
  have H : exp (- θ) / (1 + exp (- θ)) = 1 - sigmoid θ :=
    calc  exp (- θ) / (1 + exp (- θ))
        = ((1 + exp (- θ)) - 1) / (1 + exp (- θ)) := by simp [sub_add_eq_sub_sub]
      _ = ((1 + exp (- θ)) / (1 + exp (- θ))) - 1 / (1 + exp (- θ)) := by simp [T.div_sub_div_same]
      _ = 1 - sigmoid θ := by { rw [T.div_self (one_plus_pos exp_pos)]; rfl}

  calc  ∇ (λ θ => k (sigmoid θ)) θ
      = ∇ (λ θ => k (1 / (1 + exp (- θ)))) θ := rfl
    _ = - ∇ (λ θ => k (1 / (1 + exp θ))) (- θ) := by rw [T.grad_neg (λ θ => k (1 / (1 + exp θ)))]
    _ = - (∇ (λ θ => k (1 / (1 + θ))) (exp (- θ)) * exp (- θ)) := by rw [T.grad_exp (λ θ => k (1 / (1 + θ)))]
    _ = - (∇ (λ θ => k (1 / θ)) (1 + exp (- θ)) * exp (- θ)) := by rw [T.grad_add₂ (λ θ => k (1 / θ))]
    _ = -(-(∇ k (1 / (1 + exp (-θ))) * 1) / square (1 + exp (-θ)) * exp (-θ)) := by rw [(T.grad_div₂ k 1 (1 + exp (- θ)) (square_pos_of_pos $ one_plus_pos exp_pos))]
    _ =    (∇ k (1 / (1 + exp (-θ))))     / square (1 + exp (-θ)) * exp (-θ)  := by rw [T.neg_div]; rw [neg_mul]; rw [neg_neg]; simp
    _ =    (∇ k (sigmoid θ))              / square (1 + exp (-θ)) * exp (-θ)  := rfl
    _ =    (∇ k (sigmoid θ)) * (1 / (1 + exp (-θ))) * (exp (-θ) / (1 + exp (- θ))) := by
      simp [square, T.div_mul_inv, T.mul_inv_pos H_pre H_pre]
      ring
      -- rw [← mul_assoc]
      -- rw [← mul_assoc]
      -- have H2 : (1 + (-θ).exp)⁻¹ * (-θ).exp = (-θ).exp * (1 + (-θ).exp)⁻¹ := by rw [mul_comm]
      -- rw [← H2]
    _ = (∇ k (sigmoid θ)) * sigmoid θ * (exp (-θ) / (1 + exp (- θ))) := rfl
    _ = ∇ k (sigmoid θ) * sigmoid θ * (1 - sigmoid θ) := by rw [H]


-- Gradients wrt arbitrary functions
lemma grad_add_fs {ishape : S} (θ : T ishape) (f₁ f₂ : T ishape → TReal) :
  is_cdifferentiable f₁ θ → is_cdifferentiable f₂ θ →
  ∇ (λ θ₀ => f₁ θ₀ + f₂ θ₀) θ = ∇ (λ θ₀ => f₁ θ₀) θ + ∇ (λ θ₀ => f₂ θ₀) θ := by
  intro H_f₁ H_f₂
  have H₁ : is_cdifferentiable (λ θ₀ => f₁ θ₀ + f₂ θ) θ := by
     apply Iff.mp (is_cdifferentiable_add_fs _ _ _) ; constructor; exact H_f₁; apply is_cdifferentiable_const
  have H₂ : is_cdifferentiable (λ θ₀ => f₁ θ + f₂ θ₀) θ := by
     apply Iff.mp (is_cdifferentiable_add_fs _ _ _) ; constructor; apply is_cdifferentiable_const; exact H_f₂
  rw [grad_binary (λ θ₁ θ₂ => f₁ θ₁ + f₂ θ₂) _ H₁ H₂]
  rw [grad_chain_rule _ (λ θ₀ => θ₀ + f₂ θ) θ, grad_chain_rule _ (λ θ₀ => f₁ θ + θ₀) θ]
  rw [tmulT_scalar, D_scalar, tmulT_scalar, D_scalar]
  rw [grad_add₁ (λ θ => θ), grad_id, one_smul]
  rw [grad_add₂ (λ θ => θ), grad_id, one_smul]

-- #check @OfNat.ofNat

-- lemma trivial_mul_one  (α : TReal) (shape : S): (const α [] * (1: TReal)) = const α [] := by
--   simp
--   apply mul_one

lemma trivial_mul_one  (α : TReal) (shape : S): (const α shape * 1) = const α shape := by simp
-- lemma trivial_mul_one' (α : TReal) : (const α [] * 1) = const α [] := by apply trivial_mul_one


-- failure reason:
-- multiply arbitrary shapes with TReal (e.g., 1) is not propoerly defined yet
-- also(and thus), 1 is interpreted as arbitrary shape

lemma grad_scale_f {ishape : S} (θ : T ishape) (α : TReal) (f : T ishape → TReal) :
  ∇ (λ θ₀ => α • f θ₀) θ = α • ∇ (λ θ₀ => f θ₀) θ := by
  rw [grad_chain_rule f (λ θ => α • θ) θ]
  rw [grad_scale (λ θ => θ)]
  rw [grad_id]
  -- at this point, 1 is treated as TReal 1, instead Tensor One; this is problematic
  -- rw [smul.def]
  -- have H : (const α [] * 1) = const α [] := by simp; apply mul_one
  rw [TReal_one] -- we introduce a new axiom here
  rw [tmulT_scalar]
  rw [D_scalar]

  -- simp; apply mul_one
  -- unfold smul has_smul.smul scalar_mul

-- begin
-- rw grad_chain_rule f (λ θ => α • θ) θ,
-- rw grad_scale (λ θ => θ),
-- rw grad_id,
-- rw smul.def,
-- rw mul_one,
-- rw tmulT_scalar,
-- rw D_scalar,
-- dunfold smul has_smul.smul scalar_mul,
-- rw const_scalar
-- end

-- lemma H_grad_log_simple : {θ : T shape} → θ > 0 → ∇ log θ = θ := sorry -- θ⁻¹

lemma H_grad_log_simple :  {x : TReal} →  x > 0 → ∇ log x = x⁻¹ := by
  intro x h1
  have h2 :=  grad_log (k := (λ (y:TReal) => y))
  have h3 := h2 x
  rw [grad_id] at h3
  have h4 : ∇ (fun θ => θ.log) x = 1 / x := by apply h3; apply h1 -- two zeros are different, TReal, tensor zero
  have h5 : 1 / x = x⁻¹ := by apply T.one_div_inv
  rw [← h5]
  rw [← h4]

-- because grad expects the function maps a tensor to a real number
-- while log maps tensor to tensor, lean infers the output tensor must a real number
-- as a result, the input tensor should be a real number as well


lemma grad_log_f {shape : S} (θ : T shape) (f : T shape → TReal) : f θ > 0 → ∇ (λ θ₀ => log (f θ₀)) θ = (f θ)⁻¹ • ∇ f θ := by
  -- intro H_pos
  -- have H_grad_log_simple :  {x : TReal} →  x > 0 → ∇ log x = x⁻¹ := by
  --   -- intros a H_pos2
  --   rw [grad_log (k := (λ (y:TReal) => y)) _ H_pos]
  --   -- apply grad_log
  intro H_pos
  rw [grad_chain_rule, tmulT_scalar, D_scalar, H_grad_log_simple H_pos]


-- assume H_pos,
-- have H_grad_log_simple : Π {θ : TReal}, θ > 0 → ∇ log θ = θ⁻¹, from
-- begin
-- intros θ H_pos,
-- rw grad_log (λ θ => θ) _ H_pos,
-- rw grad_id,
-- apply T.one_div_inv
-- end,
-- by rw [grad_chain_rule, tmulT_scalar, D_scalar, H_grad_log_simple H_pos]

section simplify_grad

-- open util_list expr tactic

lemma id_rule {A : Type} (a : A) : id a = a := rfl

-- withMainContext resolves unknown free variable error
-- Now reduceK is indirectly wrapped in tid.withcontex
def reduceK (k : Expr) : TacticM Expr :=  do
  -- Create a SimpTheorems object
  let slss ← Meta.SimpTheorems.addConst {} `certigrad.T.id_rule

  -- Attempt to simplify `k` using the simplification theorems
  let simpResult ← Meta.simp k { simpTheorems := #[slss] }

  -- If simplification results in a different expression, return it; otherwise, return the original `k`
  if simpResult.1.expr != k then
    return simpResult.1.expr
  else
    return k

partial def has_x (x e : Expr) : Option Bool :=
  if e.eqv x then pure true
  else
    let f : Bool → Expr → Option Bool := (λ found (m : Expr) =>
      if found then pure true
      else has_x x m)
    e.foldlM f false

/-
  Illustration of input arguments:
  - x is `new_x
  - k is initially `fun x => x`
  - e is the body `... (new_x op y) ...`
-/

partial def computeOuterInnerFunctionsCore (x : Expr) : Expr → Expr → TacticM Expr :=
  λ k e =>
  -- withMainContext resolves the unknown free variables error in computeOuterInnerFunctionsCore
  --  withMainContext
   do
    -- logInfo m!"computeOuterInnerFunctionsCore, x:={x}, k:={k}, e:={e}"

    -- e.g.,  f = @T.prod
    let f := e.getAppFn
    -- e.g., {shape : S} → T shape → TReal
    -- let f_type ← inferType f
    -- e.g., [ishape, large_body_expr]
    let args := e.getAppArgs'
    let n := args.size
    -- interesting finding: syntax `match` is actually a function
    -- logInfo m!"f:={f}\nf_type:={f_type}\nargs:={args}\nn:={n}"

    if n <= 1 then
      -- return k
      throwError "Expression does not have enough arguments"

    let barg₁ := args.get! (n-2)
    let barg₂ := args.get! (n-1)
    -- logInfo m!"barg1:={barg₁}, barg2:={barg₂}"

    let barg₁_type ← inferType barg₁
    -- logInfo m!"barg₁_type:={barg₁_type}"
    let barg₂_type ← inferType barg₂

    -- logInfo m!"barg₁_type:={barg₁_type},  barg₂_type:={barg₂_type}"

    let h1 := (has_x x barg₁)
    let h2 := (has_x x barg₂)
    -- logInfo m! "h1:={h1}, h2:={h2}"

    if barg₁ == x || barg₂ == x then
      return k
    else if h1 = some true then
      computeOuterInnerFunctionsCore x (mkLambda `x BinderInfo.default barg₁_type (Expr.app k (mkAppN f $ args.set! (n-2) (mkBVar 0)))) barg₁
    else if h2 = some true then
      computeOuterInnerFunctionsCore x (mkLambda `x BinderInfo.default barg₂_type (Expr.app k (mkAppN f $ args.set! (n-1) (mkBVar 0)))) barg₂
    else
      -- return k
      throwError "Variable not found"

/-
grad is in the form of: `T.is_cdifferentiable f val`
where f is (fun x => ... (x op y) ...)

the goal is to find `k := (fun v => ... v ...)` such that f = `fun x => k (x op y)`
-/

partial def computeOuterInnerFunctions (grad : Expr) : TacticM Expr := do
  -- let f := grad.getAppFn'
  -- logInfo m!"args := {args}"
  -- let f : Expr := if h : f0.isApp then f0.appArg h else f0
  -- logInfo m!"f := {f}"

  -- now f is `fun x => ... (x op y) ...`
  let args := grad.getAppArgs'
  let f := args[1]!

  /-
    f := fun θ₀ => ((2 * T.pi shape * θ₀.square).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
    input_domain_type := T shape
    binding_body := ((2 * T.pi shape * T.square #0).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
  -/
  let input_domain_type := f.bindingDomain!
  let binding_body := f.bindingBody!
  -- logInfo m!"input_domain_type := {input_domain_type}, binding_body := {binding_body}"

  let x ← mkFreshExprMVar input_domain_type (userName:= `new_x)
  let body := binding_body.instantiate1 x
  let bodyType ← inferType body

  -- throwError "computeOuterInnerFunctions debug-1"

  /-
    x := ?new_x
    body := ((2 * T.pi shape * ?new_x.square).sqrt⁻¹ * (-(2⁻¹ * ((x - μ) / σ).square)).exp).prod
    bodyType := TReal
  -/
  -- logInfo m!"x:={x}, body:={body}, bodyType:={bodyType}"

  -- initialK is simply an identity function: λ x => x
  -- `bvar 0` is de Bruin index
  let initialK := mkLambda `x BinderInfo.default bodyType (mkBVar 0)
  -- logInfo m!"initialK:={initialK}"

  -- Note: `<|>` prevents logInfo message of computeOuterInnerFunctionsCore
  -- being printed if any error happens inside
  computeOuterInnerFunctionsCore x initialK body <|> return initialK

/-

checkIsCDifferentiable will make sure the given `grad` expression is indeed a `T.is_cdifferentiable`

grad is in the form of: `T.is_cdifferentiable (fun x => ... x ...) val`

Given: T.is_cdifferentiable (fun θ₀ => ((2 * T.pi ishape * σ.square).sqrt⁻¹ * (-(2⁻¹ * ((x - θ₀) / σ).square)).exp).prod) μ

Find: k is (fun v => ((2 * T.pi ishape * σ.square).sqrt⁻¹ * (-(2⁻¹ * (v / σ).square)).exp).prod)

original function is equivalent to: fun θ₀ => k (x - θ₀)

-/

def computeK (grad : Expr) : TacticM Expr := do
  let k ← computeOuterInnerFunctions grad
  -- logInfo m!"after outer-inner, k = {k}"

  -- Q: why do we need reduceK? this might be problematic,
  -- since after reducing the structure may not match the oringal function
  -- A: reduceK is really needed because the way we construct k
  -- has a lot of nested function applications
  let kSimp ← reduceK k

  -- Perform head eta-expansion
  -- Meta.headEtaExpand kSimp
  -- logInfo m!"after reduceK, k = {kSimp}"
  return kSimp

-- meta def check_grad (e : expr) : tactic expr :=
-- if is_napp_of e `certigrad.T.grad 3 then head_eta_expand e else tactic.fail "not ∇"

def checkGrad (e : Expr) : TacticM Expr :=do
  if e.isAppOfArity `certigrad.T.grad 3 then
    -- In Lean3 implementation, `head_eta_expand e` is returned
    -- but there seems no similar API (e.g., headEtaExpansion) in Lean4
    return e
  else
    throwError "Variable not found"

-- meta def try_add_simp (s : simp_lemmas) (p : pexpr) : tactic simp_lemmas :=
-- do oe ← try_core $ to_expr p,
--    match oe with
--    | none := return s
--    | (some e) := simp_lemmas.add s e
--    end

-- ChatGPT suggestion

def tryAddSimp (s : SimpTheorems) (p : Syntax) : TacticM SimpTheorems := do
  -- Try to convert the `Syntax` (which represents a `pexpr`) to an `Expr`
  let oe ← Lean.Elab.Tactic.tryTactic? (elabTerm p none)

  match oe with
  | none =>
    -- If the expression is invalid, return the original `SimpTheorems`
    return s
  | some e =>
    -- If valid, add the expression to the `SimpTheorems`
    return (← s.addConst e.constName!)


-- meta def build_simplify_grad_simp_lemmas (k : expr) : tactic simp_lemmas :=
-- do es ← monad.mapm to_expr
--                    [``(@certigrad.T.grad_const)
--                   , ``(@certigrad.T.grad_id)
--                   , ``(certigrad.T.grad_exp %%k)
--                   , ``(certigrad.T.grad_log %%k)
--                   , ``(certigrad.T.grad_scale %%k)
--                   , ``(certigrad.T.grad_neg %%k)
--                   , ``(certigrad.T.grad_add₁ %%k)
--                   , ``(certigrad.T.grad_add₂ %%k)
--                   , ``(certigrad.T.grad_sub₁ %%k)
--                   , ``(certigrad.T.grad_sub₂ %%k)
--                   , ``(certigrad.T.grad_mul₁ %%k)
--                   , ``(certigrad.T.grad_mul₂ %%k)
--                   , ``(certigrad.T.grad_div₁ %%k)
--                   , ``(certigrad.T.grad_div₂ %%k)
--                   , ``(@certigrad.T.grad_dot₁)
--                   , ``(@certigrad.T.grad_dot₂)
--                   , ``(certigrad.T.grad_square %%k)
--                   , ``(certigrad.T.grad_sqrt %%k)
--                   , ``(certigrad.T.grad_softplus %%k)
--                   , ``(certigrad.T.grad_sigmoid %%k)
-- ],
--    s ← simp_lemmas.append simp_lemmas.mk es,
--    -- These have shape requirements that may cause `to_expr` to fail
--    s ← try_add_simp s ``(certigrad.T.grad_gemm₁ %%k),
--    s ← try_add_simp s ``(certigrad.T.grad_gemm₂ %%k),
--    s ← try_add_simp s ``(certigrad.T.grad_sum %%k),
--    -- These haven't been defined yet
--    s ← try_add_simp s ```(certigrad.T.grad_mvn_kl₁ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_mvn_kl₂ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₁ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₂ %%k),

--    s ← try_add_simp s ``(@certigrad.T.grad_scale_f),
--    return s


def buildSimplifyGradSimpLemmas (k : Expr) : TacticM SimpTheorems := do
  -- List of expressions to elaborate
  -- let dbg1 : Syntax := `(certigrad.T.grad_sum )

  let exprs : List (TacticM (TSyntax `term)) :=
    [ ``(@certigrad.T.grad_const),
      ``(@certigrad.T.grad_id),
      ``(certigrad.T.grad_exp $$k),
      ``(certigrad.T.grad_log $$k),
      ``(certigrad.T.grad_scale $$k),
      ``(certigrad.T.grad_neg $$k),
      ``(certigrad.T.grad_add₁ $$k),
      ``(certigrad.T.grad_add₂ $$k),
      ``(certigrad.T.grad_sub₁ $$k),
      ``(certigrad.T.grad_sub₂ $$k),
      ``(certigrad.T.grad_mul₁ $$k),
      ``(certigrad.T.grad_mul₂ $$k),
      ``(certigrad.T.grad_div₁ $$k),
      ``(certigrad.T.grad_div₂ $$k),
      ``(@certigrad.T.grad_dot₁),
      ``(@certigrad.T.grad_dot₂),
      ``(certigrad.T.grad_square $$k),
      ``(certigrad.T.grad_sqrt $$k),
      ``(certigrad.T.grad_softplus $$k),
      ``(certigrad.T.grad_sigmoid $$k) ]

  let exprs2 ←  Monad.sequence exprs
  -- Convert the list of syntax to expressions
  let es ← exprs2.mapM fun p => elabTerm p none

  -- Create the initial SimpTheorems
  let mut s := {}

  -- Add each elaborated expression to SimpTheorems
  for e in es do
    s ← s.addConst e.constName!

  -- These have shape requirements that may cause `elabTerm` to fail, use `tryAddSimp`
  s ← tryAddSimp s (← ``(certigrad.T.grad_gemm₁ $$k))
  s ← tryAddSimp s (← ``(certigrad.T.grad_gemm₂ $$k))
  s ← tryAddSimp s (← ``(certigrad.T.grad_sum $$k))

--    -- These haven't been defined yet
--    s ← try_add_simp s ```(certigrad.T.grad_mvn_kl₁ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_mvn_kl₂ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₁ %%k),
--    s ← try_add_simp s ```(certigrad.T.grad_bernoulli_neglogpdf₂ %%k),

  s ← tryAddSimp s (← ``(@certigrad.T.grad_scale_f))

  -- Return the final set of simplification lemmas
  return s


-- old_conv definition in Lean 3
-- meta def old_conv (α : Type) : Type :=
-- name → expr → tactic (old_conv_result α)
-- According to the above, r refers to `name` and e refers to `expr`
-- the logic is to first check r is indeed `eq`

-- meta def simplify_grad_core_helper (tac : tactic unit) : conv unit :=
-- λ r e => do guard $ r = `eq,
--           grad ← check_grad e,
--           k ← compute_k grad,
--           s ← build_simplify_grad_simp_lemmas k,
--           conv.apply_lemmas_core reducible s tac r e

def simplifyGradCoreHelper (tac : MetaM Unit) : TacticM Unit := do
  let tag ← getMainTag
  guard $ tag = `eq
  let target ← getMainGoal
  let grad ← checkGrad (← target.getType)
  let k ← computeK grad
  let s ← buildSimplifyGradSimpLemmas k

  -- run the tac with newly added lemmas
  -- s must be used, otherwise this function is meaningless
  -- focus tac
  -- withMainContext tac
  Simp.withSimpContext { simpTheorems := #[s] } tac

-- def simplifyGradCoreHelper (tac : TacticM Unit) : TacticM Unit := do
--   -- Ensure we are working within an equation
--   let r ← getLhs
--   guard (← isDefEq r (mkConst ``Eq)) -- `Eq` is the Lean 4 equivalent to `eq`
--   -- Perform checks and simplifications
--   let grad ← checkGrad r
--   let k ← computeK grad
--   let s ← buildSimplifyGradSimpLemmas k
--   applyLemmasCore reducible s tac

-- another ChatGPT attempt
-- def simplifyGradCoreHelper (tac : TacticM Unit) : Conv Unit := do
--   let r ← getLhs
--   let e ← getRhs
--   guard (← isDefEq r (mkConst ``Eq))  -- Ensure we are working within an equation
--   let grad ← checkGrad e
--   let k ← computeK grad
--   let s ← buildSimplifyGradSimpLemmas k
--   applyLemmasCore reducible s tac

/-

  https://leanprover-community.github.io/archive/stream/113488-general/topic/simp.20inside.20expressions.20with.20coe_to_fun.20sometimes.20fails.html

  ext_simplify_core supports adding some hook in the built-in `simp` process

  seems not supported in Lean 4 anymore

  simplify_grad_core essentially injects the simplify_grad_core_helper into the simp process
-/

-- meta def simplify_grad_core (tac : tactic unit) : tactic unit :=
-- at_target (λ e => do (a, new_e, pf) ← ext_simplify_core () {zeta := ff, beta := ff, eta := ff, proj := ff} simp_lemmas.mk
--                                                       (λ u => failed)
--                                                       (λ a s r p e => failed)
--                                                       (λ a s r p e => do ⟨u, new_e, pr⟩ ← simplify_grad_core_helper tac r e,
--                                                                        return ((), new_e, pr, tt))
--                                                       `eq e,
--                 return (new_e, pf))


-- def simplifyGradCore (tac : TacticM Unit) : TacticM Unit := do
--   let target ← getMainGoal
--   let goalExpr ← target.getType
--   let (a, newExpr, pf) ← extSimplifyCore
--     (cfg := {zeta := false, beta := false, eta := false, proj := false})
--     {}  -- Empty simp lemmas
--     (pre := fun _ => return none)  -- No preprocessing
--     (post := fun _ => return none)  -- No postprocessing
--     (step := fun _ _ _ r e => do
--       let ⟨(), newE, pr⟩ ← simplifyGradCoreHelper tac
--       return (some ((), newE, pr)))
--     goalExpr

--   replaceMainGoalWith (← assertExprEq goalExpr newExpr pf)
--   pure ()


/-
  some guildines:
  - we cannot literally transform each old Lean 3 implementation to Lean 4, especially for helper functions
  - because the underlying logic of processing tactics changed a lot
  - we have to understand the high-level purpose
-/



-- meta def check_is_cdifferentiable (e : expr) : tactic expr :=
-- if is_napp_of e `certigrad.T.is_cdifferentiable 3 then head_eta_expand e else tactic.fail "not is_cdifferentiable"

def checkIsCDifferentiable (e : Expr) : TacticM Expr := do

  /- e can be mdata : Lean.MData → Lean.Expr → Lean.Expr-/
  -- logInfo m! "checkIsCDifferentiable e={e}"

  if e.isAppOfArity' ``T.is_cdifferentiable 3 then
    -- return (← headBeta e)
    return e
  else
  if e.isAppOfArity' ``T.is_cdifferentiable 2 then
    -- return (← headBeta e)
    throwError " is_cdifferentiable arity is 2"
  else
    throwError "not is_cdifferentiable fn:= {e.getAppFn} fn'={e.getAppFn'} numArgs:= {e.getAppNumArgs'} isConst={e.isConst} isLam={e.isLambda} isApp={e.isApp} isForAll={e.isForall} isLet={e.isLet} isLetFun={e.isLetFun} isProp={e.isProp} isMVar={e.isMVar} isFVar={e.isFVar} isBinding={e.isBinding} isSort={e.isSort} isLit={e.isLit} isMdata={e.isMData}"

-- def prove_differentiable_core_helper (grad : expr) : TacticM Unit := do
--   match x with

-- meta def prove_differentiable_core_helper (grad : expr) : tactic unit :=
-- do k ← compute_k grad,
--    first [applyc `certigrad.T.is_cdifferentiable_const
--         , applyc `certigrad.T.is_cdifferentiable_id
--           -- these haven't been defined yet
--         , to_expr ```(T.is_cdifferentiable_sigmoid %%k) >>= apply
--         , to_expr ```(T.is_cdifferentiable_softplus %%k) >>= apply
--         , to_expr ```(T.is_cdifferentiable_mvn_kl₁ %%k) >>= apply
--         , to_expr ```(T.is_cdifferentiable_mvn_kl₂ %%k) >>= apply
--         , to_expr ```(T.is_cdifferentiable_bernoulli_neglogpdf₁ %%k) >>= apply
--         , to_expr ```(T.is_cdifferentiable_bernoulli_neglogpdf₂ %%k) >>= apply

--         , to_expr ``(T.is_cdifferentiable_exp %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_log %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_sqrt %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_scale %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_neg %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_inv %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_add₁ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_add₂ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_sub₁ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_sub₂ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_mul₁ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_mul₂ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_div₁ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_div₂ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_square %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_sum %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_prod %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_gemm₁ %%k) >>= apply
--         , to_expr ``(T.is_cdifferentiable_gemm₂ %%k) >>= apply
-- ]

def myFirstApply (tid : MVarId) (exprs : List (MetaM Expr)) : TacticM (List MVarId) := do
  -- logInfo m!"myFirstApply is invoked, exprs.length={exprs.length}"
  match exprs with
  | [] => --pure []
    throwError "myFirstApply: None is successful:("
  | e :: es =>
    try
      -- logInfo m! "will extract e"
      let e' ← e
      -- logInfo m! "will try e:={e'}"
      let mvarIds ← tid.apply e'
      Term.synthesizeSyntheticMVarsNoPostponing
      -- logInfo m!"myFirstApply, mvardIds: {mvarIds}"
      return mvarIds

      -- let mvarIds ← (← getMainGoal).apply e'
      -- Term.synthesizeSyntheticMVarsNoPostponing
      -- replaceMainGoal mvarIds
    catch ex =>
      -- logInfo m!"ex:={ex.toMessageData}"
      myFirstApply tid es
  -- assume exprs consists of a list of App Exprs

-- def proveDifferentiableCoreHelper (grad : Expr) : TacticM (List MVarId) := do

def proveDifferentiableCore (tid : MVarId): TacticM (List MVarId) := do
  let tgt ←  instantiateMVars  (← tid.getType)
  let grad ← checkIsCDifferentiable tgt

  -- match stx with
  -- | `(tactic| apply $e) => evalApplyLikeTactic (·.apply) e
  -- let target ← getMainGoal
  -- let tmp ← target.apply grad
  -- val ← instantiateMVars (← elabTermForApply e)


  -- let val : Expr := Expr.const ``iNat.zero []
  -- let target ← getMainGoal
  -- logInfo m!"target := {target}"
  -- let mvarIds' ← target.apply val
  -- logInfo m!"mvarIds := {mvarIds'}"
  -- Term.synthesizeSyntheticMVarsNoPostponing
  -- replaceMainGoal mvarIds'

  -- dbg_trace f!"dbg_trace: before calling computeK, grad := {grad}"

  -- computeK is essential since we have to find the proper wrapping structure

  let k ← tid.withContext (computeK grad)
  -- let k := grad
  -- throwError "proveDiff failed 4"
  -- Lean.logInfo m!"logInfo: done with computeK, k:=\n{k}"

  -- we shall change the state of MetaM to put k in the hypothesis, which can be referred later on
  -- https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html#tweaking-the-context

  let candidate_exprs : List (MetaM Expr) := [
    (mkAppM ``certigrad.T.is_cdifferentiable_id #[]),
    (mkAppM ``certigrad.T.is_cdifferentiable_add₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_const #[]),
    (mkAppM ``certigrad.T.is_cdifferentiable_exp #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_log #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sqrt #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_scale #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_neg #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_inv #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_add₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_add₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sub₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sub₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_mul₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_mul₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_div₁ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_div₂ #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_square #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_sum #[k]),
    (mkAppM ``certigrad.T.is_cdifferentiable_prod #[k])
  ]
  -- logInfo m!"constructed all candidates"

  myFirstApply tid candidate_exprs

  -- logInfo m!"finished trying all candidates, with k:={k}"
  -- throwError "proveDiff failed 5"


-- meta def prove_differentiable_core : tactic unit := target >>= check_is_cdifferentiable >>= prove_differentiable_core_helper
-- meta def prove_differentiable : tactic unit := repeat (prove_differentiable_core <|> prove_preconditions_core)

-- def proveDifferentiableCore (tid : MVarId): TacticM (List MVarId) := do
--   logInfo m!"enter proveDifferentiableCore..."
--   -- let tgt ← getMainTarget
--   -- let expr ← checkIsCDifferentiable tgt
--   let tgt ←  instantiateMVars  (← tid.getType)
--   let expr ← checkIsCDifferentiable tgt
--   -- logInfo m!"tgt:={tgt}, expr:={expr}"
--   proveDifferentiableCoreHelper expr
--   -- return []


-- elab "proveDifferentiable_helper_tac" : tactic => withMainContext $ do
--     -- logInfo m!"enter proveDifferentiable_helper_tac..."
--     proveDifferentiableCore -- <|> provePreconditions


-- def proveDifferentiable_ : TacticM Unit := do
--   -- throwError "prove diff failed"
--   evalTactic $ ← `(tactic| repeat proveDifferentiable_helper_tac)
--   -- evalTactic $ ← `(tactic| proveDifferentiable_helper_tac)

-- syntax "proveDifferentiable" : tactic
-- elab_rules : tactic
-- | `(tactic| proveDifferentiable) =>
--   withMainContext $ do
--     -- logInfo m!"enter proveDifferentiable..."
--     proveDifferentiable_

elab "proveDifferentiable" : tactic => do
    setGoals (← Meta.repeat' proveDifferentiableCore (← getGoals))

    -- logInfo m!"proveDifferentiable is invoked"
    -- logInfo m!"number of goals {(← getGoals).length}"
    -- evalTactic $ ← `(tactic| repeat proveDifferentiable_helper_tac)

    -- let mvarIds ←  proveDifferentiableCore (← getMainGoal)
    -- logInfo m!"mvarIds: {mvarIds}"
    -- replaceMainGoal mvarIds

    -- let f := fun tid => do
      -- logInfo m! "one iteration of proveDifferentiable"
      -- let res ← (proveDifferentiableCore tid)
      -- logInfo m! "res length: {res.length}"
      -- return res

      -- `return []` is buggy, which incorrectly close the main goal
      -- return []
    -- setGoals (← Meta.repeat' f (← getGoals))

-- meta def simplify_grad : tactic unit := simplify_grad_core (repeat $ prove_preconditions_core <|> prove_differentiable_core)

end simplify_grad


-- Compounds with simplify_grad

-- lemma grad_mvn_kl₁ (k : TReal → TReal) (shape : S) (μ σ : T shape) : ∇ (λ μ => k (mvn_kl μ σ)) μ = ∇ k (mvn_kl μ σ) • μ := by

-- begin
-- dunfold T.mvn_kl,
-- simplify_grad,
-- simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero, T.const_one, T.const_bit0, T.const_bit1, T.const_inv],
-- rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
-- simp
-- end

-- lemma grad_mvn_kl₂ (k : TReal → TReal) (shape : S) (μ σ : T shape) (H_σ : σ > 0) (H_k : is_cdifferentiable k (mvn_kl μ σ)) :
--   ∇ (λ σ => k (mvn_kl μ σ)) σ = ∇ k (mvn_kl μ σ) • (σ - (1 / σ)) :=
-- have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
-- have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), k (-2⁻¹ * T.sum (1 + T.log (square θ₀) - square μ - square σ))) σ, by prove_differentiable,
-- have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), k (-2⁻¹ * T.sum (1 + T.log (square σ) - square μ - square θ₀))) σ, by prove_differentiable,

-- begin
-- dunfold T.mvn_kl,
-- rw (T.grad_binary (λ θ₁ θ₂, k ((- 2⁻¹) * T.sum (1 + T.log (square θ₁) - square μ - square θ₂))) _ H_diff₁ H_diff₂),
-- dsimp,
-- simplify_grad,
-- simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero,
--       T.const_one, T.const_bit0, T.const_bit1, T.const_inv,
--       left_distrib, right_distrib],
-- rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
-- erw T.neg_div,
-- simp [mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm],
-- apply congr_arg, apply congr_arg,
-- simp only [T.mul_div_mul, square],
-- rw [-mul_assoc, T.mul_div_mul, (@T.div_self_square _ σ H_σ)],
-- simp,
-- rw [-(mul_assoc (2 : T shape) 2⁻¹), T.mul_inv_cancel two_pos],
-- simp,
-- rw T.div_mul_inv,
-- simp
-- end

-- prove_differentiable is essential for proving the remaining lemmas

-- lemma grad_bernoulli_neglogpdf₁ (k : TReal → TReal) (shape : S) (p z : T shape)
--                                 (H_p₁ : 0 < p) (H_p₂ : 0 < 1 - p) (H_k : is_cdifferentiable k (bernoulli_neglogpdf p z)) :
--   ∇ (λ p => k (bernoulli_neglogpdf p z)) p = ∇ k (bernoulli_neglogpdf p z) • ((1 - z) / (eps shape + (1 - p)) - z / (eps shape + p)) := by
--   have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape) => k (-T.sum (z * T.log (eps shape + θ₀) + (1 - z) * T.log (eps shape + (1 - p))))) p := by
--     prove_differentiable
--   have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape) => k (-T.sum (z * T.log (eps shape + p) + (1 - z) * T.log (eps shape + (1 - θ₀))))) p := by
--     prove_differentiable,

-- begin
-- dunfold T.bernoulli_neglogpdf,
-- rw T.grad_binary (λ θ₁ θ₂ => k ( - T.sum (z * T.log (eps shape + θ₁) + (1 - z) * T.log (eps shape + (1 - θ₂))))) _ H_diff₁ H_diff₂,
-- dsimp,
-- simplify_grad,
-- simp [T.smul.def, const_neg, T.neg_div, T.div_mul_inv, left_distrib, right_distrib],
-- end

-- lemma grad_bernoulli_neglogpdf₂ (k : TReal → TReal) (shape : S) (p z : T shape)
--                                 (H_p₁ : 0 < p) (H_p₂ : 0 < 1 - p) (H_k : is_cdifferentiable k (bernoulli_neglogpdf p z)) :
--   ∇ (λ z => k (bernoulli_neglogpdf p z)) z = ∇ k (bernoulli_neglogpdf p z) • (log (eps shape + (1 - p)) - log (eps shape + p)) :=
-- have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), k (-T.sum (θ₀ * T.log (eps shape + p) + (1 - z) * T.log (eps shape + (1 - p))))) z, by prove_differentiable,
-- have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape) => k (-T.sum (z * T.log (eps shape + p) + (1 - θ₀) * T.log (eps shape + (1 - p))))) z, by prove_differentiable,

-- begin
-- dunfold T.bernoulli_neglogpdf,
-- rw T.grad_binary (λ θ₁ θ₂ => k (- T.sum (θ₁ * T.log (eps shape + p) + (1 - θ₂) * T.log (eps shape + (1 - p))))) _ H_diff₁ H_diff₂,
-- dsimp,
-- simplify_grad,
-- simp [T.smul.def, const_neg, left_distrib, right_distrib],
-- end

-- -- Compounds with prove_differentiable
-- lemma is_cdifferentiable_sigmoid {shape : S} (k : T shape → TReal) (θ : T shape) :
--   is_cdifferentiable k (sigmoid θ) → is_cdifferentiable (λ θ => k (sigmoid θ)) θ :=
-- begin intro H, dunfold sigmoid, prove_differentiable end

-- lemma is_cdifferentiable_softplus {shape : S} (k : T shape → TReal) (θ : T shape) :
--   is_cdifferentiable k (softplus θ) → is_cdifferentiable (λ θ => k (softplus θ)) θ :=
-- begin intro H, dunfold softplus, prove_differentiable end

-- lemma is_cdifferentiable_mvn_kl₁ (k : TReal → TReal) (shape : S) (μ σ : T shape) :
--   is_cdifferentiable k (mvn_kl μ σ) → is_cdifferentiable (λ μ => k (mvn_kl μ σ)) μ :=
-- begin intro H, dunfold mvn_kl, prove_differentiable end

-- lemma is_cdifferentiable_mvn_kl₂ (k : TReal → TReal) (shape : S) (μ σ : T shape) (H_σ : σ > 0) :
--   is_cdifferentiable k (mvn_kl μ σ) → is_cdifferentiable (λ σ => k (mvn_kl μ σ)) σ :=
-- begin
-- intro H, dunfold mvn_kl,
-- apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-2⁻¹ * T.sum (1 + T.log (square θ₁) + -square μ + -square θ₂))),
-- { dsimp, prove_differentiable },
-- { dsimp, prove_differentiable }
--  end

-- lemma is_cdifferentiable_bernoulli_neglogpdf₁ (k : TReal → TReal) (shape : S) (p z : T shape) (H_p₁ : p > 0) (H_p₂ : p < 1) :
--   is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ p => k (bernoulli_neglogpdf p z)) p :=
-- begin
-- intro H, dunfold bernoulli_neglogpdf,
-- apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-T.sum (z * T.log (eps shape + θ₁) + (1 + -z) * T.log (eps shape + (1 + -θ₂))))),
-- { dsimp, prove_differentiable },
-- { dsimp, prove_differentiable }
-- end

-- lemma is_cdifferentiable_bernoulli_neglogpdf₂ (k : TReal → TReal) (shape : S) (p z : T shape) :
--   is_cdifferentiable k (bernoulli_neglogpdf p z) → is_cdifferentiable (λ z => k (bernoulli_neglogpdf p z)) z :=
-- begin
-- intro H, dunfold bernoulli_neglogpdf,
-- apply is_cdifferentiable_binary (λ θ₁ θ₂ => k (-T.sum (θ₁ * T.log (eps shape + p) + (1 + -θ₂) * T.log (eps shape + (1 + -p))))),
-- { dsimp, prove_differentiable },
-- { dsimp, prove_differentiable }
-- end

-- Random

-- lemma mvn_grad_logpdf_μ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
--   ∇ (λ θ => mvn_logpdf θ σ x) μ = mvn_grad_logpdf_μ μ σ x :=
-- begin
-- dunfold mvn_logpdf,
-- note H := square_pos_of_pos H_σ,
-- simplify_grad,
-- simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div],
-- rw -mul_assoc, rw T.mul_inv_cancel two_pos,
-- simp, rw T.div_div_eq_div_mul,
-- reflexivity
-- end

-- lemma mvn_grad_logpdf_σ_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) :
--   ∇ (λ θ => mvn_logpdf μ θ x) σ = mvn_grad_logpdf_σ μ σ x :=
-- have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
-- have H_d₁ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / θ₀) + log (2 * pi shape) + log (square σ))) σ, by prove_differentiable,
-- have H_d₂ : is_cdifferentiable (λ θ₀ => -2⁻¹ * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square θ₀))) σ, by prove_differentiable,

-- have H₁ : (2 * (2⁻¹ / square σ)) = σ⁻¹ * σ⁻¹,
--   begin dunfold square, rw [T.mul_div_mul_alt, T.mul_inv_cancel two_pos, one_div_inv, T.mul_inv_pos H_σ H_σ] end,

-- have H₂ : 2 * ((x + -μ) * ((x + -μ) * 2⁻¹)) = (2 * 2⁻¹) * square (x - μ), by simp [square],

-- begin
-- dunfold mvn_logpdf,
-- rw grad_binary (λ θ₁ θ₂ => -2⁻¹ * sum (square ((x - μ) / θ₁) + log (2 * pi shape) + log (square θ₂))) _ H_d₁ H_d₂, dsimp,
-- simplify_grad,
-- simp [smul.def, const_bit0, const_one, const_neg, const_inv, T.neg_div, T.div_div_eq_div_mul],
-- rw H₁,
-- rw -mul_assoc, rw T.mul_inv_cancel H_σ,
-- simp [T.mul_div_mul_alt, T.div_div_eq_div_mul],
-- rw [H₂, T.mul_inv_cancel two_pos],
-- simp [mvn_grad_logpdf_σ]
-- end

-- With data structures
lemma grad_sumr {X : Type} {shape : S} (θ : T shape) (f : T shape → X → TReal) :
  Π (xs : List X),
    is_cdifferentiable (λ (θ₀ : T shape) => sumr (List.map (f θ₀) xs)) θ →
    ∇ (λ (θ₀ : T shape) =>  sumr (List.map (f θ₀) xs)) θ
    =
    sumr (List.map (λ x => ∇ (λ θ₀ => f θ₀ x) θ) xs)
  | [],      H_diff => by { unfold List.map sumr; rw [grad_const] }
  | (x::xs), H_diff => by
    unfold List.map sumr
    unfold List.map sumr at H_diff
    rw [grad_add_fs _ _ _ (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).left (Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right]
    rw [grad_sumr _  _ _ ((Iff.mpr (is_cdifferentiable_add_fs _ _ _) H_diff).right)]

-- Note: this could be proved from a `select`/`replicate` formulation,
-- but it is arguably a more natural way of axiomatizing the property anyway.

-- axiom multiple_args_general :
--   ∀ (parents : List Reference) (tgt : Reference) (m : env)
--     (f : Dvec T parents^.p2 → T tgt.2 → TReal) (θ : T tgt.2),
--     is_cdifferentiable (λ θ₀ => f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ →
--     is_cdifferentiable (λ θ₀ => sumr (map (λ (idx : ℕ) => f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ)
--                                        (filter (λ idx => tgt = dnth parents idx) (riota $ length parents)))) θ →
-- ∇ (λ (θ₀ : T tgt.2) => f (env.get_ks parents (env.insert tgt θ₀ m)) θ₀) θ
-- =
-- ∇ (λ θ₀ => f (env.get_ks parents (env.insert tgt θ m)) θ₀) θ +
-- sumr (map (λ (idx : ℕ) =>
--             ∇ (λ θ₀ => f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx) θ) θ)
--          (filter (λ idx => tgt = dnth parents idx) (riota $ length parents)))


end T
end certigrad
