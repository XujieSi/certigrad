/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of the multivariate Gaussian distribution.
-/
-- import .tfacts .tgrads

import CertiGrad.Tfacts
import CertiGrad.Tgrads

namespace certigrad
namespace T

axiom is_integrable_mvn_of_sub_exp {shape₁ shape₂ : S} (μ σ : T shape₁) (f : T shape₁ → T shape₂) :
  is_btw_exp₂ f → is_integrable (λ x => mvn_pdf μ σ x • f x)

axiom is_uintegrable_mvn_of_bounded_exp₂_around {shape₁ shape₂ shape₃ : S} (pdf : T shape₁ → TReal) (f : T shape₁ → T shape₂ → T shape₃) (θ : T shape₂) :
  is_bounded_btw_exp₂_around f θ → is_uniformly_integrable_around (λ θ₀ x => pdf x • f x θ₀) θ

end T

-- section tactic
-- open tactic

-- meta def prove_is_mvn_integrable_core : tactic unit :=
-- first [
--        applyc `certigrad.T.is_btw_id
--      , applyc `certigrad.T.is_btw_const
--      , applyc `certigrad.T.is_btw_sigmoid
--      , applyc `certigrad.T.is_btw_softplus
--      , applyc `certigrad.T.is_btw_sum
--      , applyc `certigrad.T.is_btw_log_sigmoid
--      , applyc `certigrad.T.is_btw_log_1msigmoid
--      , applyc `certigrad.T.is_btw_gemm
--      , applyc `certigrad.T.is_btw_transpose
--      , applyc `certigrad.T.is_btw_neg
--      , applyc `certigrad.T.is_btw_inv
--      , applyc `certigrad.T.is_btw_add
--      , applyc `certigrad.T.is_btw_mul
--      , applyc `certigrad.T.is_btw_sub
--      , applyc `certigrad.T.is_btw_div
--      , applyc `certigrad.T.is_btw_exp

--      , applyc `certigrad.T.is_sub_quadratic_id
--      , applyc `certigrad.T.is_sub_quadratic_const
--      , applyc `certigrad.T.is_sub_quadratic_gemm
--      , applyc `certigrad.T.is_sub_quadratic_transpose
--      , applyc `certigrad.T.is_sub_quadratic_neg
--      , applyc `certigrad.T.is_sub_quadratic_add
--      , applyc `certigrad.T.is_sub_quadratic_softplus
--      , applyc `certigrad.T.is_sub_quadratic_mul₁
--      , applyc `certigrad.T.is_sub_quadratic_mul₂
--      , applyc `certigrad.T.is_sub_quadratic_sub
--      , prove_preconditions_core
-- ]

-- meta def prove_is_mvn_integrable : tactic unit :=
-- do applyc `certigrad.T.is_integrable_mvn_of_sub_exp,
--    repeat prove_is_mvn_integrable_core

-- meta def prove_is_mvn_uintegrable_core_helper : tactic unit :=
-- first [applyc `certigrad.T.is_bbtw_of_btw
--      , applyc `certigrad.T.is_bbtw_id
--      , applyc `certigrad.T.is_bbtw_bernoulli_neglogpdf
--      , applyc `certigrad.T.is_bbtw_softplus
--      , applyc `certigrad.T.is_bbtw_sum
--      , applyc `certigrad.T.is_bbtw_log_sigmoid
--      , applyc `certigrad.T.is_bbtw_log_1msigmoid
--      , applyc `certigrad.T.is_bbtw_gemm
--      , applyc `certigrad.T.is_bbtw_neg
--      , applyc `certigrad.T.is_bbtw_inv
--      , applyc `certigrad.T.is_bbtw_mul
--      , applyc `certigrad.T.is_bbtw_sub
--      , applyc `certigrad.T.is_bbtw_add
--      , applyc `certigrad.T.is_bbtw_exp
-- ] <|> (intro1 >> skip)

-- meta def prove_is_mvn_uintegrable_core : tactic unit :=
-- do try T.simplify_grad,
--    applyc `certigrad.T.is_uintegrable_mvn_of_bounded_exp₂_around,
--    repeat (prove_is_mvn_uintegrable_core_helper <|> prove_is_mvn_integrable_core)

-- meta def prove_is_mvn_uintegrable : tactic unit :=
-- -- TODO(dhs): why do I need the `try`?
-- (split >> focus [prove_is_mvn_uintegrable, prove_is_mvn_uintegrable]) <|> try prove_is_mvn_uintegrable_core

-- end tactic

namespace T
axiom mvn_const_int {shape oshape : S} (μ σ : T shape) : σ > 0 → ∀ (y : T oshape), is_integrable (λ (x : T shape) => mvn_pdf μ σ x • y)
axiom mvn_moment₁_int {shape : S} (μ σ : T shape) : σ > 0 → is_integrable (λ (x : T shape) => mvn_pdf μ σ x • x)
axiom mvn_moment₂_int {shape : S} (μ σ : T shape) : σ > 0 → is_integrable (λ (x : T shape) => mvn_pdf μ σ x • square x)
axiom mvn_cmoment₂_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • square (x - μ))

axiom mvn_logpdf_int {shape : S} (μ μ' σ σ' : T shape) (H_σ : σ > 0) (H_σ' : σ' > 0) : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_logpdf μ' σ' x)

-- TODO(dhs): prove in terms of primitives (possibly for concrete p)
axiom mvn_bernoulli_neglogpdf_int {shape₁ shape₂ : S} (μ σ : T shape₁) (H_σ : σ > 0) (p : T shape₁ → T shape₂)
                                      (H_p_cont : ∀ x, is_continuous p x) (H_p : ∀ x, p x > 0 ∧ p x < 1) (z : T shape₂) :
  is_integrable (λ (x : T shape₁) => T.mvn_pdf μ σ x • bernoulli_neglogpdf (p x) z)

axiom mvn_mvn_empirical_kl_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_empirical_kl μ' σ' x)

axiom mvn_mvn_kl_int {shape : S} (μ σ : T shape) (H_σ : σ > 0) (μ' σ' : T shape) :
  is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_kl μ' σ')

-- mvn is a distribution (provable from first principles)
axiom mvn_pdf_pos {shape : S} (μ σ : T shape) : σ > 0 → ∀ (x : T shape), mvn_pdf μ σ x > 0
axiom mvn_pdf_int1 {shape : S} (μ σ : T shape) : σ > 0 → ∫ (λ (x : T shape) => mvn_pdf μ σ x) = 1

lemma mvn_expected {shape oshape : S} (μ σ : T shape) : σ > 0 → ∀ (y : T oshape), ∫ (λ (x : T shape) => mvn_pdf μ σ x • y) = y := by
{ intros H_σ y; rw [integral_fscale, (mvn_pdf_int1 _ _ H_σ), one_smul] }

-- moments (provable from first principles)
axiom mvn_moment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • x) = μ
axiom mvn_moment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square x) = square μ + square σ

-- central moments (provable in terms of moments)
lemma mvn_cmoment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (x - μ)) = 0 := by
  have H_int_x : is_integrable (λ x => mvn_pdf μ σ x • x) := by
    apply mvn_moment₁_int μ σ H_σ
  have H_int_μ : is_integrable (λ x => - (mvn_pdf μ σ x • μ)) := by
    apply Iff.mp (is_integrable_neg _) (mvn_const_int μ σ H_σ μ)
  calc  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (x - μ))
      = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • x + - (T.mvn_pdf μ σ x • μ)) := by simp [minus_eq_add_neg, smul_addr, smul_neg]
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • x) - ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • μ) := by
      rw [integral_add]
      rw [integral_neg]
      rfl
      assumption
      assumption
      -- rw [← minus_eq_add_neg]
      -- simp [integral_add, H_int_x, H_int_μ, integral_neg]
    _ = μ - μ := by { rw [mvn_expected _ _ H_σ, mvn_moment₁ _ _ H_σ]}
    _ = 0 := by simp

-- Exercise for the reader: prove
axiom mvn_cmoment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square (x - μ)) = square σ

-- central scaled moments (provable in terms of central moments)
lemma mvn_csmoment₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((x - μ) / σ)) = 0 := by
  have H_int_xσ : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • (x / σ)) := by
    { simp [smul_div]; exact Iff.mp (is_integrable_div _ _ H_σ) (mvn_moment₁_int _ _ H_σ) }

  have H_int_μσ : is_integrable (λ (x : T shape) => -(T.mvn_pdf μ σ x • (μ / σ))) := by
    { apply Iff.mp (is_integrable_neg _); simp [smul_div]; exact Iff.mp (is_integrable_div _ _ H_σ) (mvn_const_int _ _ H_σ _) }

  calc  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((x - μ) / σ))
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (x / σ) - (T.mvn_pdf μ σ x • (μ / σ))) := by
      simp [minus_eq_add_neg,T.div_add_div_same_symm, smul_addr, sum_add, neg_div, smul_neg, integral_neg]
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (x / σ)) - ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (μ / σ)) := by
      simp [minus_eq_add_neg,integral_add, H_int_xσ, H_int_μσ, integral_neg]
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • x) / σ - ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (μ / σ)) := by simp [smul_div, integral_div]
    _ = μ / σ - μ / σ := by rw [mvn_moment₁ _ _ H_σ, mvn_expected _ _ H_σ]
    _ = 0 := by simp

-- Exercise for the reader: prove
axiom mvn_csmoment₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square ((x - μ) / σ)) = (1 : T shape)

-- lemma mvn_helper_1 {shape : S} (x : T shape) : (- 2⁻¹) = const (-2⁻¹) shape  := by
--   rw [const_neg]

-- unfold mvn_pdf
-- rfl

-- -- simp
-- rw [H0]
-- rw [smul.def]
-- rw [scalar_mul]

--   rfl
--   simp
-- essentially, we want to say  "- (1/2)"" is equal to 1/(-2) ??
--  (- 1/2 : T shape) = const (- 1/2 : TReal) shape

-- lemma mvn_helper_1 {shape : S}  : const 2 shape = 2 := by

lemma mvn_logpdf_correct {shape : S} (μ σ x : T shape) (H_σ : σ > 0) : log (mvn_pdf μ σ x) = mvn_logpdf μ σ x := by
  have H_σ₂ : square σ > 0 := by apply square_pos_of_pos H_σ
  -- have H0 : 2 * pi shape = 2 • pi shape := by simp
  have H_mul : (2 * pi shape) * square σ > 0 := by
    apply  mul_pos_of_pos_pos two_pi_pos
    assumption
    -- rw [H0]
    -- apply mul_pos_of_pos_pos two_pi_pos H_σ₂
  have H_sqrt : (sqrt ((2 * pi shape) * square σ))⁻¹ > 0 := by apply inv_pos (sqrt_pos H_mul)
  have H_exp : exp ((- 2⁻¹) * (square $ (x - μ) / σ)) > 0 := by apply exp_pos
  have H_mul₂ : (sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)) > 0 := by apply mul_pos_of_pos_pos H_sqrt H_exp

  calc  log (mvn_pdf μ σ x)
      = log (prod ((sqrt ((2 * pi shape) * square σ))⁻¹ * exp ((- 2⁻¹) * (square $ (x - μ) / σ)))) := by rfl
    _ = sum (log ((sqrt ((2 * pi shape) * square σ))⁻¹) + ((- 2⁻¹) * (square $ (x - μ) / σ))) := by simp only [log_prod H_mul₂, log_mul H_sqrt H_exp, log_exp]
    _ = sum ((- 2⁻¹) * log ((2 * pi shape) * square σ) + ((- 2⁻¹) * (square $ (x - μ) / σ))) := by simp [log_inv, log_sqrt]
    _ = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ)) + (- 2⁻¹) * (square $ (x - μ) / σ)) := by simp only [log_mul two_pi_pos H_σ₂]
    _ = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) := by simp only [left_distrib]
    _ = sum ((- (2 : TReal)⁻¹) • (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) := by
          simp only [smul.def, const_neg, const_inv, const_bit0, const_one]
          rw [two_shape_eq_two]
    _ = (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ)) := by
          simp [sum_smul]
          simp [add_comm]
          simp [← add_assoc]
          simp [add_comm σ.square.log]

-- _ = sum (log ((sqrt ((2 * pi shape) * square σ))⁻¹) + ((- 2⁻¹) * (square $ (x - μ) / σ))) : by simp only [log_prod H_mul₂, log_mul H_sqrt H_exp, log_exp]
-- _ = sum ((- 2⁻¹) * log ((2 * pi shape) * square σ) + ((- 2⁻¹) * (square $ (x - μ) / σ))) : by simp [log_inv, log_sqrt]
-- _ = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ)) + (- 2⁻¹) * (square $ (x - μ) / σ)) : by simp only [log_mul two_pi_pos H_σ₂]
-- _ = sum ((- 2⁻¹) * (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) : by simp only [left_distrib]
-- _ = sum ((- (2 : TReal)⁻¹) • (log (2 * pi shape) + log (square σ) + (square $ (x - μ) / σ))) : by simp only [smul.def, const_neg, const_inv, const_bit0, const_one]
-- _ = (- 2⁻¹) * sum (square ((x - μ) / σ) + log (2 * pi shape) + log (square σ)) : by simp [sum_smul]
-- _ = mvn_logpdf μ σ x : rfl

lemma mvn_int_const {shape : S} (μ σ : T shape) (H_σ : σ > 0) (y : TReal) :
  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • y) = y :=
by { rw [integral_fscale, (mvn_pdf_int1 _ _ H_σ), one_smul] }

lemma mvn_integral₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape) => T.mvn_pdf μ σ x • T.mvn_logpdf 0 1 x)
=
(- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape)) := by

  have H_sq_x_int : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • square x) := by apply mvn_moment₂_int _ _ H_σ
  have H_log_pi_int : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • log (2 * pi shape)) := by apply mvn_const_int _ _ H_σ _
  have H_sum_int : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • (square x + log (2 * pi shape))) := by
    simp only [smul_addr]; exact Iff.mp (is_integrable_add _ _) (And.intro H_sq_x_int H_log_pi_int)
  calc  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (square ((x - 0) / 1) + log (2 * pi shape) + log (square 1))))
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (square x + log (2 * pi shape)))) := by simp [log_one, square, T.div_one]
    _ = ∫ (λ (x : T shape) => (- (2 : TReal)⁻¹) • (T.mvn_pdf μ σ x • sum (square x + log (2 * pi shape)))) := by simp only [smul_mul_scalar_right]
    _ = (- 2⁻¹) * ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • sum (square x + log (2 * pi shape))) := by { simp only [integral_scale]; simp [smul.def] }
    _ = (- 2⁻¹) * sum (∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (square x + log (2 * pi shape)))) := by { simp only [integral_sum, H_sum_int, smul_sum] }
    _ = (- 2⁻¹) * sum (∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square x + T.mvn_pdf μ σ x • log (2 * pi shape))) := by { simp only [smul_addr] }
    _ = (- 2⁻¹) * sum (∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square x) + ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • log (2 * pi shape))) := by { simp only [integral_add, H_sq_x_int, H_log_pi_int] }
    _ = (- 2⁻¹) * (sum (square μ + square σ) + sum (log (2 * pi shape))) := by rw [mvn_moment₂ _ _ H_σ, mvn_expected _ _ H_σ, sum_add]
    _ = (- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape)) := by rw [left_distrib]


lemma mvn_integral₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape) => T.mvn_pdf μ σ x • T.mvn_logpdf μ σ x)
=
(- 2⁻¹) * sum (1 : T shape) + (- 2⁻¹) * sum (log (2 * pi shape)) + (- 2⁻¹) * sum (log (square σ)) := by
  have H_int₁ : is_integrable (λ (x : T shape) => mvn_pdf μ σ x • (-2⁻¹ * sum (square ((x - μ) / σ)))) := by
    simp only [smul_mul_scalar_right, integral_scale]
    apply Iff.mp (is_integrable_scale _ _)
    simp only [smul_sum]
    apply Iff.mp (is_integrable_sum _)
    simp only [square_div, smul_div]
    apply Iff.mp (is_integrable_div _ _ (square_pos_of_pos H_σ))
    exact mvn_cmoment₂_int _ _ H_σ

  have H_int₂ : is_integrable (λ (x : T shape) => mvn_pdf μ σ x • (-2⁻¹ * sum (log (2 * pi shape)))) := by
    simp only [smul_mul_scalar_right, integral_scale]
    apply Iff.mp (is_integrable_scale _ _)
    simp only [smul_sum]
    apply Iff.mp (is_integrable_sum _)
    exact mvn_const_int _ _ H_σ _

  have H_int₁₂ : is_integrable (λ (x : T shape) => mvn_pdf μ σ x • (-2⁻¹ * sum (square ((x - μ) / σ))) + mvn_pdf μ σ x • (-2⁻¹ * sum (log (2 * pi shape)))) := by
    apply Iff.mp (is_integrable_add _ _) (And.intro H_int₁ H_int₂)

  have H_int₃ : is_integrable (λ (x : T shape) => mvn_pdf μ σ x • (-2⁻¹ * sum (log (square σ)))) := by
    simp only [smul_mul_scalar_right, integral_scale]
    apply Iff.mp (is_integrable_scale _ _)
    simp only [smul_sum]
    apply Iff.mp (is_integrable_sum _)
    exact mvn_const_int _ _ H_σ _

  have H_int₄ : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • square ((x - μ) / σ)) := by
    simp only [square_div, smul_div]
    apply Iff.mp (is_integrable_div _ _ (square_pos_of_pos H_σ))
    exact mvn_cmoment₂_int _ _ H_σ


  have H₁ : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (square ((x - μ) / σ)))) = (- 2⁻¹) * sum (1 : T shape) := by
    calc  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (square ((x - μ) / σ))))
        = ∫ (λ (x : T shape) => (- (2 : TReal)⁻¹) • (T.mvn_pdf μ σ x • sum (square ((x - μ) / σ)))) := by simp only [smul_mul_scalar_right]
      _ = (- 2⁻¹) * ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • sum (square ((x - μ) / σ))) := by { simp only [integral_scale]; simp [smul.def] }
      _ = (- 2⁻¹) * sum (∫ (λ (x : T shape) => T.mvn_pdf μ σ x • square ((x - μ) / σ))) := by simp only [smul_sum, integral_sum, H_int₄]
      _ = (- 2⁻¹) * sum (1 : T shape) := by rw [(mvn_csmoment₂ _ _ H_σ)]

  have H₂ : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (log (2 * pi shape)))) = (- 2⁻¹) * sum (log (2 * pi shape)) := by rw [(mvn_int_const μ _ H_σ)]

  have H₃ : ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • ((- 2⁻¹) * sum (log (square σ)))) = (- 2⁻¹) * sum (log (square σ)) := by rw [mvn_int_const μ _ H_σ]

  unfold mvn_logpdf
  simp only [sum_add, left_distrib, smul_addr, integral_add, H₁, H₂, H₃, H_int₁₂, H_int₁, H_int₂, H_int₃]

lemma mvn_kl_identity {shape : S} (μ σ : T shape) (H_σ : σ > 0) :
∫ (λ (x : T shape) => T.mvn_pdf μ σ x • T.mvn_empirical_kl μ σ x)
=
T.mvn_kl μ σ := by
  have H_logpdf_int : is_integrable (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_logpdf μ σ x) := by apply mvn_logpdf_int μ μ σ σ H_σ H_σ

  have H_std_logpdf_int : is_integrable (λ (x : T shape) => - (T.mvn_pdf μ σ x • mvn_logpdf 0 1 x)) := by apply Iff.mp (is_integrable_neg _) (mvn_logpdf_int μ 0 σ 1 H_σ one_pos)

  calc  ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • T.mvn_empirical_kl μ σ x)
      = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • (mvn_logpdf μ σ x - mvn_logpdf 0 1 x)) := rfl
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_logpdf μ σ x + - (T.mvn_pdf μ σ x • mvn_logpdf 0 1 x)) := by
        simp [sub_eq_neg_add, smul_addr, smul_neg, add_comm]
    _ = ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_logpdf μ σ x) - ∫ (λ (x : T shape) => T.mvn_pdf μ σ x • mvn_logpdf 0 1 x) := by
        simp [sub_eq_neg_add, integral_add, H_logpdf_int, H_std_logpdf_int, integral_neg, add_comm]
    _ = ((- 2⁻¹) * sum (1 : T shape) + (- 2⁻¹) * sum (log (2 * pi shape)) + (- 2⁻¹) * sum (log (square σ))) - ((- 2⁻¹) * sum (square μ + square σ) + (- 2⁻¹) * sum (log (2 * pi shape))) := by rw [mvn_integral₁ μ σ H_σ, mvn_integral₂ μ σ H_σ]
    _ = (- 2⁻¹) * sum ((1 : T shape) + log (2 * pi shape) + log (square σ) - square μ - square σ - log (2 * pi shape)) := by
        -- rw [sum_add]
        simp [sub_eq_neg_add, sum_add, left_distrib, sum_neg]
        ring

    _ = (- 2⁻¹) * sum ((1 : T shape) + log (square σ) - square μ - square σ + (log (2 * pi shape) - log (2 * pi shape))) := by simp [sub_eq_neg_add]; ring
    _ = (- 2⁻¹) * sum ((1 : T shape) + log (square σ) - square μ - square σ) := by simp
    _ = T.mvn_kl μ σ := rfl

end T
end certigrad
