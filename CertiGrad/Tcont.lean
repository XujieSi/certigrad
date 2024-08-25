/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of continuous functions.
-/
-- import .tfacts .util

import CertiGrad.Tfacts
import CertiGrad.Util


namespace certigrad
namespace T

open util_list

-- def x : List Nat := []
-- def y := x.sum

axiom continuous_id : ∀ {ishape : S} (x : T ishape), is_continuous (λ (x₀ : T ishape) => x₀) x
axiom continuous_const : ∀ {ishape oshape : S} (y : T oshape) (x : T ishape), is_continuous (λ (x₀ : T ishape) => y) x

axiom continuous_add_fs {ishape oshape : S} (f g : T ishape → T oshape) (x : T ishape) :
  is_continuous f x → is_continuous g x → is_continuous (λ x₀ => f x₀ + g x₀) x

lemma continuous_sumr {α : Type} {ishape oshape : S} (f : α → T ishape → T oshape) (x : T ishape) :
  ∀ (γs : List α), (∀ (γ : α), γ ∈ γs → is_continuous (λ (x₀ : T ishape) => f γ x₀) x) →
  is_continuous (λ (x₀ : T ishape) => sumr (List.map (λ γ => f γ x₀) γs)) x
  | [], H => by apply (continuous_const 0)
  | (γ::γs), H => by
    unfold sumr List.map
    apply (continuous_add_fs _ _ _ (H γ mem_of_cons_same))
    apply continuous_sumr
    intros γ' H_γ'
    exact H γ' (List.mem_cons_of_mem _ H_γ')


axiom continuous_chain_full {ishape oshape fshape : S} {f : T ishape → T oshape} {g : T ishape → T oshape → T fshape} {x : T ishape} :
  is_continuous f x → is_continuous (λ x₀ => g x₀ (f x)) x → is_continuous (g x) (f x) → is_continuous (λ x₀ => g x₀ (f x₀)) x

lemma continuous_chain {ishape oshape fshape : S} (f : T ishape → T oshape) (g : T oshape → T fshape) (x : T ishape) :
  is_continuous f x → is_continuous g (f x) → is_continuous (λ x => g (f x)) x := by
  intros H_cont_f H_cont_g
  let h : T ishape → T oshape → T fshape := λ x y => g y
  let H_cont_h₁ : is_continuous (λ x₀ => h x₀ (f x)) x := by
    apply (continuous_const (g (f x)))
  let H_cont_h₂ : is_continuous (h x) (f x) := by apply H_cont_g
  apply continuous_chain_full H_cont_f H_cont_h₁ H_cont_h₂

-- assume (H_cont_f : is_continuous f x) (H_cont_g : is_continuous g (f x)),
-- let h : T ishape → T oshape → T fshape := λ x y => g y in
-- have H_cont_h₁ : is_continuous (λ x₀ => h x₀ (f x)) x, by apply (continuous_const (g (f x))),
-- have H_cont_h₂ : is_continuous (h x) (f x), from H_cont_g,
-- continuous_chain_full H_cont_f H_cont_h₁ H_cont_h₂

axiom continuous_binary {ishape oshape : S} (f : T ishape → T ishape → T oshape) (θ : T ishape) :
  is_continuous (λ θ₀ => f θ₀ θ) θ → is_continuous (λ θ₀ => f θ θ₀) θ → is_continuous (λ θ₀ => f θ₀ θ₀) θ

-- lemma continuous_congr {ishape oshape : S} (f g : T ishape → T oshape) (x : T ishape) :
--   (∀ x₀, g x₀ = f x₀) → is_continuous f x → is_continuous g x :=
-- begin intros H H_f, assert H_gf : g = f, { exact funext H }, rw H_gf, exact H_f end

axiom continuous_lift₀ {shape : S} (α : TReal) : is_continuous (λ α : TReal => const α shape) α
axiom continuous_scale {shape : S} (α : TReal) (x : T shape) : is_continuous (λ x₀ => α • x₀) x
axiom continuous_neg {shape : S} {θ : T shape} : is_continuous neg θ
axiom continuous_exp {shape : S} {θ : T shape} : is_continuous exp θ
axiom continuous_log {shape : S} {θ : T shape} : θ > 0 → is_continuous log θ
axiom continuous_sqrt {shape : S} {θ : T shape} : θ > 0 → is_continuous sqrt θ
axiom continuous_add₁ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => θ₀ + x) θ
axiom continuous_add₂ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => x + θ₀) θ
axiom continuous_mul₁ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => θ₀ * x) θ
axiom continuous_mul₂ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => x * θ₀) θ
axiom continuous_sub₁ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => θ₀ - x) θ
axiom continuous_sub₂ {shape : S} {θ x : T shape} : is_continuous (λ θ₀ => x - θ₀) θ
axiom continuous_div₁ {shape : S} {θ x : T shape} : square x > 0 → is_continuous (λ θ₀ => θ₀ / x) θ
axiom continuous_div₂ {shape : S} {θ x : T shape} : square θ > 0 → is_continuous (λ θ₀ => x / θ₀) θ
axiom continuous_sum {shape : S} {θ : T shape} : is_continuous sum θ
axiom continuous_gemm₁ {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : is_continuous (λ M₀ => T.gemm M₀ N) M
axiom continuous_gemm₂ {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : is_continuous (λ N₀ => T.gemm M N₀) N

lemma continuous_square {shape : S} (θ : T shape) : is_continuous (λ x => T.square x) θ :=
by { apply continuous_binary (λ θ₁ θ₂ => θ₁ * θ₂); apply continuous_mul₁; apply continuous_mul₂ }

axiom continuous_mvn_pdf_μ {shape : S} (μ σ x : T shape) (H_σ : σ > 0) : is_continuous (λ θ => mvn_pdf θ σ x) μ
axiom continuous_mvn_pdf_σ {shape : S} (μ σ x : T shape) (H_σ : σ > 0) : is_continuous (λ θ => mvn_pdf μ θ x) σ

lemma continuous_scale_fs {ishape oshape : S} {f : T ishape → TReal} {g : T ishape → T oshape} {θ : T ishape} :
                          is_continuous f θ → is_continuous g θ → is_continuous (λ θ₀ => f θ₀ • g θ₀) θ := by
  intros H_cont_f H_cont_g
  apply (continuous_binary (λ θ₁ θ₂ => f θ₁ • g θ₂))
  apply (continuous_chain f (λ θ₀ => θ₀ • g θ) _ H_cont_f)
  simp [T.smul.def]
  apply (continuous_chain (λ θ₀ => const θ₀ oshape) (λ θ₀ => θ₀ * g θ) _)
  apply continuous_lift₀
  apply continuous_mul₁
  apply (continuous_chain g (λ θ₀ => f θ • θ₀) _ H_cont_g)
  apply continuous_scale

-- assume (H_cont_f : is_continuous f θ) (H_cont_g : is_continuous g θ),
-- begin
-- apply (continuous_binary (λ θ₁ θ₂ => f θ₁ ⬝ g θ₂)),
-- apply (continuous_chain f (λ θ₀ => θ₀ ⬝ g θ) _ H_cont_f),
-- simp [T.smul.def],
-- apply (continuous_chain (λ θ₀ => const θ₀ oshape) (λ θ₀ => g θ * θ₀) _),
-- apply continuous_lift₀,
-- apply continuous_mul₂,
-- apply (continuous_chain g (λ θ₀ => f θ ⬝ θ₀) _ H_cont_g),
-- apply continuous_scale
-- end

lemma continuous_fscale {ishape oshape : S} {f : T ishape → TReal} {x : T oshape} {θ : T ishape} :
                        is_continuous f θ → is_continuous (λ θ₀ => f θ₀ • x) θ := by
  intro H_cont_f
  apply continuous_scale_fs
  assumption
  apply continuous_const

lemma continuous_scale_f {ishape oshape : S} (α : TReal) (f : T ishape → T oshape) (x : T ishape) : is_continuous f x → is_continuous (λ x₀ => α • f x₀) x := by
  intro H_f_cont
  apply continuous_scale_fs (continuous_const α x) H_f_cont


-- Note: this could be proved from the `select`/`replicate` formulation,
-- but it is arguably a more natural way of axiomatizing the property.

-- axiom continuous_multiple_args :
--   ∀ (parents : List Reference) (oshape : S) (tgt : Reference) (m : env)
--     (f : dvec T parents^.p2 → T oshape) (θ : T tgt.2),
--     (∀ (idx : ℕ), at_idx parents idx tgt →
--     is_continuous (λ θ₀ => f (dvec.update_at θ₀ (env.get_ks parents (env.insert tgt θ m)) idx)) θ)
--     →
--     is_continuous (λ θ₀ => f (env.get_ks parents (env.insert tgt θ₀ m))) θ

end T

-- section tactic
-- open tactic

-- meta def prove_continuous_core : tactic unit :=
-- first [
--        applyc `certigrad.T.continuous_id
--      , applyc `certigrad.T.continuous_const
--      , applyc `certigrad.T.continuous_add_fs
--      , applyc `certigrad.T.continuous_sumr

--      -- TODO(dhs): bug in Lean
--      -- This causes a silent "sorry" in prove_continuous_core with
--      -- no explanation
-- --     , applyc `certigrad.T.continuous_mvn_kl₁
-- --     , applyc `certigrad.T.continuous_mvn_kl₂,

--      , applyc `certigrad.T.continuous_lift₀
--      , applyc `certigrad.T.continuous_scale
--      , applyc `certigrad.T.continuous_neg
--      , applyc `certigrad.T.continuous_exp
--      , applyc `certigrad.T.continuous_log
--      , applyc `certigrad.T.continuous_sqrt
--      , applyc `certigrad.T.continuous_add₁
--      , applyc `certigrad.T.continuous_add₂
--      , applyc `certigrad.T.continuous_mul₁
--      , applyc `certigrad.T.continuous_mul₂
--      , applyc `certigrad.T.continuous_sub₁
--      , applyc `certigrad.T.continuous_sub₂
--      , applyc `certigrad.T.continuous_div₁
--      , applyc `certigrad.T.continuous_div₂
--      , applyc `certigrad.T.continuous_sum
--      , applyc `certigrad.T.continuous_gemm₁
--      , applyc `certigrad.T.continuous_gemm₂
--      , applyc `certigrad.T.continuous_square
--      , applyc `certigrad.T.continuous_mvn_pdf_μ
--      , applyc `certigrad.T.continuous_mvn_pdf_σ
--      , applyc `certigrad.T.continuous_scale_fs
--      , applyc `certigrad.T.continuous_scale_f
--      , applyc `certigrad.T.continuous_chain
--      , assumption
-- ]

-- meta def prove_continuous : tactic unit := repeat (prove_continuous_core <|> prove_preconditions_core)

-- end tactic

-- namespace T

-- -- lemma continuous_mvn_kl₁ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : is_continuous (λ μ₀ => mvn_kl μ₀ σ) μ :=
-- -- by { dunfold mvn_kl, prove_continuous }

-- -- lemma continuous_mvn_kl₂ {shape : S} (μ σ : T shape) (H_σ : σ > 0) : is_continuous (λ σ₀ => mvn_kl μ σ₀) σ :=
-- -- have H_σ₂ : square σ > 0, from square_pos_of_pos H_σ,
-- -- by { dunfold mvn_kl, prove_continuous }

-- -- lemma continuous_bernoulli_neglogpdf₁ {shape : S} (p x : T shape) (H_p₁ : p > 0) (H_p₂ : 1 - p > 0) :
-- -- is_continuous (λ p₀ => bernoulli_neglogpdf p₀ x) p :=
-- -- by { dunfold bernoulli_neglogpdf, prove_continuous }

-- -- lemma continuous_bernoulli_neglogpdf₂ {shape : S} (p x : T shape) (H_p₁ : p > 0) (H_p₂ : 1 - p > 0) :
-- -- is_continuous (λ x₀ => bernoulli_neglogpdf p x₀) x :=
-- -- begin
-- -- dunfold bernoulli_neglogpdf,
-- -- apply continuous_binary (λ θ₁ θ₂ => - T.sum (θ₁ * T.log (eps shape + p) + (1 - θ₂) * T.log (eps shape + (1 + -p)))),
-- -- dsimp,
-- -- prove_continuous,
-- -- -- TODO(dhs): not sure why this is necessary
-- -- apply continuous_chain (λ x => 1 - x) (λ y => y * log (eps shape + (1 + - p))),
-- -- prove_continuous,
-- -- end

-- end T

end certigrad
