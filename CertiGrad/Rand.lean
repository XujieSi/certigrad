/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic operators.
-/
-- import .tensor .tfacts .tgrads .tcont .mvn

import CertiGrad.Tensor
import CertiGrad.Tfacts
import CertiGrad.Tgrads
import CertiGrad.Tcont
import CertiGrad.Mvn
import CertiGrad.Dvec

namespace certigrad

namespace rand
open util_list dvec

set_option linter.unusedVariables false
-- dvec is a namespace

-- `Dvec T ishapes` contains multiple tensors, each of which may have different shapes (specified by ishapes)
-- pdf_function is quite flexible in the sense that it may take as input different input tensors (even shapes can be different)
-- produce distribution over one common shape tensor as output
-- a single element/shape in ishapes should be sufficient for most cases,
-- since usually a function takes one specific shape as input and produce one specific shape as output
-- In fact, the ishapes is more like hyper-paramters (e.g., mean, variances) and the oshape is more like the "input"
-- because the real output is a numeric probability value between 0 and 1
-- For a probability function, we essentially "query" the probability over a space (i.e., described by the oshape)
def pdf_function (ishapes : List S) (oshape : S) : Type := Dvec T ishapes → T oshape → TReal

-- `state` is not available in Lean4
-- Lean3 doc: https://leanprover-community.github.io/mathlib_docs/init/control/state.html#state

def rng_function (ishapes : List S) (oshape : S) : Type := Dvec T ishapes → StateM RNG (T oshape)

def precondition (ishapes : List S) : Type := Dvec T ishapes → Prop

-- here, `(λ θ₀ => pdf (dvec.update_at θ₀ xs idx) y)` essentially says that
-- we only consider a specific shape of tensor (i.e. the i-th one specified in xs) as input
-- vary its value (i.e., θ₀) of that particular shape via update_at
-- The continuous property stated here is somewhat strange in the sense that
-- it describes if we vary the hyper-parameters (e.g., mean or variance) slightly,
-- the changes of probability over some predefined event (specified by y) also change slightly
noncomputable def pdf_cdiff {ishapes : List S} {oshape : S} (pdf : pdf_function ishapes oshape) (pdf_pre : precondition ishapes) : Prop :=
  ∀ ⦃xs : Dvec T ishapes⦄ {y : T oshape} {idx : ℕ} {fshape : S},
  at_idx ishapes idx fshape → pdf_pre xs →
  T.is_cdifferentiable (λ θ₀ => pdf (dvec.update_at θ₀ xs idx) y) (dvec.get fshape _ xs idx)

def grad_logpdf (ishapes : List S) (oshape : S) : Type := Dvec T ishapes → T oshape → Π (idx : ℕ) (fshape : S), T fshape

def pdf_positive {ishapes : List S} {oshape : S} (pdf : pdf_function ishapes oshape) (pdf_pre : precondition ishapes) : Prop :=
  ∀ (xs : Dvec T ishapes), pdf_pre xs → ∀ (y : T oshape), pdf xs y > 0

-- here, we can see the actual input is essentially the output space (i.e., the space over which the distribution of interest is about)
-- values of ishapes are fixed for the integration: ∫ (λ (y : T oshape) => pdf xs y) = 1
noncomputable def pdf_integrates_to_one {ishapes : List S} {oshape : S} (pdf : pdf_function ishapes oshape) (pdf_pre : precondition ishapes) : Prop :=
  ∀ (xs : Dvec T ishapes), pdf_pre xs → ∫ (λ (y : T oshape) => pdf xs y) = 1

noncomputable def grad_logpdf_correct {ishapes : List S} {oshape : S}
                        (pdf : pdf_function ishapes oshape) (pdf_pre : precondition ishapes) (pdf_grad : grad_logpdf ishapes oshape) : Prop :=
  ∀ ⦃xs : Dvec T ishapes⦄ {y : T oshape} {idx : ℕ} {ishape : S},
    util_list.at_idx ishapes idx ishape →
    pdf_pre xs →
    pdf_grad xs y idx ishape
    =
    ∇ (λ (θ₀ : T ishape) => T.log (pdf (dvec.update_at θ₀ xs idx) y)) (dvec.get ishape _ xs idx)

noncomputable def continuous {ishapes : List S} {oshape : S} (pdf : pdf_function ishapes oshape) (pdf_pre : precondition ishapes) : Prop :=
  ∀ ⦃xs : Dvec T ishapes⦄ {y : T oshape} {idx : ℕ} {tshape : S},
    util_list.at_idx ishapes idx tshape →
    pdf_pre xs → T.is_continuous (λ (x : T tshape) => pdf (dvec.update_at x xs idx) y) (dvec.get tshape _ xs idx)

namespace pdf

-- set_option trace.Elab.match true
noncomputable def mvn (shape : S) : pdf_function [shape, shape] shape
| ⟦μ, σ⟧, x => T.mvn_pdf μ σ x

noncomputable def mvn_std (shape : S) : pdf_function [] shape
| ⟦⟧, x => T.mvn_pdf 0 1 x

end pdf

namespace run

noncomputable def mvn (shape : S) : rng_function [shape, shape] shape
| ⟦μ, σ⟧ => T.sample_mvn μ σ

noncomputable def mvn_std (shape : S) : rng_function [] shape
| ⟦⟧ => T.sample_mvn 0 1

end run

namespace pre

def mvn : (shape : S) → precondition [shape, shape]
| shape => λ xs => xs.head2 > 0

def mvn_std : (shape : S) → precondition []
| shape => λ xs => True

end pre

namespace pdiff

def mvn (shape : S) : pdf_cdiff (pdf.mvn shape) (pre.mvn shape)
| ⟦μ, σ⟧, x, 0, ishape, H_at_idx, H_pre => by
  clear mvn
  have H_ishape_eq := H_at_idx.right
  simp [util_list.dnth] at H_ishape_eq
  subst H_ishape_eq
  dsimp [dvec.update_at, dvec.get]
  simp
  unfold pdf.mvn T.mvn_pdf

  simp -- get rid of the match

  -- the axioms are not quite intuitive,
  -- is_cdifferentiable k (log θ) → is_cdifferentiable (λ θ => k (log θ)) θ
  -- what if θ is used not once but in many different ways, e.g., log θ + exp θ ??
  -- in this case, is_cdifferentiable_binary seems to work
  -- In contrast, the other way around might be much better, for instance,
  -- is_cdifferentiable k θ → is_cdifferentiable (λ θ => log (k θ)) θ

  -- given: (fun θ₀ => ((2 * T.pi ishape * σ.square).sqrt⁻¹ * (-(2⁻¹ * ((x - θ₀) / σ).square)).exp).prod)
  -- to use T.is_cdifferentiable_sub₂
  -- we need to figure out k (the structure of wrapping up the internal x - θ₀)
  -- apply T.is_cdifferentiable_sub₂ (x₁ := x)
  -- apply T.is_cdifferentiable_prod
  proveDifferentiable

  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable
  -- proveDifferentiable

  -- apply T.is_cdifferentiable_id

-- | ⟦μ, σ⟧ x 1 ishape H_at_idx H_pre :=
-- have H_σ₂ : T.square σ > 0, from T.square_pos_of_pos H_pre,
-- have H_inv : T.sqrt (2 * T.pi shape * T.square σ) > 0, from T.sqrt_pos (T.mul_pos_of_pos_pos (T.mul_pos_of_pos_pos T.two_pos T.pi_pos) H_σ₂),
-- begin
-- clear mvn,
-- note H_ishape_eq := H_at_idx^.right,
-- dsimp [list.dnth] at H_ishape_eq,
-- subst H_ishape_eq,
-- dsimp [dvec.update_at, dvec.get],
-- simp,
-- dunfold pdf.mvn T.mvn_pdf,
-- apply T.is_cdifferentiable_binary (λ θ₁ θ₂, T.prod ((T.sqrt (2 * T.pi ishape * T.square θ₁))⁻¹ * T.exp (-2⁻¹ * T.square ((x - μ) / θ₂)))),
-- all_goals { dsimp, T.prove_differentiable }
-- end

-- | ⟦μ, σ⟧ x (n+2) ishape H_at_idx H_pre := false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

-- def mvn_std (shape : S) : pdf_cdiff (pdf.mvn_std shape) (pre.mvn_std shape)
-- | ⟦⟧, x, tgt, ishape, H_at_idx, H_pre => false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

end pdiff

-- namespace glogpdf

-- def mvn (shape : S) : grad_logpdf [shape, shape] shape
-- | ⟦μ, σ⟧ x 0     fshape => T.force (T.mvn_grad_logpdf_μ μ σ x) fshape
-- | ⟦μ, σ⟧ x 1     fshape => T.force (T.mvn_grad_logpdf_σ μ σ x) fshape
-- | ⟦μ, σ⟧ x (n+2) fshape => T.error "mvn grad_logpdf: index too large"

-- def mvn_std (shape : S) : grad_logpdf [] shape
-- | ⟦⟧ x idx fshape => 0

-- end glogpdf

-- namespace glogpdf_correct

-- lemma mvn (shape : S) : grad_logpdf_correct (pdf.mvn shape) (pre.mvn shape) (glogpdf.mvn shape)
-- | ⟦μ, σ⟧ x 0     ishape H_at_idx H_pre :=
-- begin
-- clear mvn,
-- note H_ishape_eq := H_at_idx^.right,
-- dsimp [list.dnth] at H_ishape_eq,
-- subst H_ishape_eq,
-- dsimp [dvec.update_at, dvec.get],
-- simp,
-- assert H : ∀ (θ₀ : T ishape), T.log (pdf.mvn ishape ⟦θ₀, σ⟧ x) = T.mvn_logpdf θ₀ σ x,
-- { intro θ₀, simp [pdf.mvn, T.mvn_logpdf_correct θ₀ σ x H_pre] },
-- rw (funext H), clear H,
-- erw T.mvn_grad_logpdf_μ_correct _ _ _ H_pre,
-- simp [glogpdf.mvn, dvec.head2]
-- end

-- | ⟦μ, σ⟧ x 1     ishape H_at_idx H_pre :=
-- begin
-- clear mvn,
-- note H_ishape_eq := H_at_idx^.right,
-- dsimp [list.dnth] at H_ishape_eq,
-- subst H_ishape_eq,
-- dsimp [dvec.update_at, dvec.get],
-- simp,
-- assert H : ∀ (θ₀ : T ishape), θ₀ > 0 → T.log (pdf.mvn ishape ⟦μ, θ₀⟧ x) = T.mvn_logpdf μ θ₀ x,
-- { intros θ₀ H_θ₀, simp [pdf.mvn, T.mvn_logpdf_correct μ θ₀ x H_θ₀] },

-- erw T.grad_congr_pos _ _ _ H_pre H,
-- clear H,
-- erw T.mvn_grad_logpdf_σ_correct _ _ _ H_pre,
-- simp [glogpdf.mvn, dvec.head2]
-- end
-- | ⟦μ, σ⟧ x (n+2) ishape H_at_idx H_pre => false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

-- lemma mvn_std (shape : S) : grad_logpdf_correct (pdf.mvn_std shape) (pre.mvn_std shape) (glogpdf.mvn_std shape)
-- | ⟦⟧ x idx     ishape H_at_idx H_pre => false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

-- end glogpdf_correct

-- namespace pdf_pos

-- lemma mvn (shape : S) : pdf_positive (pdf.mvn shape) (pre.mvn shape)
-- | ⟦μ, σ⟧ H_pre y => T.mvn_pdf_pos μ σ H_pre y

-- lemma mvn_std (shape : S) : pdf_positive (pdf.mvn_std shape) (pre.mvn_std shape)
-- | ⟦⟧ H_pre y => T.mvn_pdf_pos 0 1 T.one_pos y

-- end pdf_pos

-- namespace pdf_int1

-- lemma mvn (shape : S) : pdf_integrates_to_one (pdf.mvn shape) (pre.mvn shape)
-- | ⟦μ, σ⟧ H_pre => T.mvn_pdf_int1 μ σ H_pre

-- lemma mvn_std (shape : S) : pdf_integrates_to_one (pdf.mvn_std shape) (pre.mvn_std shape)
-- | ⟦⟧ H_pre => T.mvn_pdf_int1 0 1 T.one_pos

-- end pdf_int1

-- namespace cont

-- lemma mvn (shape : S) : continuous (pdf.mvn shape) (pre.mvn shape)
-- | ⟦μ, σ⟧ x 0     tshape H_at_idx H_pre :=
-- begin
-- clear mvn,
-- note H_ishape_eq := H_at_idx^.right,
-- dsimp [list.dnth] at H_ishape_eq,
-- subst H_ishape_eq,
-- dsimp [dvec.update_at, dvec.get],
-- simp,
-- apply T.continuous_mvn_pdf_μ,
-- exact H_pre
-- end
-- | ⟦μ, σ⟧ x 1     tshape H_at_idx H_pre :=
-- begin
-- clear mvn,
-- note H_ishape_eq := H_at_idx^.right,
-- dsimp [list.dnth] at H_ishape_eq,
-- subst H_ishape_eq,
-- dsimp [dvec.update_at, dvec.get],
-- simp,
-- apply T.continuous_mvn_pdf_σ,
-- exact H_pre
-- end

-- | ⟦μ, σ⟧ x (n+2) tshape H_at_idx H_pre => false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

-- lemma mvn_std (shape : S) : continuous (pdf.mvn_std shape) (pre.mvn_std shape)
-- | ⟦⟧ x 0     tshape H_at_idx H_pre => false.rec _ (util_list.at_idx_over H_at_idx (by tactic.dec_triv))

-- end cont

-- inductive op : Π (ishapes : List S) (oshape : S), Type
-- | mvn : ∀ (shape : S), op [shape, shape] shape
-- | mvn_std : ∀ (shape : S), op [] shape

-- namespace op

-- def pdf : Π {ishapes : List S} {oshape : S}, op ishapes oshape → pdf_function ishapes oshape
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.pdf.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.pdf.mvn_std shape

-- def run : Π {ishapes : List S} {oshape : S}, op ishapes oshape → rng_function ishapes oshape
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.run.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.run.mvn_std shape

-- def pre : Π {ishapes : List S} {oshape : S}, op ishapes oshape → precondition ishapes
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.pre.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.pre.mvn_std shape

-- def pdf_cdiff : Π {ishapes : List S} {oshape : S} (p : op ishapes oshape), pdf_cdiff p^.pdf p^.pre
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.pdiff.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.pdiff.mvn_std shape

-- def glogpdf : Π {ishapes : List S} {oshape : S}, op ishapes oshape → grad_logpdf ishapes oshape
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.glogpdf.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.glogpdf.mvn_std shape

-- def glogpdf_correct : Π {ishapes : List S} {oshape : S} (p : op ishapes oshape), grad_logpdf_correct p^.pdf p^.pre p^.glogpdf
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.glogpdf_correct.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.glogpdf_correct.mvn_std shape

-- def pdf_pos : Π {ishapes : List S} {oshape : S} (p : op ishapes oshape), pdf_positive p^.pdf p^.pre
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.pdf_pos.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.pdf_pos.mvn_std shape

-- def pdf_int1 : Π {ishapes : List S} {oshape : S} (p : op ishapes oshape), pdf_integrates_to_one p^.pdf p^.pre
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.pdf_int1.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.pdf_int1.mvn_std shape

-- def cont : Π {ishapes : List S} {oshape : S} (p : op ishapes oshape), continuous p^.pdf p^.pre
-- | [shape, .(shape)] .(shape) (mvn .(shape)) => _root_.certigrad.rand.cont.mvn shape
-- | []               shape (mvn_std .(shape)) => _root_.certigrad.rand.cont.mvn_std shape

-- end op
end rand

-- lemma mvn_pre {shape : S} (xs : Dvec T [shape, shape]) :
--   (rand.op.mvn shape)^.pre xs = (dvec.head2 xs > 0) := rfl

end certigrad
