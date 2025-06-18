/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Estimators.
-/
import CertiGrad.Util
import CertiGrad.Tensor
import CertiGrad.Id
import CertiGrad.Graph
import CertiGrad.ExpectedValue
import CertiGrad.Tfacts
import CertiGrad.Dvec

namespace certigrad
namespace Estimators
open List

lemma score {ishapes : List S} {oshape tshape : S} (op : rand.op ishapes oshape) (args : T tshape → Dvec T ishapes) (θ : T tshape)
  (H_op_pre : op.pre (args θ))
  (f : T oshape → TReal)
  (H_pdf_diff : ∀ (v : T oshape), T.is_cdifferentiable (λ x₀ => op.pdf (args x₀) v) θ)
  (H_f_uint : T.is_uniformly_integrable_around (λ θ₀ x => rand.op.pdf op (args θ₀) x • f x) θ)
  (H_f_grad_uint : T.is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => rand.op.pdf op (args θ₁) x • f x) θ₀) θ) :
  ∇ (λ θ₀ => E (sprog.prim op (args θ₀)) (λ x => f x.head)) θ
  =
  E (sprog.prim op (args θ)) (λ x₀ => f x₀.head • ∇ (λ θ₀ => T.log (op.pdf (args θ₀) x₀.head)) θ) :=
by
  have H_pdf_pos : ∀ x, op.pdf (args θ) x > 0 := rand.op.pdf_pos op (args θ) H_op_pre

  have H_f_diff : ∀ x, T.is_cdifferentiable (λ θ₀ => rand.op.pdf op (args θ₀) x • f x) θ := by
    intro x
    exact (T.is_cdifferentiable_fscale _ _ _).mp (H_pdf_diff x)

  unfold E T.dintegral
  erw [T.grad_integral _ _ H_f_diff H_f_uint H_f_grad_uint]

  apply congr_arg
  apply funext
  intro x
  simp
  rw [T.grad_log_f θ _ (H_pdf_pos x)]
  erw [← T.smul_group, ← T.smul_group]
  rw [mul_assoc, mul_comm (f x), ← mul_assoc]
  rw [(T.mul_inv_cancel (H_pdf_pos x))]
  rw [one_mul]
  rw [←T.grad_scale_f]
  apply T.grad_congr
  intro y
  rw [T.smul_comm]

lemma pathwise {ishapes : List S} {oshape tshape : S} {f : T oshape → T tshape → TReal}
  (op : rand.op ishapes oshape) (args : Dvec T ishapes) (θ : T tshape)
  (H_f_diff : ∀ (x : T oshape), T.is_cdifferentiable (f x) θ)
  (H_uint : T.is_uniformly_integrable_around (λ θ₀ x => rand.op.pdf op args x • f x θ₀) θ)
  (H_grad_uint : T.is_uniformly_integrable_around (λ θ₀ x => ∇ (λ θ₁ => rand.op.pdf op args x • f x θ₁) θ₀) θ) :
  ∇ (λ θ₀ => E (sprog.prim op args) (λ x => f x.head θ₀)) θ
  =
  E (sprog.prim op args) (λ x => ∇ (λ θ₀ => f x.head θ₀) θ) :=
by
  have H_pdf_f_diff : ∀ x, T.is_cdifferentiable (λ θ₀ => op.pdf args x • f x θ₀) θ := by
    intro x
    exact (T.is_cdifferentiable_scale_f _ _ _).mp (H_f_diff x)
  unfold E T.dintegral
  erw [T.grad_integral _ _ H_pdf_f_diff H_uint H_grad_uint]
  apply congr_arg
  apply funext
  intro x
  apply T.grad_scale_f

open util_list




lemma hybrid_general {parents : List Reference} {tgt : Reference} {oshape : S} (m : Env)
    (h_tgt_in_inputs : env.hasKey tgt m)
    (op : rand.op parents.p2 oshape)
    (h_op_pre : op.pre (env.getKs parents m))
    (f : T oshape → T tgt.2 → TReal)
    (θ : T tgt.2) (h_θ : θ = env.get tgt m)
    (h_f_diff : ∀ (x : T oshape), T.is_cdifferentiable (f x) θ)
    (h_f_uint : T.is_uniformly_integrable_around (fun (θ₀ : T (tgt.snd)) (x : T oshape) => rand.op.pdf op (env.getKs parents (env.insert tgt θ m)) x • f x θ₀) θ)
    (h_f_grad_uint : T.is_uniformly_integrable_around (fun (θ₀ : T (tgt.snd)) (x : T oshape) => ∇ (fun (θ₁ : T (tgt.snd)) => rand.op.pdf op (env.getKs parents (env.insert tgt θ m)) x • f x θ₁) θ₀) θ)
    (h_d'_pdf_diff : ∀ {idx : ℕ}, at_idx parents idx tgt →
           ∀ (v : T oshape), T.is_cdifferentiable (fun (x₀ : T (tgt.snd)) => rand.op.pdf op (dvec.update_at x₀ (env.getKs parents (env.insert tgt θ m)) idx) v) θ)
    (h_d'_uint : ∀ {idx : ℕ}, at_idx parents idx tgt →
                    T.is_uniformly_integrable_around (fun (θ₀ : T (tgt.snd)) (x : T oshape)=>
                        rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x • f x θ) θ)
    (h_d'_grad_uint : ∀ {idx : ℕ}, at_idx parents idx tgt →
                        T.is_uniformly_integrable_around (fun (θ₀ : T (tgt.snd)) (x : T oshape) =>
                             ∇ (fun (θ₀ : T (tgt.snd)) => rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x • f x θ) θ₀) θ)
    :
    let g : Dvec T parents.p2 → T tgt.2 → TReal := (fun (xs : Dvec T parents.p2) (θ : T tgt.2) => E (sprog.prim op xs) (fun (y : Dvec T [oshape]) => f y.head θ))
    ∀ (h_diff₁ : T.is_cdifferentiable (fun (θ₀ : T (tgt.snd)) => g (env.getKs parents (env.insert tgt θ m)) θ₀) θ)
    (h_diff₂ : T.is_cdifferentiable (fun (θ₀ : T (tgt.snd)) => sumr (map (fun (idx : ℕ) => g (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) θ)
                                                                    (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))) θ)
    (h_int₁ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ m))) (fun (x : Dvec T [oshape]) => ∇ (f x.head) θ))
    (h_int₂ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
                              (fun (x : Dvec T [oshape]) => sumr (map (fun (idx : ℕ) => f x.head θ • ∇ (fun (θ₀ : T (tgt.snd)) => T.log (rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) (Dvec.head x))) θ) (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))),
∇ (fun θ₀ => E (sprog.prim op (env.getKs parents (env.insert tgt θ₀ m))) (fun x₀ => f x₀.head θ₀)) θ
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (fun x₀ => ∇ (fun θ₀ => f x₀.head θ₀) θ
  + sumr (map (fun (idx : ℕ) =>
                f x₀.head θ • ∇ (fun θ₀ => T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x₀.head)) θ)
             (filter (fun idx => tgt = dnth parents idx) (riota $ length parents)))) := by

  -- let g : Dvec T parents.p2 → T tgt.2 → TReal := (λ (xs : Dvec T parents.p2) (θ : T tgt.2) => E (sprog.prim op xs) (λ (y : Dvec T [oshape]) => f y.head θ))
  let g : Dvec T parents.p2 → T tgt.2 → TReal := (fun (xs : Dvec T parents.p2) (θ : T tgt.2) => E (sprog.prim op xs) (fun (y : Dvec T [oshape]) => f y.head θ))
  intro _ h_diff₁ h_diff₂ h_int₁ h_int₂
  set ks' : Dvec T parents.p2 := env.getKs parents (env.insert tgt θ m)
  set ksDist := sprog.prim op ks'

  show
    ∇ (λ (θ₀ : T tgt.2) => g (env.getKs parents (env.insert tgt θ₀ m)) θ₀) θ = E ksDist
    (λ (x₀ : Dvec T [oshape]) => ∇ (λ (θ₀ : T tgt.2) => f x₀.head θ₀) θ
    + sumr (map (λ (idx : ℕ) =>
                  f x₀.head θ • ∇ (λ (θ₀ : T tgt.2) => T.log (op.pdf (dvec.update_at θ₀ ks' idx) x₀.head)) θ)
               (filter (fun idx => tgt = dnth parents idx) (riota $ length parents))))
  suffices h_suffices :
        ∇ (λ (θ₀ : T tgt.2) => E ksDist (λ (x₀ : Dvec T [oshape]) => f x₀.head θ₀)) θ
      +
      sumr (map (λ (idx : ℕ) =>
                  ∇ (λ (θ₀ : T tgt.2) =>
                      E (sprog.prim op (dvec.update_at θ₀ ks' idx))
                        (λ (y : Dvec T [oshape]) => f y.head θ))
                    θ)
              (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))
      = E ksDist (λ (x₀ : Dvec T [oshape]) => ∇ (f x₀.head) θ) +
      E ksDist
        (λ (x₀ : Dvec T [oshape]) =>
          sumr (map (fun (idx : ℕ) =>
                    f x₀.head θ •  ∇ (fun (θ₀ : T tgt.2) =>
                    T.log (op.pdf (dvec.update_at θ₀ ks' idx) x₀.head)) θ)
                  (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))
                  by
                    rw [T.multiple_args_general]
                    simp only [g]
                    rw [E.E_add _ _ _ h_int₁ h_int₂]
                    exact h_suffices
                    exact h_diff₁
                    exact h_diff₂

  have h_term₁ :
    ∇ (fun (θ₀ : T tgt.2) =>
        E (sprog.prim op ks')
          (fun (y : Dvec T [oshape]) => f y.head θ₀))
      θ
    =
    E (sprog.prim op ks')
      (fun (x₀ : Dvec T [oshape]) => ∇ (fun (θ₀ : T tgt.2) => f x₀.head θ₀) θ) := by
    apply pathwise _ _ _ h_f_diff h_f_uint h_f_grad_uint

  suffices h_suffices :
    sumr (map (fun (idx : ℕ) =>
                ∇ (fun (θ₀ : T tgt.2) =>
                    E (sprog.prim op (dvec.update_at θ₀ ks' idx))
                      (fun (y : Dvec T [oshape]) => f y.head θ))
                  θ)
             (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))
    =
    E (sprog.prim op ks')
      (fun (x₀ : Dvec T [oshape]) =>
        sumr (map (fun (idx : ℕ) =>
                   f x₀.head θ • ∇ (fun (θ₀ : T tgt.2) => T.log (op.pdf (dvec.update_at θ₀ ks' idx) x₀.head)) θ)
                 (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))) by
      rw [h_term₁]
      apply congr_arg
      exact h_suffices

  suffices h_suffices :
    sumr (map (fun (idx : ℕ) =>
                ∇ (fun (θ₀ : T tgt.2) =>
                    E (sprog.prim op (dvec.update_at θ₀ ks' idx))
                      (fun (y : Dvec T [oshape]) => f y.head θ))
                  θ)
             (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))
    =
    sumr (map (fun (x : ℕ) =>
               E (sprog.prim op ks')
                 (fun (y : Dvec T [oshape]) =>
                   f y.head θ •  ∇ (fun (θ₀ : T tgt.2) =>
                                T.log (op.pdf (dvec.update_at θ₀ ks' x) y.head)) θ))
             (filter (fun (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))  by
        rw [← E.E_pull_out_of_sum _ _ _ _ _ h_int₂]
        exact h_suffices
        unfold ks'
        rw [h_θ, env.insert_get_same h_tgt_in_inputs]
        exact h_op_pre

  suffices h_suffices :
    ∀ (idx : ℕ), idx ∈ riota (length parents) → tgt = dnth parents idx →
    ∇ (fun (θ₀ : T tgt.2) =>
        E (sprog.prim op (dvec.update_at θ₀ ks' idx))
          (fun (y : Dvec T [oshape]) => f y.head θ))
      θ
    =
    E (sprog.prim op ks')
      (fun (y : Dvec T [oshape]) =>
          f y.head θ • ∇ (fun (θ₀ : T tgt.2) =>
                     T.log (op.pdf (dvec.update_at θ₀ ks' idx) y.head)) θ) by
    apply congr_arg
    apply map_filter_congr
    exact h_suffices

  intro (idx : ℕ)
        (h_idx_in_riota : idx ∈ riota (length parents))
        (h_tgt_eq_dnth_idx : tgt = dnth parents idx)

  let mk_args : T tgt.2 → Dvec T parents.p2 :=
        (fun (v : T tgt.2) =>
           dvec.update_at v ks' idx)

  show
    ∇ (λ (θ₀ : T tgt.2) =>
        E (sprog.prim op (mk_args θ₀))
          (λ (y : Dvec T [oshape]) => f y.head θ))
      θ
    =
    E (sprog.prim op ks')
      (λ (y : Dvec T [oshape]) =>
          f y.head θ • ∇ (λ (θ₀ : T tgt.2) =>
                     T.log (op.pdf (dvec.update_at θ₀ ks' idx) y.head)) θ)
  have h_idx_lt_len_parents : idx < length parents := in_riota_lt h_idx_in_riota
  have h_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt h_idx_in_riota, h_tgt_eq_dnth_idx⟩
  have h_tgt_in_parents : tgt ∈ parents := mem_of_at_idx h_tgt_at_idx

  have h_op'_pre : op.pre (mk_args θ) := by
    dsimp
    simp only [mk_args, ks']
    simp at h_tgt_at_idx
    -- unfold ks'
    rw [h_θ, env.insert_get_same h_tgt_in_inputs, env.dvec_update_at_env _ h_tgt_at_idx]
    exact h_op_pre

    -- -- Apply the `score` lemma.
  suffices h_suffices :
    E (sprog.prim op (dvec.update_at θ (env.getKs parents (env.insert tgt θ m)) idx))
      (fun (x₀ : Dvec T [oshape]) =>
          f x₀.head θ • ∇ (fun (θ₀ : T tgt.2) => T.log (op.pdf (mk_args θ₀) x₀.head)) θ)
    =
    E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
      (fun (y : Dvec T [oshape]) =>
          f y.head θ •  ∇ (fun (θ₀ : T tgt.2) => T.log (op.pdf (mk_args θ₀) y.head)) θ) by
    rw [(score op mk_args θ h_op'_pre (fun y => f y θ) (h_d'_pdf_diff h_tgt_at_idx) (h_d'_uint h_tgt_at_idx) (h_d'_grad_uint h_tgt_at_idx))]
    exact h_suffices

    -- Simplify the `dvec.update_at` term when `θ₀` is `θ`.
  have h_remove_dvec_update : dvec.update_at θ (env.getKs parents (env.insert tgt θ m)) idx = env.getKs parents (env.insert tgt θ m) := by
    rw [h_θ, env.insert_get_same h_tgt_in_inputs]
    rw [env.dvec_update_at_env m ⟨h_idx_lt_len_parents, h_tgt_eq_dnth_idx⟩]
  rw [h_remove_dvec_update]
end Estimators
end certigrad
