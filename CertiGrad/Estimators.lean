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
  (H_tgt_in_inputs : env.hasKey tgt m)
  (op : rand.op parents.p2 oshape)
  (H_op_pre : op.pre (env.getKs parents m))
  (f : T oshape → T tgt.2 → TReal)
  (θ : T tgt.2) (H_θ : θ = env.get tgt m)
  (H_f_diff : ∀ (x : T oshape), T.is_cdifferentiable (f x) θ)
  (H_f_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T oshape) => rand.op.pdf op (env.getKs parents (env.insert tgt θ m)) x • f x θ₀) θ)
  (H_f_grad_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T oshape) => ∇ (λ (θ₁ : T (tgt.snd)) => rand.op.pdf op (env.getKs parents (env.insert tgt θ m)) x • f x θ₁) θ₀) θ)

  (H_d'_pdf_diff : ∀ {idx : ℕ}, at_idx parents idx tgt →
       ∀ (v : T oshape), T.is_cdifferentiable (λ (x₀ : T (tgt.snd))=> rand.op.pdf op (dvec.update_at x₀ (env.getKs parents (env.insert tgt θ m)) idx) v) θ)

  (H_d'_uint : ∀ {idx : ℕ}, at_idx parents idx tgt →
          T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T oshape)=>
            rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x • f x θ) θ)
  (H_d'_grad_uint : ∀ {idx : ℕ}, at_idx parents idx tgt →
            T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T oshape) =>
               ∇ (λ (θ₀ : T (tgt.snd)) => rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x • f x θ) θ₀) θ)
  :
  let g : Dvec T parents.p2 → T tgt.2 → TReal := (λ (xs : Dvec T parents.p2) (θ : T tgt.2) => E (sprog.prim op xs) (λ (y : Dvec T [oshape]) => f y.head θ))

  ∀ (H_diff₁ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd))=> g (env.getKs parents (env.insert tgt θ m)) θ₀) θ)
  (H_diff₂ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd))=>sumr (map (λ (idx : ℕ) => g (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) θ)
                                  (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))) θ)

  (H_int₁ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ m))) (λ (x : Dvec T [oshape]) => ∇ (f x.head) θ))
  (H_int₂ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
                (λ (x : Dvec T [oshape])=> sumr (map (λ (idx : ℕ) => f x.head θ • ∇ (λ (θ₀ : T (tgt.snd)) => T.log (rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) (Dvec.head x))) θ) (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))),

∇ (λ θ₀ => E (sprog.prim op (env.getKs parents (env.insert tgt θ₀ m))) (λ x₀ => f x₀.head θ₀)) θ
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (λ x₀ => ∇ (λ θ₀ => f x₀.head θ₀) θ
  + sumr (map (λ idx =>
        f x₀.head θ • ∇ (λ θ₀ => T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x₀.head)) θ)
       (filter (λ idx => tgt = dnth parents idx) (riota $ length parents)))) :=
let g : Dvec T parents.p2 → T tgt.2 → TReal := (λ xs θ => E (sprog.prim op xs) (λ y => f y.head θ))
fun H_diff₁ H_diff₂ H_int₁ H_int₂ =>

have H_term₁ :
∇ (λ (θ₀ : T tgt.2) =>
  E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
    (λ (y : Dvec T [oshape]) => f y.head θ₀))
   θ
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (λ (x₀ : Dvec T [oshape]) => ∇ (λ (θ₀ : T tgt.2) => f x₀.head θ₀) θ) :=
  pathwise _ _ _ H_f_diff H_f_uint H_f_grad_uint

suffices H_suffices :
sumr (map (λ (idx : ℕ) =>
            ∇ (λ (θ₀ : T tgt.2) =>
                E (sprog.prim op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx))
                  (λ (y : Dvec T [oshape]) => f y.head θ))
              θ)
         (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (λ (x₀ : Dvec T [oshape])=>
    sumr (map (λ (idx : ℕ) =>
               f x₀.head θ •  ∇ (λ (θ₀ : T tgt.2) => T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) x₀.head)) θ)
             (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))
             by
              rw [H_term₁]
              apply congr_arg
              exact H_suffices

suffices H_suffices :
sumr (map (λ (idx : ℕ) =>
            ∇ (λ (θ₀ : T tgt.2) => E (sprog.prim op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx))
                  (λ (y : Dvec T [oshape]) => f y.head θ))
              θ)
         (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))
=
sumr (map (λ (x : ℕ) =>
           E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
             (λ (y : Dvec T [oshape]) =>
               f y.head θ •  ∇ (λ (θ₀ : T tgt.2) =>
                            T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) x) y.head)) θ)
         (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))
         by
          rw [← E.E_pull_out_of_sum _ _ _ _ _ H_int₂]
          exact H_suffices
          rw [H_θ]
          rw [env.insert_get_same H_tgt_in_inputs, exact H_op_pre]

suffices H_suffices :
∀ (idx : ℕ), idx ∈ riota (length parents) → tgt = dnth parents idx →
∇ (λ (θ₀ : T tgt.2) =>
    E (sprog.prim op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx))
      (λ (y : Dvec T [oshape]) => f y.head θ))
  θ
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (λ (y : Dvec T [oshape]) =>
      f y.head θ • ∇ (λ (θ₀ : T tgt.2)=>
                 T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) y.head)) θ)
  by
    apply congr_arg
    apply map_filter_congr
    exact H_suffices

    intro (idx : ℕ) (H_idx_in_riota : idx ∈ riota (length parents)) (H_tgt_eq_dnth_idx : tgt = dnth parents idx)

    let mk_args : T tgt.2 → Dvec T parents.p2 :=
      (λ (v : T tgt.2) =>
         dvec.update_at v (env.getKs parents (env.insert tgt θ m)) idx)

    have
    ∇ (λ (θ₀ : T tgt.2) =>
        E (sprog.prim op (mk_args θ₀))
          (λ (y : Dvec T [oshape]) => f y.head θ))
      θ
    =
    E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
        (λ (y : Dvec T [oshape]) =>
          f y.head θ • ∇ (λ (θ₀ : T tgt.2) =>
                    T.log (op.pdf (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ m)) idx) y.head)) θ) := by

      have H_idx_lt_len_parents : idx < length parents := by
        apply in_riota_lt H_idx_in_riota

      have H_tgt_at_idx : at_idx parents idx tgt := by
        apply ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
      have H_tgt_in_parents : tgt ∈ parents := by
        apply mem_of_at_idx H_tgt_at_idx

      have H_op'_pre : op^.pre (mk_args θ) := by
        dsimp
        rw [H_θ]
        rw [env.insert_get_same H_tgt_in_inputs]
        rw [env.dvec_update_at_env _ H_tgt_at_idx]
        exact H_op_pre

suffices H_suffices :
E (sprog.prim op (dvec.update_at θ (env.getKs parents (env.insert tgt θ m)) idx))
  (λ (x₀ : Dvec T [oshape]) =>
     f x₀.head θ • ∇ (λ (θ₀ : T tgt.2) => T.log (op.pdf (mk_args θ₀) x₀.head)) θ)
=
E (sprog.prim op (env.getKs parents (env.insert tgt θ m)))
  (λ (y : Dvec T [oshape]) =>
     f y.head θ • ∇ (λ (θ₀ : T tgt.2) => T.log (op.pdf (mk_args θ₀) y.head)) θ)
  by
    rw [score op mk_args θ H_op'_pre (λ y => f y θ) (H_d'_pdf_diff H_tgt_at_idx) (H_d'_uint H_tgt_at_idx) (H_d'_grad_uint H_tgt_at_idx)]
    exact H_suffices

have H_remove_dvec_update : dvec.update_at θ (env.getKs parents (env.insert tgt θ m)) idx = env.getKs parents (env.insert tgt θ m) := by
  rw [H_θ, env.insert_get_same H_tgt_in_inputs]
  rw [env.dvec_update_at_env m ⟨H_idx_lt_len_parents, H_tgt_eq_dnth_idx⟩]

by rw [H_remove_dvec_update]

end Estimators
end certigrad
