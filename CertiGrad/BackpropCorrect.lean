/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Main functional correctness theorem for stochastic backpropagation.
-/
import CertiGrad.Util
import CertiGrad.ExpectedValue
import CertiGrad.Reference
import CertiGrad.Graph
import CertiGrad.ComputeGrad
import CertiGrad.Predicates
import CertiGrad.Estimators
import CertiGrad.Env
import CertiGrad.Dvec
import CertiGrad.ComputeGradSlow
import CertiGrad.MemorizeCorrect
import CertiGrad.Lemmas
import CertiGrad.LemmaExtra

namespace certigrad
open tactic List theorems
open util_list
theorem backprop_correct {costs : List ID} :
  ∀ {nodes : List Node} (inputs : Env) (tgts : List Reference),
  ∀ {tgt : Reference} {idx : ℕ}, at_idx tgts idx tgt →
  Nodup (tgts ++ map Node.ref nodes) →
  wellFormedAt costs nodes inputs tgt →
  gradsExistAt nodes inputs tgt →
  pdfsExistAt nodes inputs →
  isGintegrable (λ m => ⟦computeGradSlow costs nodes m tgt⟧) inputs nodes Dvec.head →
  canDifferentiateUnderIntegrals costs nodes inputs tgt →

  ∇ (λ θ₀ => E (graph.toDist (λ m => ⟦sumCosts m costs⟧) (env.insert tgt θ₀ inputs) nodes) Dvec.head) (env.get tgt inputs)
  =
  E (graph.toDist (λ m => backprop costs nodes m tgts) inputs nodes) (λ dict => dvec.get tgt.2 _ dict idx) := by

    intro (nodes : List Node) (inputs : Env) (tgts : List Reference)
      (tgt : Reference) (idx : ℕ) (H_at_idx : at_idx tgts idx tgt)
      (H_nd : Nodup (tgts ++ map Node.ref nodes))
      (H_wf : wellFormedAt costs nodes inputs tgt)
      (H_gs_exist : gradsExistAt nodes inputs tgt)
      (H_pdfs_exist : pdfsExistAt nodes inputs)
      (H_grad_gint : isGintegrable (λ m => ⟦computeGradSlow costs nodes m tgt⟧) inputs nodes Dvec.head)
      (H_diff_under_int : canDifferentiateUnderIntegrals costs nodes inputs tgt)

    have H_gdiff : isGdifferentiable (λ m => ⟦sumCosts m costs⟧) tgt inputs nodes Dvec.head :=
      is_gdifferentiable_of_pre _ _ _ H_wf H_gs_exist H_pdfs_exist H_diff_under_int
    have H_nabla_gint : isNablaGintegrable (λ m => ⟦sumCosts m costs⟧) tgt inputs nodes Dvec.head :=
      is_nabla_gintegrable_of_gintegrable _ _ _ H_wf H_gs_exist H_pdfs_exist H_gdiff H_diff_under_int H_grad_gint

    rw [compute_grad_slow_correct H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int]
    rw [E.E_move_fn_to_continuation _ _ _ (λ dict => dvec.get tgt.2 _ dict idx)]
    unfold backprop
    dsimp
    simp only [(λ m => tvec.get_from_env H_at_idx m), (λ m => memoize_correct costs nodes m H_at_idx H_nd)]


end certigrad
