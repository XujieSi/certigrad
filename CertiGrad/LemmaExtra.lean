/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous lemmas that depend on compute_grad_slow_correct.
-/
import CertiGrad.Predicates
import CertiGrad.Tcont
import CertiGrad.ExpectedValue
import CertiGrad.Lemmas
import CertiGrad.ComputeGradSlow

namespace certigrad
open List
open util_list
lemma is_nabla_gintegrable_of_gintegrable {costs : List ID} :
  Π (m : Env)
  (nodes : List Node)
  (tgt : Reference),
  wellFormedAt costs nodes m tgt →
  gradsExistAt nodes m tgt →
  pdfsExistAt nodes m →
  isGdifferentiable (λ m => ⟦sumCosts m costs⟧) tgt m nodes Dvec.head →
  canDifferentiateUnderIntegrals costs nodes m tgt →
  isGintegrable (λ m =>  ⟦computeGradSlow costs nodes m tgt⟧) m nodes Dvec.head → isNablaGintegrable (λ m =>⟦sumCosts m costs⟧) tgt m nodes Dvec.head
| m, [], tgt, H_wf, H_gs_exist, H_pdfs_exist, H_gdiff, H_diff_under_int, H_gint => trivial

| m, (⟨ref, parents, Operator.det op⟩ :: nodes), tgt, H_wf, H_gs_exist, H_pdfs_exist, H_gdiff, H_diff_under_int, H_gint => by
  let x : T ref.2 := op.f (env.getKs parents m)
  let next_inputs : Env := env.insert ref x m
  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
  have H_get_ks_next_inputs : env.getKs parents next_inputs = env.getKs parents m := by dsimp; rw [(env.get_ks_insert_diff H_ref_notin_parents)]
  have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref := wf_at_next H_wf
  dsimp [isGintegrable, computeGradSlow] at H_gint
  dsimp [isNablaGintegrable]
  constructor
  . apply is_nabla_gintegrable_of_gintegrable
    exact H_wfs.left
    exact H_gs_exist.left
    exact H_pdfs_exist
    exact H_gdiff.right.right.left
    exact H_diff_under_int.left
    exact ( (is_gintegrable_k_add _ _ _ _).mpr H_gint).left

  .
    intros idx H_idx_in_riota H_tgt_eq_dnth_idx
    have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
    have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
    have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx
    have H_f_pre : op.pre (env.getKs parents next_inputs) := Eq.recOn (Eq.symm H_get_ks_next_inputs) (H_gs_exist.right H_tgt_in_parents).left

    have H_grad_gint_ref : isGintegrable (λ m => ⟦computeGradSlow costs nodes m ref⟧) next_inputs nodes Dvec.head := by
      have H_op_called : isGintegrable (λ m => ⟦det.op.pb op (env.getKs parents m) (env.get ref m) (computeGradSlow costs nodes m ref) idx (tgt.snd)⟧)
                                      next_inputs nodes Dvec.head :=
      is_gintegrable_of_sumr_map (λ m idx => det.op.pb op (env.getKs parents m) (env.get ref m) (computeGradSlow costs nodes m ref) idx (tgt.snd))
                                        next_inputs nodes _ ((is_gintegrable_k_add _ _ _ _).mpr H_gint).right idx (List.mem_filter_of_mem H_idx_in_riota (decide_eq_true H_tgt_eq_dnth_idx))

      have H_op_called_swap : isGintegrable (λ m => ⟦det.op.pb op (env.getKs parents next_inputs) x (computeGradSlow costs nodes m ref) idx (tgt.snd)⟧)
                                          next_inputs nodes Dvec.head := by
            apply isGintegrableK_congr _ _ _ _ _ H_wfs.right.uids _ H_op_called
            intros m H_envs_match
            have H_parents_match : env.getKs parents m = env.getKs parents next_inputs := by
              apply env.get_ks_env_eq
              intros parent H_parent_in_parents
              apply H_envs_match
              apply env.hasKey_insert
              exact (H_wf.psInEnv.left parent H_parent_in_parents)
            have H_ref_matches : env.get ref m = x := by
              have H_env_has_key_ref : env.hasKey ref next_inputs := env.hasKey_insert_same _ _
              rw [H_envs_match ref H_env_has_key_ref, env.get_insert_same]
            simp only [H_parents_match, H_ref_matches]
      simp only [λ (m : Env) => op.pb_correct (env.getKs parents next_inputs) x (by rw [H_get_ks_next_inputs]) (computeGradSlow costs nodes m ref) H_tshape_at_idx H_f_pre] at H_op_called_swap
      exact (is_gintegrable_tmulT _ _ _ _).mpr H_op_called_swap


    apply is_nabla_gintegrable_of_gintegrable
    exact H_wfs.right
    exact (H_gs_exist.right H_tgt_in_parents).right
    exact H_pdfs_exist
    exact H_gdiff.right.right.right H_idx_in_riota H_tgt_eq_dnth_idx
    exact H_diff_under_int.right H_tgt_in_parents
    exact H_grad_gint_ref
| inputs, (⟨ref, parents, Operator.rand op⟩ :: nodes), tgt, H_wf, H_gs_exist, H_pdfs_exist, H_gdiff, H_diff_under_int, H_gint => by
    let θ := env.get tgt inputs
    let next_inputs := λ (y : T ref.2) => env.insert ref y inputs
    have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
    have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
    have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids

    have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by
      intro y
      exact wf_at_next H_wf

    dsimp [isGintegrable, computeGradSlow] at H_gint
    dsimp [isNablaGintegrable]

    have H_cgsc : ∀ x,
      E (graph.toDist (λ (m : Env) => ⟦computeGradSlow costs nodes m tgt⟧) (env.insert ref x inputs) nodes) Dvec.head =
      ∇ (λ (θ₀ : T tgt.2) =>
          E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧) (env.insert ref x (env.insert tgt θ₀ inputs)) nodes) Dvec.head) (env.get tgt inputs) := by
          intro x
          rw [← theorems.compute_grad_slow_correct (H_wfs x).left (H_gs_exist.right _) (H_pdfs_exist.right _) (H_gdiff.right.right _)
                                                _
                                                ((is_gintegrable_k_add _ _ _ _).mpr (H_gint.right x)).left
                                                (H_diff_under_int.right _)]

          unfold next_inputs
          simp only [(λ (θ₀ : T tgt.2) => env.insert_insert_flip θ₀ x inputs H_tgt_neq_ref), @env.get_insert_diff tgt ref x inputs H_tgt_neq_ref]
          exact is_nabla_gintegrable_of_gintegrable _ _ _ (H_wfs x).left (H_gs_exist.right _) (H_pdfs_exist.right _) (H_gdiff.right.right _)
                                          (H_diff_under_int.right _)
                                          ((is_gintegrable_k_add _ _ _ _).mpr (H_gint.right x)).left
    simp only [λ x => E.E_k_add _ _ _ _ ( (is_gintegrable_k_add _ _ _ _).mpr (H_gint.right x)).left
                              ((is_gintegrable_k_add _ _ _ _).mpr (H_gint.right x)).right] at H_gint
    simp only [H_cgsc] at H_gint

    constructor
    .
      apply ((T.is_integrable_add_middle _ _ _).mpr H_gint.left).left
    .
        unfold sumDownstreamCosts at H_gint

-- Scores
        have H_score_rw : ∀ y,
          map (λ (idx : ℕ) =>
                      E
                        (graph.toDist
                            (λ (m : Env) =>⟦sumCosts m costs⟧)
                            (env.insert ref y inputs)
                            nodes)
                        Dvec.head • ∇
                        (λ (θ₀ : T (tgt.snd)) => T.log (rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents inputs) idx) y))
                        (env.get tgt inputs))
                    (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))
        =
        map
            (λ (idx : ℕ)=>
              E
                (graph.toDist
                    (λ (m : Env) =>
                      ⟦sumDownstreamCosts nodes costs ref m • rand.op.glogpdf op (env.getKs parents m) (env.get ref m)
                            idx
                            (tgt.snd)⟧)
                    (env.insert ref y inputs)
                    nodes)
                Dvec.head)
            (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))) := by
            exact map_filter_expand_helper _ _ _ _ _ _ H_wf H_gs_exist

        have H_pull_E : ∀ y,
sumr
         (map
            (λ (idx : ℕ) =>
               E
                 (graph.toDist
                    (λ (m : Env) =>
                       ⟦sumDownstreamCosts nodes costs ref m • rand.op.glogpdf op (env.getKs parents m) (env.get ref m) idx (tgt.snd)⟧)
                    (env.insert ref y inputs)
                    nodes)
                 Dvec.head)
            (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))) =
        E (graph.toDist (λ (m : Env) =>
                    ⟦sumr (map (λ (idx : ℕ) => sumDownstreamCosts nodes costs ref m • rand.op.glogpdf op (env.getKs parents m) (env.get ref m) idx (tgt.snd))
                               (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))⟧)
                    (env.insert ref y inputs)
                    nodes)
                 Dvec.head := by
            intro y
            rw [← E.E_g_pull_out_of_sum _ _ _ _ (H_pdfs_exist.right y)]
            exact ((is_gintegrable_k_add _ _ _ _).mpr (H_gint.right y)).right

        constructor
        .
          simp only [H_score_rw]
          simp only [H_pull_E]
          apply ((T.is_integrable_add_middle _ _ _).mpr H_gint.left).right
        .
          intro y
          apply is_nabla_gintegrable_of_gintegrable
          exact (H_wfs y).left
          exact H_gs_exist.right y
          exact H_pdfs_exist.right y
          exact H_gdiff.right.right y
          exact H_diff_under_int.right y
          exact ((is_gintegrable_k_add _ _ _ _).mpr (H_gint.right y)).left

end certigrad
