/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Proof that the simple, non-memoized version of stochastic backpropagation
is correct.
-/
import CertiGrad.Graph
import CertiGrad.Estimators
import CertiGrad.Predicates
import CertiGrad.ComputeGrad
import CertiGrad.Lemmas
import CertiGrad.Tgrads
import CertiGrad.Tactics

namespace certigrad
namespace theorems
open List
open util_list
lemma compute_grad_slow_correct {costs : List ID} :
  ∀ {nodes : List Node} {inputs : Env} {tgt : Reference},
  wellFormedAt costs nodes inputs tgt →
  gradsExistAt nodes inputs tgt →
  pdfsExistAt nodes inputs →
  isGdifferentiable (λ m => ⟦sumCosts m costs⟧) tgt inputs nodes Dvec.head →
  isNablaGintegrable (λ m => ⟦sumCosts m costs⟧) tgt inputs nodes Dvec.head →
  isGintegrable (λ m => ⟦computeGradSlow costs nodes m tgt⟧) inputs nodes Dvec.head →
  canDifferentiateUnderIntegrals costs nodes inputs tgt →
  ∇ (λ θ₀ => E (graph.toDist (λ m => ⟦sumCosts m costs⟧) (env.insert tgt θ₀ inputs) nodes) Dvec.head) (env.get tgt inputs)
  =
  E (graph.toDist (λ m => ⟦computeGradSlow costs nodes m tgt⟧) inputs nodes) Dvec.head
| [], inputs, tgt => by
    intro H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int
    simp only [graph.toDist, E.E_ret]
    unfold Dvec.head computeGradSlow sumCosts
    rw [T.grad_sumr _ _ _ (sum_costs_differentiable costs tgt inputs)]
    apply congr_arg
    apply map_congr_fn_pred
    intros cost H_cost_in_costs
    have H_em : tgt = (cost, []) ∨ tgt ≠ (cost, []) := Decidable.em _
    cases H_em
    case h.inl H_eq =>
      rw [H_eq]
      simp [env.get_insert_same, T.grad_id]
    case h.inr H_neq =>
      simp [λ (x : T tgt.2) => env.get_insert_diff x inputs (Ne.symm H_neq), H_neq, T.grad_const]

| (⟨ref, parents, Operator.det op⟩ :: nodes), inputs, tgt => by
      intro H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int
      let θ := env.get tgt inputs
      let x := op.f (env.getKs parents inputs)
      let next_inputs := env.insert ref x inputs

      -- 0. Collect useful helpers
      have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := by simp

      have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids

      have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids

      have H_get_ks_next_inputs : env.getKs parents next_inputs = env.getKs parents inputs :=
        by
           unfold next_inputs
           simp [env.get_ks_insert_diff H_ref_notin_parents]

      have H_get_ref_next : env.get ref next_inputs = op.f (env.getKs parents inputs) := by
          unfold next_inputs
          -- dsimp
          sorry
          -- simp [env.get_insert_same]




      have H_can_insert : env.get tgt next_inputs = env.get tgt inputs := by
        unfold next_inputs
        simp [env.get_insert_diff _ _ H_tgt_neq_ref]

      have H_insert_next : ∀ (y : T ref.2), env.insert ref y inputs = env.insert ref y next_inputs := by
        intro y
        unfold next_inputs
        simp [env.insert_insert_same]

      have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref := by
        unfold next_inputs
        simp [wf_at_next H_wf]

      have H_gs_exist_tgt : gradsExistAt nodes next_inputs tgt := by
        unfold next_inputs
        -- gradsExistAt
        exact H_gs_exist.left

      have H_pdfs_exist_next : pdfsExistAt nodes next_inputs := H_pdfs_exist

      have H_grad_gint_tgt : isGintegrable (λ m => ⟦computeGradSlow costs nodes m tgt⟧) next_inputs nodes Dvec.head := by
         exact ((is_gintegrable_k_add _ _ _ _).mpr H_grad_gint).left

      have H_nabla_gint_tgt : isNablaGintegrable (λ m => ⟦sumCosts m costs⟧) tgt next_inputs nodes Dvec.head := by
        exact H_nabla_gint.left

      have H_grad_gint₁ : isGintegrable (λ (m : Env) => ⟦computeGradSlow costs nodes m tgt⟧)
                                  (env.insert ref (op.f (env.getKs parents inputs)) inputs)
                                  nodes
                                  Dvec.head := by
        unfold isGintegrable computeGradSlow at H_grad_gint
        exact ((is_gintegrable_k_add _ _ _ _).mpr H_grad_gint).left

      have H_grad_gint₂ : isGintegrable
          (λ (m : Env) =>
            ⟦sumr
              (map
                  (λ (idx : ℕ)=>
                    det.op.pb op (env.getKs parents m) (env.get ref m) (computeGradSlow costs nodes m ref) idx (tgt.snd))
                  (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))⟧)
          (env.insert ref (det.op.f op (env.getKs parents inputs)) inputs)
          nodes
          Dvec.head := by
        unfold isGintegrable computeGradSlow at H_grad_gint
        exact ((is_gintegrable_k_add _ _ _ _).mpr H_grad_gint).right

      dsimp only [graph.toDist, Operator.toDist]
      unfold computeGradSlow
      simp only [E.E_bind, E.E_ret,Dvec.head]
      rw [E.E_k_add _ _ _ _ H_grad_gint₁ H_grad_gint₂]
      rw [E.E_k_sum_map _ _ nodes _ H_pdfs_exist H_grad_gint₂]


      -- -- 1. Use the general estimator on the LHS
      let g := (λ (v : Dvec T parents.p2) (θ : T tgt.2) => E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧) (env.insert ref (op.f v) (env.insert tgt θ inputs)) nodes) Dvec.head)
      have H_diff₁ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)) => g (env.getKs parents (env.insert tgt θ inputs)) θ₀) θ := by
        exact H_gdiff.left

      have H_diff₂ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)) => sumr (map (λ (idx : ℕ) => g (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx) θ)
                                                                      (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))))
                                            θ := by
        exact H_gdiff.right.left

      rw [(T.multiple_args_general parents tgt inputs g θ H_diff₁ H_diff₂)]

      rw [env.insert_get_same H_wf.m_contains_tgt]


      have H_almost_tgt := (Eq.symm (compute_grad_slow_correct H_wfs.left H_gs_exist_tgt H_pdfs_exist_next H_gdiff.right.right.left H_nabla_gint_tgt H_grad_gint_tgt H_diff_under_int.left))
      rw [env.get_insert_diff _ _ H_tgt_neq_ref] at H_almost_tgt
      erw [H_almost_tgt]
      -- dsimp
      simp only [next_inputs]
      simp [λ (θ : T tgt.2) => env.insert_insert_flip x θ inputs (Ne.symm H_tgt_neq_ref)]
      apply congr_arg

    -- 3. Time for the second term: get rid of sum and use map_filter_congr
    apply (congr_arg sumr),
    apply map_filter_congr,
    intros idx H_idx_in_riota H_tgt_dnth_parents_idx,
    assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩,
    assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
    assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

    -- 4. Put the LHS in terms of T.tmulT
    rw (T.grad_chain_rule (λ (θ : T tgt.2), det.op.f op (dvec.update_at θ (env.get_ks parents inputs) idx))
                          (λ (x : T ref.2), E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
                                                            (env.insert ref x inputs)
                                                            nodes)
                                              dvec.head))

      -- rw [env.insert_get_same H_wf.m_contains_tgt]

      -- pose H_almost_tgt := (eq.symm (compute_grad_slow_correct H_wfs^.left H_gs_exist_tgt H_pdfs_exist_next H_gdiff^.right^.right^.left H_nabla_gint_tgt H_grad_gint_tgt H_diff_under_int^.left)),
      -- rw (env.get_insert_diff _ _ H_tgt_neq_ref) at H_almost_tgt,
      -- erw H_almost_tgt,
      -- dsimp,
      -- simp [λ (θ : T tgt.2), env.insert_insert_flip x θ inputs (ne.symm H_tgt_neq_ref)],
      -- apply congr_arg,

      -- -- 3. Time for the second term: get rid of sum and use map_filter_congr
      -- apply (congr_arg sumr),
      -- apply map_filter_congr,
      -- intros idx H_idx_in_riota H_tgt_dnth_parents_idx,
      -- assertv H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩,
      -- assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
      -- assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

      -- -- 4. Put the LHS in terms of T.tmulT
      -- rw (T.grad_chain_rule (λ (θ : T tgt.2), det.op.f op (dvec.update_at θ (env.get_ks parents inputs) idx))
      --                       (λ (x : T ref.2), E (graph.to_dist (λ (m : env), ⟦sum_costs m costs⟧)
      --                                                         (env.insert ref x inputs)
      --                                                         nodes)
      --                                           dvec.head)),

      -- -- 5. Replace `m` with `inputs`/`next_inputs` so that we can use `pb_correct`
      -- assert H_swap_m_for_inputs :
      -- graph.to_dist (λ (m : env),
      --                   ⟦op^.pb (env.get_ks parents m)
      --                           (env.get ref m)
      --                           (compute_grad_slow costs nodes m ref)
      --                           idx
      --                           tgt.2⟧)
      --                 next_inputs
      --                 nodes
      -- =
      -- (graph.to_dist (λ (m : env),
      --                     ⟦op^.pb (env.get_ks parents next_inputs)
      --                             x
      --                             (compute_grad_slow costs nodes m ref)
      --                             idx
      --                             tgt.2⟧)
      --                 next_inputs
      --                 nodes),
      -- begin
      --   apply graph.to_dist_congr,
      --   exact H_wfs^.right^.uids,
      --   dsimp,
      --   intros m H_envs_match,
      --   apply dvec.singleton_congr,
      --   assert H_parents_match : env.get_ks parents m = env.get_ks parents next_inputs,
      --   begin
      --     apply env.get_ks_env_eq,
      --     intros parent H_parent_in_parents,
      --     apply H_envs_match,
      --     apply env.has_key_insert,
      --     exact (H_wf^.ps_in_env^.left parent H_parent_in_parents)
      --   end,
      --   assert H_ref_matches : env.get ref m = x,
      --   begin
      --     assertv H_env_has_key_ref : env.has_key ref next_inputs := env.has_key_insert_same _ _,
      --     rw [H_envs_match ref H_env_has_key_ref, env.get_insert_same]
      --   end,
      --   simp [H_parents_match, H_ref_matches],
      -- end,

      -- rw H_swap_m_for_inputs,
      -- clear H_swap_m_for_inputs,

      -- -- 6. Use pb_correct
      -- assertv H_f_pre : op^.pre (env.get_ks parents next_inputs) := eq.rec_on (eq.symm H_get_ks_next_inputs) (H_gs_exist^.right H_tgt_in_parents)^.left,
      -- simp [λ (m : env), op^.pb_correct (env.get_ks parents next_inputs) x (by rw H_get_ks_next_inputs) (compute_grad_slow costs nodes m ref) H_tshape_at_idx H_f_pre],

      -- -- 7. Push E over tmulT and cancel the first terms
      -- simp [E.E_k_tmulT, H_get_ks_next_inputs, env.dvec_get_get_ks inputs H_tgt_at_idx],
      -- apply congr_arg,

      -- -- 8. Final recursive case
      -- assertv H_gs_exist_ref : grads_exist_at nodes next_inputs ref := (H_gs_exist^.right H_tgt_in_parents)^.right,

      -- assert H_grad_gint_ref : is_gintegrable (λ m, ⟦compute_grad_slow costs nodes m ref⟧) next_inputs nodes dvec.head,
      -- begin
      -- assertv H_op_called : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
      --                                     next_inputs nodes dvec.head :=
      --   is_gintegrable_of_sumr_map (λ m idx, det.op.pb op (env.get_ks parents m) (env.get ref m) (compute_grad_slow costs nodes m ref) idx (tgt.snd))
      --                                     next_inputs nodes _ H_grad_gint₂ idx (in_filter _ _ _ H_idx_in_riota H_tgt_dnth_parents_idx),

      -- assert H_op_called_swap : is_gintegrable (λ m, ⟦det.op.pb op (env.get_ks parents next_inputs) x (compute_grad_slow costs nodes m ref) idx (tgt.snd)⟧)
      --                                         next_inputs nodes dvec.head,
      -- {
      -- apply is_gintegrable_k_congr _ _ _ _ _ H_wfs^.right^.uids _ H_op_called,
      -- intros m H_envs_match,
      -- -- TODO(dhs): this is copy-pasted from above
      -- assert H_parents_match : env.get_ks parents m = env.get_ks parents next_inputs,
      -- begin
      --   apply env.get_ks_env_eq,
      --   intros parent H_parent_in_parents,
      --   apply H_envs_match,
      --   apply env.has_key_insert,
      --   exact (H_wf^.ps_in_env^.left parent H_parent_in_parents)
      -- end,
      -- assert H_ref_matches : env.get ref m = x,
      -- begin
      --   assertv H_env_has_key_ref : env.has_key ref next_inputs := env.has_key_insert_same _ _,
      --   rw [H_envs_match ref H_env_has_key_ref, env.get_insert_same]
      -- end,
      -- simp only [H_parents_match, H_ref_matches],
      -- },

      -- simp only [λ (m : env), op^.pb_correct (env.get_ks parents next_inputs) x (by rw H_get_ks_next_inputs) (compute_grad_slow costs nodes m ref) H_tshape_at_idx H_f_pre] at H_op_called_swap,
      -- exact iff.mpr (is_gintegrable_tmulT _ _ _ _) H_op_called_swap
      -- end,

      -- assert H_gdiff_ref : is_gdifferentiable (λ m, ⟦sum_costs m costs⟧) ref next_inputs nodes dvec.head,
      --   { exact H_gdiff^.right^.right^.right H_idx_in_riota H_tgt_dnth_parents_idx },

      -- assert H_nabla_gint_ref : is_nabla_gintegrable (λ m, ⟦sum_costs m costs⟧) ref next_inputs nodes dvec.head,
      --   { exact H_nabla_gint^.right H_idx_in_riota H_tgt_dnth_parents_idx },

      -- pose H_correct_ref := compute_grad_slow_correct H_wfs^.right H_gs_exist_ref H_pdfs_exist_next
      --                                                 H_gdiff_ref H_nabla_gint_ref H_grad_gint_ref (H_diff_under_int^.right H_tgt_in_parents),

      -- simp [H_get_ref_next] at H_correct_ref,
      -- dsimp at H_correct_ref,
      -- simp [env.insert_insert_same] at H_correct_ref,
      -- dsimp,
      -- simp [env.dvec_update_at_env inputs H_tgt_at_idx],
      -- exact H_correct_ref
      -- end
| (⟨ref, parents, Operator.rand op⟩ :: nodes), inputs, tgt => by sorry
end theorems
end certigrad
