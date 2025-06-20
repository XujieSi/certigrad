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
          unfold next_inputs x
          simp [env.get_insert_same]




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

      have H₁:
        ∇ (fun θ₀ => g (env.getKs parents inputs) θ₀) θ =
        ∇ (fun θ₀ => E (graph.toDist (fun m => sumCosts m costs ::: Dvec.dnil)
            (env.insert tgt θ₀ next_inputs) nodes) Dvec.head)
            (env.get tgt inputs):= by
            unfold g θ next_inputs x
            set x := op.f (env.getKs parents inputs)
            simp [λ (θ : T tgt.2) => env.insert_insert_flip x θ inputs (Ne.symm H_tgt_neq_ref)]


      simp only [H₁]
      apply congr_arg
      apply (congr_arg sumr)
      apply map_filter_congr
      intros idx H_idx_in_riota H_tgt_dnth_parents_idx
      have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩
      have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
      have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx

      dsimp only [g]
      rw [T.grad_chain_rule
              (λ (θ : T tgt.2) =>
                op.f (dvec.update_at θ (env.getKs parents inputs) idx))
              (λ (x : T ref.2) =>
                E
                  (graph.toDist
                      (λ (m : Env) => sumCosts m costs ::: Dvec.dnil)
                        (env.insert ref x (env.insert tgt θ inputs)) nodes)
                      Dvec.head)
              θ
              ]
      rw [env.insert_get_same H_wf.m_contains_tgt]
      have H_swap_m_for_inputs :
        graph.toDist (λ (m : Env) =>
                   ⟦op.pb (env.getKs parents m)
                           (env.get ref m)
                           (computeGradSlow costs nodes m ref)
                           idx
                           tgt.2⟧)
                next_inputs
                nodes
          =
          (graph.toDist (λ (m : Env) =>
                              ⟦op.pb (env.getKs parents next_inputs)
                                      x
                                      (computeGradSlow costs nodes m ref)
                                      idx
                                      tgt.2⟧)
                          next_inputs
                          nodes) := by
            apply graph.toDist_congr
            exact H_wfs.right.uids
            dsimp
            intros m H_envs_match
            apply dvec.singleton_congr
            have H_parents_match : env.getKs parents m = env.getKs parents next_inputs := by
              apply env.get_ks_env_eq
              intros parent H_parent_in_parents
              apply H_envs_match
              apply env.hasKey_insert
              exact (H_wf.psInEnv.left parent H_parent_in_parents)
            have H_ref_matches : env.get ref m = x := by
              have H_env_has_key_ref : env.hasKey ref next_inputs := env.hasKey_insert_same _ _
              rw [H_envs_match ref H_env_has_key_ref, env.get_insert_same]
            simp [H_parents_match, H_ref_matches]
      rw [H_swap_m_for_inputs]
      have H_f_pre : op.pre (env.getKs parents next_inputs) := Eq.recOn (Eq.symm H_get_ks_next_inputs) (H_gs_exist.right H_tgt_in_parents).left
      simp [λ (m : Env) => op.pb_correct (env.getKs parents next_inputs) x (by rw [H_get_ks_next_inputs]) (computeGradSlow costs nodes m ref) H_tshape_at_idx H_f_pre]
      simp [E.E_k_tmulT, H_get_ks_next_inputs, env.dvec_get_get_ks inputs H_tgt_at_idx]
      apply congr_arg

      have H_op_called : isGintegrable (λ m => ⟦det.op.pb op (env.getKs parents m) (env.get ref m) (computeGradSlow costs nodes m ref) idx tgt.2⟧)
                                    next_inputs nodes Dvec.head :=
        is_gintegrable_of_sumr_map (λ m idx => det.op.pb op (env.getKs parents m) (env.get ref m) (computeGradSlow costs nodes m ref) idx (tgt.snd))
                                    next_inputs nodes _ H_grad_gint₂ idx (List.mem_filter_of_mem H_idx_in_riota (decide_eq_true H_tgt_dnth_parents_idx))

      have H_gs_exist_ref : gradsExistAt nodes next_inputs ref := (H_gs_exist.right H_tgt_in_parents).right

      have H_op_called_swap : isGintegrable (λ m => ⟦det.op.pb op (env.getKs parents next_inputs) x (computeGradSlow costs nodes m ref) idx tgt.2⟧)
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

      have H_gdiff_ref : isGdifferentiable (λ m => ⟦sumCosts m costs⟧) ref next_inputs nodes Dvec.head := by exact H_gdiff.right.right.right H_idx_in_riota H_tgt_dnth_parents_idx
      have H_nabla_gint_ref : isNablaGintegrable (λ m => ⟦sumCosts m costs⟧) ref next_inputs nodes Dvec.head := by
        exact H_nabla_gint.right H_idx_in_riota H_tgt_dnth_parents_idx

      have H_grad_gint_ref : isGintegrable (λ m => ⟦computeGradSlow costs nodes m ref⟧) next_inputs nodes Dvec.head := by
        simp only [λ (m : Env) => op.pb_correct (env.getKs parents next_inputs) x (by rw [H_get_ks_next_inputs]) (computeGradSlow costs nodes m ref) H_tshape_at_idx H_f_pre] at H_op_called_swap
        exact (is_gintegrable_tmulT _ _ _ _).mpr H_op_called_swap
      have H_correct_ref := compute_grad_slow_correct H_wfs.right H_gs_exist_ref H_pdfs_exist_next
                                                H_gdiff_ref H_nabla_gint_ref H_grad_gint_ref (H_diff_under_int.right H_tgt_in_parents)
      simp  [H_get_ref_next] at H_correct_ref
      unfold next_inputs at H_correct_ref
      simp [env.insert_insert_same] at H_correct_ref
      unfold θ next_inputs
      simp [env.dvec_update_at_env inputs H_tgt_at_idx]
      exact H_correct_ref
| (⟨ref, parents, Operator.rand op⟩ :: nodes), inputs, tgt => by
  intro H_wf H_gs_exist H_pdfs_exist H_gdiff H_nabla_gint H_grad_gint H_diff_under_int

  let θ := env.get tgt inputs
  let next_inputs := λ (y : T ref.2) => env.insert ref y inputs

-- 0. Collect useful helpers
  have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
  have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids
  have H_insert_θ : env.insert tgt θ inputs = inputs := by rw [env.insert_get_same H_wf.m_contains_tgt]

  have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by
    intro y
    unfold next_inputs
    rw [env.get_ks_insert_diff H_ref_notin_parents]

  have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by
    intro y
    unfold next_inputs
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by
    intro y
    exact wf_at_next H_wf

  have H_op_pre : op.pre (env.getKs parents inputs) := H_pdfs_exist.left

  dsimp only [graph.toDist, Operator.toDist]
  simp only [E.E_bind]

-- 1. Rewrite with the hybrid estimator
  let g := (λ (x : T ref.2) (θ₀ : T tgt.2) => E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧) (env.insert ref x (env.insert tgt θ₀ inputs)) nodes) Dvec.head)

  let θ := env.get tgt inputs

  have H_diff₁ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)) => E (sprog.prim op (env.getKs parents (env.insert tgt θ inputs))) (λ (y : Dvec T [ref.snd]) => g y.head θ₀)) θ := by
    exact H_gdiff.left

  have H_diff₂ : T.is_cdifferentiable (λ (θ₀ : T (tgt.snd)) => sumr (map (λ (idx : ℕ) => E (sprog.prim op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx)) (λ (y : Dvec T [ref.snd]) => g y.head θ))
                                                                      (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))) θ := by
    exact H_gdiff.right.left

  have H_eint₁ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ inputs))) (λ (x : Dvec T [ref.snd]) => ∇ (g x.head) θ) := by
    dsimp [E.is_eintegrable, Dvec.head]
    unfold θ g
    simp only [env.insert_get_same H_wf.m_contains_tgt]
    exact H_nabla_gint.left

  have H_eint₂ : E.is_eintegrable (sprog.prim op (env.getKs parents (env.insert tgt θ inputs)))
    (λ (x : Dvec T [ref.snd]) =>
       sumr
         (map
            (λ (idx : ℕ) =>
               g x.head θ •  ∇
                 (λ (θ₀ : T (tgt.snd)) =>
                    T.log
                      (rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx)
                         (Dvec.head x)))
                 θ)
            (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))) := by
                dsimp [E.is_eintegrable, Dvec.head]
                unfold θ g
                simp only [env.insert_get_same H_wf.m_contains_tgt]
                exact H_nabla_gint.right.left

  have H_g_diff : ∀ (x : T (ref.snd)), T.is_cdifferentiable (g x) θ := by
    intros y
    unfold θ g
    simp [λ θ₀ => env.insert_insert_flip y θ₀ inputs (Ne.symm H_tgt_neq_ref)]
    simp [Eq.symm (H_can_insert_y y)]
    apply pd_is_cdifferentiable _ _ _ _ (H_wfs y).left (H_gs_exist.right y) (H_pdfs_exist.right y) (H_diff_under_int.right y)




  have H_g_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => rand.op.pdf op (env.getKs parents (env.insert tgt θ inputs)) x • g x θ₀) θ := by
    exact can_diff_under_ints_alt1 H_diff_under_int

  have H_g_grad_uint : T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => ∇ (λ (θ₁ : T (tgt.snd)) => rand.op.pdf op (env.getKs parents (env.insert tgt θ inputs)) x • g x θ₁) θ₀) θ := by
    exact H_diff_under_int.left.right.left.right

  have H_d'_pdf_cdiff : ∀ (idx : ℕ), at_idx parents idx tgt →
    ∀ (v : T (ref.snd)), T.is_cdifferentiable (λ (x₀ : T (tgt.snd)) => rand.op.pdf op (dvec.update_at x₀ (env.getKs parents (env.insert tgt θ inputs)) idx) v) θ := by
     intros idx H_at_idx y
     have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_at_idx
     have H_pre_satisfied : op.pre (env.getKs parents inputs) := H_gs_exist.left H_tgt_in_parents
     unfold θ
     simp [env.insert_get_same H_wf.m_contains_tgt]
     simp [Eq.symm (env.dvec_get_get_ks inputs H_at_idx)]
     exact op.pdf_cdiff (at_idx_p2 H_at_idx) H_pre_satisfied

  have H_d'_uint : ∀ (idx : ℕ), at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) => rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx) x • g x θ) θ := by
    exact H_diff_under_int.left.right.right.left

  have H_d'_grad_uint : ∀ (idx : ℕ),  at_idx parents idx tgt →
    T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.snd)) (x : T (ref.snd)) =>
                                         ∇ (λ (θ₀ : T (tgt.snd)) => rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents (env.insert tgt θ inputs)) idx) x • g x θ) θ₀) θ := by
    exact H_diff_under_int.left.right.right.right

  rw [ Estimators.hybrid_general inputs H_wf.m_contains_tgt op H_op_pre g θ rfl
                              H_g_diff H_g_uint H_g_grad_uint
                              @H_d'_pdf_cdiff @H_d'_uint @H_d'_grad_uint H_diff₁ H_diff₂ H_eint₁ H_eint₂]

-- 2. Cancel first stochastic choice
  -- dsimp
  unfold g θ
  simp only [env.insert_get_same H_wf.m_contains_tgt]
  apply congr_arg
  apply funext
  intro y

  cases y with
  | dcons y Dvec.dnil =>
    dsimp [Dvec.head]

    have H_get_ks_next_inputs : env.getKs parents (next_inputs y) = env.getKs parents inputs := by
      dsimp
      rw [env.get_ks_insert_diff H_ref_notin_parents]

    have H_get_ref_next : env.get ref (next_inputs y) = y := by
      dsimp
      rw [env.get_insert_same]

-- 3. Push E over sum on RHS
    unfold computeGradSlow
    have H_grad_gint₁ : isGintegrable (λ (m : Env) => ⟦computeGradSlow costs nodes m tgt⟧) (env.insert ref y inputs) nodes Dvec.head := by
      dsimp [isGintegrable, computeGradSlow] at H_grad_gint
      apply ((is_gintegrable_k_add _ _ _ _).mpr (H_grad_gint.right y)).left

    have H_grad_gint₂ : isGintegrable
        (λ (m : Env) =>
          ⟦sumr
            (map
                (λ (idx : ℕ) =>
                  sumDownstreamCosts nodes costs ref m • rand.op.glogpdf op (env.getKs parents m) (env.get ref m) idx
                    (tgt.snd))
                (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents))))⟧)
        (env.insert ref y inputs)
        nodes
        Dvec.head := by
            dsimp [isGintegrable, computeGradSlow] at H_grad_gint
            apply ((is_gintegrable_k_add _ _ _ _).mpr (H_grad_gint.right y)).right

    rw [E.E_k_add _ _ _ _ H_grad_gint₁ H_grad_gint₂]

    have H_gdiff_tgt : isGdifferentiable (λ (m : Env) => ⟦sumCosts m costs⟧) tgt (next_inputs y) nodes Dvec.head := by
      exact H_gdiff.right.right y

    have H_grad_gint_tgt : isGintegrable (λ (m : Env) => ⟦computeGradSlow costs nodes m tgt⟧) (next_inputs y) nodes Dvec.head := by
      exact ((is_gintegrable_k_add _ _ _ _).mpr (H_grad_gint.right y)).left

    have H_nabla_gint_tgt : isNablaGintegrable (λ (m : Env) => ⟦sumCosts m costs⟧) tgt (next_inputs y) nodes Dvec.head := by
      exact H_nabla_gint.right.right y

    erw [← (compute_grad_slow_correct (H_wfs y).left (H_gs_exist.right y) (H_pdfs_exist.right y) H_gdiff_tgt H_nabla_gint_tgt H_grad_gint_tgt (H_diff_under_int.right y))]
    -- dsimp,
    unfold next_inputs
    simp [λ (θ : T tgt.2) => env.insert_insert_flip θ y inputs H_tgt_neq_ref]
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]
    apply congr_arg


    rw [E.E_k_sum_map _ _ _ _ (H_pdfs_exist.right y) H_grad_gint₂]
    apply congr_arg

  -- 6. Apply map_filter_congr
    exact map_filter_expand_helper _ _ _ _ _ _ H_wf H_gs_exist _


end theorems
end certigrad
