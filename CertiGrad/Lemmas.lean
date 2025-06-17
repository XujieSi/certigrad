/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Miscellaneous lemmas.
-/
import CertiGrad.Predicates
import CertiGrad.Tcont
import CertiGrad.ExpectedValue

namespace certigrad
open List
open util_list
lemma env_not_has_key_insert {m : Env} {ref₁ ref₂ : Reference} {x : T ref₂.2} :
  ref₁ ≠ ref₂ → (¬ env.hasKey ref₁ m) → (¬ env.hasKey ref₁ (env.insert ref₂ x m)) :=
by
  intro H_neq H_nin H_in
  exact H_nin (env.hasKey_insert_diff H_neq H_in)

lemma env_in_nin_ne {m : Env} {ref₁ ref₂ : Reference} : env.hasKey ref₁ m → (¬ env.hasKey ref₂ m) → ref₁ ≠ ref₂ :=
by
  intro H_in H_nin H_eq
  subst H_eq
  exact H_nin H_in

lemma ref_notin_parents {n : Node} {nodes : List Node} {m : Env} :
  allParentsInEnv m (n::nodes) → uniqIds (n::nodes) m → n.ref ∉ n.parents :=
by
  let ⟨ref, parents, op⟩ := n
  intro H_ps_in_env H_uids H_ref_in_parents

  simp [uniqIds] at H_uids
  simp at H_ref_in_parents
  simp [allParentsInEnv] at H_ps_in_env
  exact H_uids.left (H_ps_in_env.left ref.1 ref.2 H_ref_in_parents)


lemma ref_ne_tgt {n : Node} {nodes : List Node} {m : Env} {tgt : Reference} :
  env.hasKey tgt m → uniqIds (n::nodes) m → tgt ≠ n.ref :=
by
  intro H_tgt H_uids
  exact env_in_nin_ne H_tgt H_uids.left


lemma wf_at_next {costs : List ID} {n : Node} {nodes : List Node} {x : T n.ref.2} {inputs : Env} {tgt : Reference} :
  let next_inputs : Env := env.insert n.ref x inputs
  wellFormedAt costs (n::nodes) inputs tgt →
  wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs n.ref := by
  intro next_inputs H_wf
  let ref := n.ref
  have H_uids_next : uniqIds nodes next_inputs := by
    simp [next_inputs, H_wf.uids.right]

  have H_ps_in_env_next : allParentsInEnv next_inputs nodes := H_wf.psInEnv.right x
  have H_costs_scalars_next : allCostsScalars costs nodes := H_wf.costsScalars.right
  have H_m_contains_tgt : env.hasKey tgt next_inputs := by
    apply env.hasKey_insert
    exact H_wf.m_contains_tgt
  have H_m_contains_ref : env.hasKey ref next_inputs := by
    apply env.hasKey_insert_same
  have H_cost_scalar_tgt : tgt.1 ∈ costs → tgt.2 = [] := H_wf.tgt_cost_scalar
  have H_cost_scalar_ref : ref.1 ∈ costs → ref.2 = [] := H_wf.costsScalars.left
  have H_wf_tgt : wellFormedAt costs nodes next_inputs tgt :=
    ⟨H_uids_next, H_ps_in_env_next, H_costs_scalars_next, H_m_contains_tgt, H_cost_scalar_tgt⟩
  have H_wf_ref : wellFormedAt costs nodes next_inputs ref :=
    ⟨H_uids_next, H_ps_in_env_next, H_costs_scalars_next, H_m_contains_ref, H_cost_scalar_ref⟩
  exact ⟨H_wf_tgt, H_wf_ref⟩

lemma can_diff_under_ints_alt1 {costs : List ID}
  {ref : Reference} {parents : List Reference} {op :  rand.op parents.p2 ref.2} {nodes : List Node} {inputs : Env} {tgt : Reference} :
  let θ : T tgt.2 := env.get tgt inputs
  let g : T ref.2 → T tgt.2 → TReal :=
  fun (x : T ref.2) (θ₀ : T tgt.2) =>
    E
      (graph.toDist
        (fun (inputs : Env) => ⟦sumCosts inputs costs ⟧)
        (env.insert ref x (env.insert tgt θ₀ inputs))
        nodes)
      Dvec.head
canDifferentiateUnderIntegrals costs (⟨ref, parents, Operator.rand op⟩ :: nodes) inputs tgt
→
T.is_uniformly_integrable_around (λ (θ₀ : T (tgt.2)) (x : T (ref.snd)) => rand.op.pdf op (env.getKs parents (env.insert tgt θ inputs)) x • g x θ₀) θ := by

dsimp [canDifferentiateUnderIntegrals]
intro H_cdi
let H := H_cdi.left.left
apply T.uint_right (λ θ₁ θ₂ x =>
rand.op.pdf op (env.getKs parents (env.insert tgt θ₁ inputs)) x •
         E
           (graph.toDist (λ (inputs : Env) => ⟦sumCosts inputs costs⟧)
              (env.insert ref x (env.insert tgt θ₂ inputs))
              nodes)
           Dvec.head) _ H


lemma pdfs_exist_at_ignore {ref₀ : Reference} {x₁ x₂ : T ref₀.2} :
  ∀ {nodes : List Node} {inputs : Env},
     allParentsInEnv inputs nodes →
     (¬ env.hasKey ref₀ inputs) → ref₀ ∉ map Node.ref nodes →
     pdfsExistAt nodes (env.insert ref₀ x₁ inputs) → pdfsExistAt nodes (env.insert ref₀ x₂ inputs)
| [], _, _, _, _, _ => by trivial
| (⟨ref, parents, Operator.det op⟩ :: nodes), inputs, H_ps_in_env, H_fresh₁, H_fresh₂, H_pdfs_exist_at =>
by
  dsimp [pdfsExistAt] at H_pdfs_exist_at
  dsimp [pdfsExistAt]
  have H_ref₀_notin_parents : ref₀ ∉ parents := λ H_contra => H_fresh₁ (H_ps_in_env.left ref₀ H_contra)
  have H_ref₀_neq_ref : ref₀ ≠ ref  := by
    intro H_contra
    subst H_contra
    exact H_fresh₂ mem_of_cons_same

  rw [env.get_ks_insert_diff H_ref₀_notin_parents]
  rw [env.insert_insert_flip _ _ _ (Ne.symm H_ref₀_neq_ref)]
  rw [env.get_ks_insert_diff H_ref₀_notin_parents ] at H_pdfs_exist_at
  rw [env.insert_insert_flip _ _ _ (Ne.symm H_ref₀_neq_ref)] at H_pdfs_exist_at


  apply (pdfs_exist_at_ignore (H_ps_in_env.right _) _ _ H_pdfs_exist_at)

  . intro H_contra
    exact H_fresh₁ (env.hasKey_insert_diff H_ref₀_neq_ref H_contra)
  . exact not_mem_of_not_mem_cons H_fresh₂

| (⟨ref, parents, Operator.rand op⟩ :: nodes), inputs, H_ps_in_env, H_fresh₁, H_fresh₂, H_pdfs_exist_at =>
by
    dsimp [pdfsExistAt] at H_pdfs_exist_at
    dsimp [pdfsExistAt]
    let H_ref₀_notin_parents : ref₀ ∉ parents := λ H_contra => H_fresh₁ (H_ps_in_env.left ref₀ H_contra)
    have H_ref₀_neq_ref : ref₀ ≠ ref := by
      intro H_contra
      subst H_contra
      exact H_fresh₂ mem_of_cons_same
    rw [env.get_ks_insert_diff H_ref₀_notin_parents]
    rw [env.get_ks_insert_diff H_ref₀_notin_parents] at H_pdfs_exist_at

    apply And.intro
    .exact H_pdfs_exist_at.left
    intro y
    have H_pdfs_exist_at_next := H_pdfs_exist_at.right y
    rw [env.insert_insert_flip _ _ _ (Ne.symm H_ref₀_neq_ref)]
    rw [env.insert_insert_flip _ _ _ (Ne.symm H_ref₀_neq_ref)] at H_pdfs_exist_at_next

    apply (pdfs_exist_at_ignore (H_ps_in_env.right _) _ _ H_pdfs_exist_at_next)
    . intro H_contra
      exact H_fresh₁ (env.hasKey_insert_diff H_ref₀_neq_ref H_contra)
    .exact not_mem_of_not_mem_cons H_fresh₂



lemma pdf_continuous {ref : Reference} {parents : List Reference} {op : rand.op parents.p2 ref.2}
  {nodes : List Node} {inputs : Env} {tgt : Reference} :
  ∀ {idx : ℕ}, at_idx parents idx tgt →
    env.hasKey tgt inputs →
    gradsExistAt (⟨ref, parents, Operator.rand op⟩ :: nodes) inputs tgt →
    ∀ (y : T ref.2),
    T.is_continuous (λ (x : T tgt.2)=>
                      (op.pdf (dvec.update_at x (env.getKs parents (env.insert tgt (env.get tgt inputs) inputs)) idx) y))
                      (env.get tgt inputs)
| idx, H_at_idx, H_tgt_in_inputs, H_gs_exist, y =>
  by
    have  H_tgt_in_parents: tgt ∈ parents := by exact mem_of_at_idx H_at_idx
    have H_pre_satisfied := H_gs_exist.left H_tgt_in_parents
    simp [env.insert_get_same H_tgt_in_inputs]

    -- dsimp
    simp [Eq.symm (env.dvec_get_get_ks inputs H_at_idx)]
    exact (op.cont (at_idx_p2 H_at_idx) H_pre_satisfied)


lemma continuous_of_grads_exist {costs : List ID} :
  Π  {nodes : List Node}{tgt : Reference}
  {inputs : Env},
  wellFormedAt costs nodes inputs tgt →
  gradsExistAt nodes inputs tgt →
  T.is_continuous (λ (θ₀ : T tgt.2) =>
                    E (graph.toDist (λ (env : Env) => ⟦sumCosts env costs⟧)
                                     (env.insert tgt θ₀ inputs)
                                     nodes)
                      Dvec.head)
                 (env.get tgt inputs)

  -- When proving theorems about inductive types like `List Node` that require recursive calls to obtain results on smaller cases, it is necessary to use `induction` (or other tactics that provide an induction hypothesis, such as `cases ... using WellFounded.induction`). This approach ensures both pattern matching and access to a usable induction hypothesis for recursive subgoals, avoiding issues like "infinite recursion" or "termination check failed".
| [], tgt, inputs, H_wf_at, H_gs_exist => by
    unfold graph.toDist
    simp [E.E_ret]
    unfold sumCosts
    apply T.continuous_sumr
    intros cost H_cost_in_costs
    have  H_em : (cost, []) = tgt ∨ (cost, []) ≠ tgt := Decidable.em _
    cases H_em
    case a.inr H_neq =>
      simp [λ (x₀ : T tgt.2) => @env.get_insert_diff (cost, []) tgt x₀ inputs H_neq]
      apply T.continuous_const
    case a.inl H_eq =>
      let ⟨ tgt₁, tgt₂⟩  := tgt
      injection H_eq with H_eq₁ H_eq₂
      rw [H_eq₁, H_eq₂]
      dsimp
      simp [env.get_insert_same]
      apply T.continuous_id
| (⟨ref, parents, Operator.det op⟩ :: nodes), tgt, inputs, H_wf, H_gs_exist => by

        let θ := env.get tgt inputs
        let x := op.f (env.getKs parents inputs)
        let next_inputs := env.insert ref x inputs
        have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
        have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
        have H_tgt_neq_ref : tgt ≠ ref :=  ref_ne_tgt H_wf.m_contains_tgt H_wf.uids

        have H_get_ks_next_inputs : env.getKs parents next_inputs = env.getKs parents inputs := by dsimp; rw [env.get_ks_insert_diff H_ref_notin_parents]
        have H_get_ref_next : env.get ref next_inputs = op.f (env.getKs parents inputs):= by dsimp; rw [env.get_insert_same]
        have H_can_insert : env.get tgt next_inputs = env.get tgt inputs := by dsimp; rw [env.get_insert_diff _ _ H_tgt_neq_ref]

        have H_insert_next : ∀ (y : T ref.2), env.insert ref y inputs = env.insert ref y next_inputs := by intro y; rw [env.insert_insert_same]

        have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref :=  wf_at_next H_wf
        have H_gs_exist_tgt : gradsExistAt nodes next_inputs tgt  :=  H_gs_exist.left

        unfold graph.toDist
        simp [E.E_bind, E.E_ret]
        unfold Operator.toDist
        simp [E.E_ret]

        have H_em_tgt_in_parents : tgt ∈ parents ∨ tgt ∉ parents := Decidable.em _
        cases H_em_tgt_in_parents
        case inl H_tgt_in_parents =>
            let chain₁ : T tgt.2 → T ref.2 :=
              λ (θ₀ : T tgt.2) => op.f (env.getKs parents (env.insert tgt θ₀ inputs))

            let chain₂ : T tgt.2 → T ref.2 → TReal :=
              λ (θ₀ : T tgt.2) (x₀ : T ref.2) =>
                E (graph.toDist (λ (env₀ : Env) => ⟦sumCosts env₀ costs⟧)
                                  (env.insert ref x₀ (env.insert tgt θ₀ inputs))
                                    nodes)
                    Dvec.head

            change T.is_continuous (λ (θ₀ : T tgt.2) => chain₂ θ₀ (chain₁ θ₀)) (env.get tgt inputs)

            have H_chain₁ : T.is_continuous (λ (θ₀ : T tgt.2) => chain₁ θ₀) (env.get tgt inputs):=by
                dsimp
                apply T.continuous_multiple_args
                intros idx H_at_idx
                simp [env.insert_get_same H_wf.m_contains_tgt]
                rw [←(env.dvec_get_get_ks _ H_at_idx)]
                apply (op.is_ocont (env.getKs parents inputs) (at_idx_p2 H_at_idx) (H_gs_exist.right $ mem_of_at_idx H_at_idx).left)

            have H_chain₂_θ : T.is_continuous (λ (x₀ : T tgt.2) => chain₂ x₀ (chain₁ (env.get tgt inputs))) (env.get tgt inputs):= by
                -- dsimp
                simp [chain₁, chain₂]
                simp [env.insert_get_same H_wf.m_contains_tgt]
                simp [λ (v₁ : T ref.2) (v₂ : T tgt.2) m => env.insert_insert_flip v₁ v₂ m (Ne.symm H_tgt_neq_ref)]
                rw [← H_can_insert]
                exact (continuous_of_grads_exist H_wfs.left H_gs_exist_tgt)

            have H_chain₂_f : T.is_continuous (chain₂ (env.get tgt inputs)) ((λ (θ₀ : T (tgt.2)) => chain₁ θ₀) (env.get tgt inputs)):= by
                have H_gs_exist_ref : gradsExistAt nodes next_inputs ref := (H_gs_exist.right H_tgt_in_parents).right
                simp [chain₁, chain₂]
                simp [env.insert_get_same H_wf.m_contains_tgt]
                rw [←H_get_ref_next]
                simp [H_insert_next]
                apply (continuous_of_grads_exist H_wfs.right H_gs_exist_ref)
            exact (T.continuous_chain_full H_chain₁ H_chain₂_θ H_chain₂_f)
        case inr H_tgt_notin_parents =>
          have H_nodep_tgt : ∀ (θ₀ : T tgt.2), env.getKs parents (env.insert tgt θ₀ inputs) = env.getKs parents inputs := by
              intro θ₀
              rw [env.get_ks_insert_diff H_tgt_notin_parents]
          simp [H_nodep_tgt]
          simp [λ (v₁ : T ref.2) (v₂ : T tgt.2) m => env.insert_insert_flip v₁ v₂ m (Ne.symm H_tgt_neq_ref)]
          rw [←H_can_insert]
          exact (continuous_of_grads_exist H_wfs.left H_gs_exist_tgt)
| (⟨ref, parents, Operator.rand op⟩ :: nodes), tgt, inputs, H_wf, H_gs_exist => by
      let θ := env.get tgt inputs
      let next_inputs := λ (y : T ref.2) => env.insert ref y inputs

      have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
      have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
      have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids
      have H_insert_θ : env.insert tgt θ inputs = inputs := by rw [env.insert_get_same H_wf.m_contains_tgt]

      have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by    intro y;  rw [env.get_ks_insert_diff H_ref_notin_parents]

      have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by
          intro y; rw [env.get_insert_diff _ _ H_tgt_neq_ref]

      have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by intro y; exact wf_at_next H_wf

      have H_pdf_continuous : ∀ (y : T ref.2), T.is_continuous (λ (θ₀ : T tgt.2) => op.pdf (env.getKs parents (env.insert tgt θ₀ inputs)) y) (env.get tgt inputs) := by
          intro (y : T ref.2)
          apply (T.continuous_multiple_args parents [] tgt inputs (λ xs => op.pdf xs y) (env.get tgt inputs))
          intros idx H_at_idx
          apply (pdf_continuous H_at_idx H_wf.m_contains_tgt H_gs_exist)

      have H_rest_continuous : ∀ (x : Dvec T [ref.2]),
  T.is_continuous (λ (θ₀ : T tgt.2) =>
                    E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
                                     (env.insert ref x.head (env.insert tgt θ₀ inputs))
                                     nodes)
                      Dvec.head)
                 (env.get tgt inputs) := by
            intro x
            have H_can_insert_x : ∀ (x : T ref.2), env.get tgt (env.insert ref x inputs) = env.get tgt inputs
              := by  intro y ; rw [env.get_insert_diff _ _ H_tgt_neq_ref]
            simp only [λ θ₀ => env.insert_insert_flip x.head θ₀ inputs (Ne.symm H_tgt_neq_ref)]
            simp only [Eq.symm (H_can_insert_x x.head)]
            exact (continuous_of_grads_exist (H_wfs _).left (H_gs_exist.right _))
      unfold graph.toDist Operator.toDist
      simp [E.E_bind]
      apply (E.E_continuous op (λ θ₀ => env.getKs parents (env.insert tgt θ₀ inputs)) _ _ H_pdf_continuous H_rest_continuous)


lemma rest_continuous {costs : List ID} {n : Node} {nodes : List Node} {inputs : Env} {tgt : Reference}:
  ∀ (x : Dvec T [n.ref.2]), tgt ≠ n.ref →
  wellFormedAt costs nodes (env.insert n.ref x.head inputs) tgt → gradsExistAt nodes (env.insert n.ref x.head inputs) tgt →
  T.is_continuous (λ (θ₀ : T tgt.2) =>
                    E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
                                     (env.insert n.ref x.head (env.insert tgt θ₀ inputs))
                                     nodes)
                      Dvec.head)
                 (env.get tgt inputs)
| x, H_tgt_neq_ref, H_wf_tgt, H_gs_exist_tgt => by
  have H_can_insert_x : ∀ (x : T n.ref.2), env.get tgt (env.insert n.ref x inputs) = env.get tgt inputs
    := by
    intro y
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]
  simp only [λ θ₀ => env.insert_insert_flip  x.head θ₀ inputs (Ne.symm H_tgt_neq_ref)]
  rw [Eq.symm (H_can_insert_x x.head)]
  exact continuous_of_grads_exist H_wf_tgt H_gs_exist_tgt

private lemma fref_notin_parents :
  Π {n : Node} {nodes : List Node} {inputs : Env} {fref : Reference},
    allParentsInEnv inputs (n::nodes) →
    (¬ env.hasKey fref inputs) →
    fref ∉ n.parents := by
      intro n
      let ⟨ref, parents, op⟩ := n
      dsimp
      intros nodes inputs fref H_ps_in_env H_fref_fresh H_fref_in_ps
      unfold allParentsInEnv at H_ps_in_env
      exact H_fref_fresh (H_ps_in_env.left fref H_fref_in_ps)

private lemma fref_neq_ref :
  Π {n : Node} {nodes : List Node} {inputs : Env} {fref : Reference},
    (¬ env.hasKey fref inputs) → fref ∉ map Node.ref (n::nodes) →
    fref ≠ n.ref := by
        intros n nodes inputs fref H_fref_fresh₁ H_fref_fresh₂
        exact (ne_of_not_mem_cons H_fref_fresh₂)

lemma to_dist_congr_insert : ∀ {costs : List ID} {nodes : List Node} {inputs : Env} {fref : Reference} {fval : T fref.2},
    allParentsInEnv inputs nodes →
    (¬ env.hasKey fref inputs) → fref ∉ map Node.ref nodes →
    fref.1 ∉ costs →
E (graph.toDist (λ env₀ => ⟦sumCosts env₀ costs⟧) (env.insert fref fval inputs) nodes) Dvec.head
=
E (graph.toDist (λ env₀ => ⟦sumCosts env₀ costs⟧) inputs nodes) Dvec.head
| costs, [], inputs,fref,fval, H_ps_in_env, H_fresh₁,H_fresh₂, H_not_cost => by
    unfold graph.toDist
    simp [E.E_ret]
    unfold  sumCosts map
    induction costs with
    | nil => rfl
    | cons cost costs IH_cost =>
        unfold map sumr
        have H_neq : (cost, []) ≠ fref := by
            intro H_contra
            let ⟨fid, fshape⟩ := fref
            injection H_contra with H_cost H_ignore
            simp [H_cost] at H_not_cost
        have H_notin : fref.1 ∉ costs := not_mem_of_not_mem_cons H_not_cost
        simp [env.get_insert_diff fval inputs H_neq]
        rw [IH_cost H_notin]
| costs,(⟨ref, parents, Operator.det op⟩::nodes),inputs,fref,fval, H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
  -- Sometimes using `simp` in facts is preferable to `unfold`, which can lead to many matches.
  simp [graph.toDist, Operator.toDist,E.E_bind, E.E_ret]
  have H_fref_notin_parents : fref ∉ parents := fref_notin_parents H_ps_in_env H_fresh₁
  have H_fref_neq_ref : fref ≠ ref := fref_neq_ref H_fresh₁ H_fresh₂
  rw [env.get_ks_insert_diff H_fref_notin_parents]
  rw [env.insert_insert_flip _ _ _ (Ne.symm H_fref_neq_ref)]
  apply (to_dist_congr_insert (H_ps_in_env.right _) _ _ H_not_cost)
  .
    intro H_contra
    exact H_fresh₁ (env.hasKey_insert_diff H_fref_neq_ref H_contra)
  . exact not_mem_of_not_mem_cons H_fresh₂

| costs, (⟨ref, parents, Operator.rand op⟩::nodes), inputs,fref,fval,H_ps_in_env, H_fresh₁, H_fresh₂, H_not_cost => by
  simp [graph.toDist, Operator.toDist, E.E_bind, E.E_ret]
  have H_fref_notin_parents : fref ∉ parents := fref_notin_parents H_ps_in_env H_fresh₁
  have H_fref_neq_ref : fref ≠ ref := fref_neq_ref H_fresh₁ H_fresh₂
  rw [env.get_ks_insert_diff H_fref_notin_parents]

  apply congr_arg
  apply funext
  intro x
  rw [env.insert_insert_flip _ _ _ (Ne.symm H_fref_neq_ref)]
  apply (@to_dist_congr_insert _ nodes _ _ _  (H_ps_in_env.right _) _ _ H_not_cost)
  . intro H_contra
    exact H_fresh₁ (env.hasKey_insert_diff H_fref_neq_ref H_contra)
  . exact not_mem_of_not_mem_cons H_fresh₂



lemma map_filter_expand_helper {costs : List ID} (ref : Reference) (parents : List Reference)
                               (op : rand.op parents.p2 ref.2)
                               (nodes : List Node) (inputs : Env) (tgt : Reference) :
wellFormedAt costs (⟨ref, parents, Operator.rand op⟩::nodes) inputs tgt →
gradsExistAt (⟨ref, parents, Operator.rand op⟩::nodes) inputs tgt →

∀ (y : T ref.2),
map
    (λ (idx : ℕ) =>
       E
         (graph.toDist
            (λ (m : Env)=> ⟦sumCosts m costs⟧)
            (env.insert ref y inputs)
            nodes)
         Dvec.head • ∇
         (λ (θ₀ : T (tgt.2))=>T.log (rand.op.pdf op (dvec.update_at θ₀ (env.getKs parents inputs) idx) y))
         (env.get tgt inputs))
    (filter (λ (idx : ℕ) =>tgt = dnth parents idx) (riota (length parents))) = map
    (λ (x : ℕ)=>
       E
         (graph.toDist
            (λ (m : Env)=>
               ⟦(λ (m : Env) (idx : ℕ)=>
                  sumDownstreamCosts nodes costs ref m • rand.op.glogpdf op (env.getKs parents m) (env.get ref m)
                    idx
                    (tgt.2))
                 m
                 x⟧)
            ((λ (y : T (ref.2)) => env.insert ref y inputs) y)
            nodes)
         Dvec.head)
    (filter (λ (idx : ℕ) => tgt = dnth parents idx) (riota (length parents)))
| H_wf, H_gs_exist, y => by
    let θ := env.get tgt inputs
    let next_inputs := λ (y : T ref.2) => env.insert ref y inputs

    have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
    have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids

    have H_get_ks_next_inputs : env.getKs parents (next_inputs y) = env.getKs parents inputs := by dsimp; rw [env.get_ks_insert_diff H_ref_notin_parents]
    have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by intro y; exact wf_at_next H_wf


--   -- Apply map_filter_congr
    apply map_filter_congr
    intros idx H_idx_in_riota H_tgt_dnth_parents_idx
    have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_dnth_parents_idx⟩
    have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
    have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx

--   -- 7. Replace `m` with `inputs`/`next_inputs` so that we can use the gradient rule for the logpdf
    unfold sumDownstreamCosts

    have H_swap_m_for_inputs :
    (graph.toDist
          (λ (m : Env) =>
              ⟦sumCosts m costs • rand.op.glogpdf op (env.getKs parents m) (env.get ref m) idx (tgt.2)⟧)
          (env.insert ref y inputs)
          nodes)
    =
    (graph.toDist
          (λ (m : Env) =>
              ⟦sumCosts m costs • rand.op.glogpdf op (env.getKs parents (next_inputs y)) (env.get ref (next_inputs y)) idx (tgt.2)⟧)
          (env.insert ref y inputs)
          nodes) := by
            apply graph.toDist_congr
            exact (H_wfs y).left.uids
            dsimp
            intros m H_envs_match
            apply dvec.singleton_congr
            have H_parents_match : env.getKs parents m = env.getKs parents (next_inputs y) :=
                by
                  apply env.get_ks_env_eq
                  intros parent H_parent_in_parents
                  apply H_envs_match
                  apply env.hasKey_insert
                  exact (H_wf.psInEnv.left parent H_parent_in_parents)
            have H_ref_matches : env.get ref m = y := by
              have H_env.has_key_ref : env.hasKey ref (next_inputs y) := env.hasKey_insert_same _ _
              rw [H_envs_match ref H_env.has_key_ref, env.get_insert_same]

            simp [H_parents_match, H_ref_matches, env.get_insert_same]
            sorry

    erw [H_swap_m_for_inputs]
    -- 8. push E over ⬝ and cancel the first terms
    rw [E.E_k_scale]
    apply congr_arg

--   -- 9. Use glogpdf correct
    have H_glogpdf_pre : op.pre (env.getKs parents (next_inputs y)) := by
        dsimp
        rw [env.get_ks_insert_diff H_ref_notin_parents]
        exact (H_gs_exist.left H_tgt_in_parents)

    simp [op.glogpdf_correct H_tshape_at_idx H_glogpdf_pre]
    -- unfold next_inputs
    -- 10. Clean-up
    -- unfold p2
    simp [H_get_ks_next_inputs]

    -- simp [env.get_insert_same, env.get_ks_insert_same, env.get_ks_insert_same, env.get_insert_same]
    simp [env.dvec_get_get_ks inputs H_tgt_at_idx]



lemma sum_costs_differentiable : Π (costs : List ID) (tgt : Reference) (inputs : Env),
  T.is_cdifferentiable (λ (θ₀ : T (tgt.2)) => sumr (map (λ (cost : ID) => env.get (cost, @nil ℕ) (env.insert tgt θ₀ inputs)) costs))
                      (env.get tgt inputs)

| costs, tgt, inputs => by
  induction costs with
  | nil =>
      unfold sumr map
      apply T.is_cdifferentiable_const
  | cons cost costs IHcosts =>
    unfold sumr map
    apply (T.is_cdifferentiable_add_fs _ _ _).mp
    constructor
    .
      have H_em : tgt = (cost, []) ∨ tgt ≠ (cost, []) := Decidable.em _
      cases H_em
      case inl H_eq =>
        rw [H_eq]
        simp only [env.get_insert_same]
        apply T.is_cdifferentiable_id
      case inr H_neq =>
        simp only [λ (x : T tgt.2) => env.get_insert_diff x inputs (Ne.symm H_neq), H_neq]
        apply T.is_cdifferentiable_const

    . exact IHcosts


lemma pd_is_cdifferentiable (costs : List ID) : Π (tgt : Reference) (inputs : Env) (nodes : List Node),
  wellFormedAt costs nodes inputs tgt →
  gradsExistAt nodes inputs tgt →
  pdfsExistAt nodes inputs →
  canDifferentiateUnderIntegrals costs nodes inputs tgt →
  T.is_cdifferentiable (λ (θ₀ : T tgt.2) => E (graph.toDist (λ m => ⟦sumCosts m costs⟧) (env.insert tgt θ₀ inputs) nodes) Dvec.head) (env.get tgt inputs)
| tgt, inputs, [] => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int
  exact sum_costs_differentiable costs tgt inputs

| tgt, inputs, (⟨ref, parents, Operator.det op⟩ :: nodes) => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int

  let θ := env.get tgt inputs
  let x := op.f (env.getKs parents inputs)
  let next_inputs := env.insert ref x inputs

  -- 0. Collect useful helpers
  have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same

  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids

  have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids

  have H_can_insert : env.get tgt next_inputs = env.get tgt inputs := by
    dsimp
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref := wf_at_next H_wf
  have H_gs_exist_tgt : gradsExistAt nodes next_inputs tgt := H_gs_exist.left
  have H_pdfs_exist_next : pdfsExistAt nodes next_inputs := H_pdfs_exist

  have H_pdiff_tgt := pd_is_cdifferentiable costs tgt next_inputs nodes H_wfs.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int.left

  dsimp [graph.toDist, Operator.toDist]
  simp only [E.E_ret, E.E_bind, Dvec.head]
  apply T.is_cdifferentiable_binary (λ θ₁ θ₂ => E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
                                                              (env.insert ref (det.op.f op (env.getKs parents (env.insert tgt θ₂ inputs))) (env.insert tgt θ₁ inputs))
                                                              nodes)
                                              Dvec.head)
  .
    -- case 1, simple recursive case
    dsimp
    simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip x θ inputs (Ne.symm H_tgt_neq_ref)]
    simp only [env.insert_get_same H_wf.m_contains_tgt]
    simp only [H_can_insert] at H_pdiff_tgt
    exact H_pdiff_tgt

  .
    -- start case 2
    dsimp
    simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip x θ inputs (Ne.symm H_tgt_neq_ref)]

    apply T.is_cdifferentiable_multiple_args _ _ _ op.f _ (λ (x' : T ref.2) =>
        E
          (graph.toDist
              (λ (m : Env) => ⟦sumCosts m costs⟧)
              (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
              nodes)
          Dvec.head)

    intros idx H_idx_in_riota H_tgt_eq_dnth_idx
    have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
    have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
    have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx

    have H_gs_exist_ref : gradsExistAt nodes next_inputs ref := (H_gs_exist.right H_tgt_in_parents).right
    have H_diff_under_int_ref : canDifferentiateUnderIntegrals costs nodes next_inputs ref := H_diff_under_int.right H_tgt_in_parents

    have H_pdiff_ref := pd_is_cdifferentiable costs ref next_inputs nodes H_wfs.right H_gs_exist_ref H_pdfs_exist_next H_diff_under_int_ref
    simp only [env.insert_get_same H_wf.m_contains_tgt]

    have H_odiff := op.is_odiff (env.getKs parents inputs) (H_gs_exist.right H_tgt_in_parents).left idx tgt.2 H_tshape_at_idx
                   (λ x' => E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
                                           (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
                                            nodes)
                             Dvec.head)

    simp only [λ m => env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff
    apply H_odiff

    -- simp at H_pdiff_ref
    simp only [next_inputs] at H_pdiff_ref
    simp only [env.insert_insert_same, env.get_insert_same] at H_pdiff_ref

    simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf.m_contains_tgt]
    exact H_pdiff_ref

| tgt, inputs, (⟨ref, parents, Operator.rand op⟩ :: nodes) => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int

  let θ := env.get tgt inputs
  let next_inputs := λ (y : T ref.2) => env.insert ref y inputs

  -- 0. Collect useful helpers
  have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
  have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids
  have H_insert_θ : env.insert tgt θ inputs = inputs := by rw [env.insert_get_same H_wf.m_contains_tgt]

  have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by
    intro y
    -- dsimp
    rw [env.get_ks_insert_diff H_ref_notin_parents]

  have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by
    intro y
    -- dsimp
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by
    intro y
    exact wf_at_next H_wf

  have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by intro y;rw [env.get_ks_insert_diff H_ref_notin_parents]
  have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by intro y;rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_op_pre : op.pre (env.getKs parents inputs) := H_pdfs_exist.left

  let g : T ref.2 → T tgt.2 → TReal :=
    (λ (x : T ref.2) (θ₀ : T tgt.2) =>
        E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
                        (env.insert ref x (env.insert tgt θ₀ inputs))
                        nodes)
          Dvec.head)

  have H_g_uint : T.is_uniformly_integrable_around
      (λ (θ₀ : T tgt.2) (x : T ref.2) =>
        rand.op.pdf op (env.getKs parents (env.insert tgt θ₀ inputs)) x • E
          (graph.toDist
              (λ (m : Env) => ⟦sumCosts m costs⟧)
              (env.insert ref x (env.insert tgt θ₀ inputs))
              nodes)
          Dvec.head)
      (env.get tgt inputs) := H_diff_under_int.left.left

  have H_g_grad_uint : T.is_uniformly_integrable_around
      (λ (θ₀ : T tgt.2) (x : T ref.2) =>
        ∇
          (λ (θ₁ : T tgt.2) =>
              (λ (x : T ref.2) (θ₀ : T tgt.2) =>
                rand.op.pdf op (env.getKs parents (env.insert tgt θ₀ inputs)) x • E
                  (graph.toDist
                      (λ (m : Env) => ⟦sumCosts m costs⟧)
                      (env.insert ref x (env.insert tgt θ₀ inputs))
                      nodes)
                  Dvec.head)
                x
                θ₁)
          θ₀)
      (env.get tgt inputs) := H_diff_under_int.left.right.left.left

  -- begin
  dsimp only [graph.toDist, Operator.toDist]
  simp only [E.E_bind]

  have H_pdiff_tgt := λ y => pd_is_cdifferentiable costs tgt (next_inputs y) nodes (H_wfs y).left (H_gs_exist.right y) (H_pdfs_exist.right y) (H_diff_under_int.right y)
  simp [E.E_bind, T.dintegral, Dvec.head]
  apply T.is_cdifferentiable_integral _ _ _ H_g_uint H_g_grad_uint
  intro y

  apply T.is_cdifferentiable_binary (λ θ₁ θ₂ => rand.op.pdf op (env.getKs parents (env.insert tgt θ₁ inputs)) y • E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧) (env.insert ref y (env.insert tgt θ₂ inputs)) nodes) Dvec.head)

  -- start PDF differentiable
  -- dsimp
  .
    apply (T.is_cdifferentiable_fscale _ _ _).mp
    apply T.is_cdifferentiable_multiple_args _ _ _ (λ θ => op.pdf θ y) _ (λ y : TReal => y)
    intros idx H_idx_in_riota H_tgt_eq_dnth_idx
    have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
    have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
    have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx
    -- dsimp

    have H_pdf_cdiff := @rand.op.pdf_cdiff _ _ op (env.getKs parents inputs) y idx tgt.2 H_tshape_at_idx H_pdfs_exist.left
    simp [rand.pdf_cdiff] at H_pdf_cdiff
    simp only [env.insert_get_same H_wf.m_contains_tgt]
    simp only [λ m => env.dvec_get_get_ks m H_tgt_at_idx] at H_pdf_cdiff
    exact H_pdf_cdiff

  .
    -- start E differentiable
    dsimp
    -- sorry
    -- simp at H_pdiff_tgt
    unfold next_inputs at H_pdiff_tgt
    apply (T.is_cdifferentiable_scale_f _ _ _).mp
    simp only [λ x y z => env.insert_insert_flip x y z H_tgt_neq_ref] at H_pdiff_tgt
    simp only [λ x y => env.get_insert_diff x y H_tgt_neq_ref] at H_pdiff_tgt
    apply H_pdiff_tgt

lemma is_gdifferentiable_of_pre {costs : List ID} : Π (tgt : Reference) (inputs : Env) (nodes : List Node),
  wellFormedAt costs nodes inputs tgt →
  gradsExistAt nodes inputs tgt →
  pdfsExistAt nodes inputs →
  canDifferentiateUnderIntegrals costs nodes inputs tgt →
  isGdifferentiable (λ m => ⟦sumCosts m costs⟧) tgt inputs nodes Dvec.head
| tgt, inputs, [] => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int
  exact trivial

| tgt, inputs, (⟨ref, parents, Operator.det op⟩ :: nodes) => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int

  let θ := env.get tgt inputs
  let x := op.f (env.getKs parents inputs)
  let next_inputs := env.insert ref x inputs

  -- 0. Collect useful helpers
  have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
  have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids
  have H_can_insert : env.get tgt next_inputs = env.get tgt inputs := by
    dsimp
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref := wf_at_next H_wf
  have H_gs_exist_tgt : gradsExistAt nodes next_inputs tgt := H_gs_exist.left
  have H_pdfs_exist_next : pdfsExistAt nodes next_inputs := H_pdfs_exist

  have H_wfs : wellFormedAt costs nodes next_inputs tgt ∧ wellFormedAt costs nodes next_inputs ref := wf_at_next H_wf
  have H_gs_exist_tgt : gradsExistAt nodes next_inputs tgt := H_gs_exist.left
  have H_pdfs_exist_next : pdfsExistAt nodes next_inputs := H_pdfs_exist

  have H_gdiff_tgt : isGdifferentiable (λ m => ⟦sumCosts m costs⟧) tgt next_inputs nodes Dvec.head :=
    is_gdifferentiable_of_pre tgt next_inputs nodes H_wfs.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int.left

-- begin
  dsimp [gradsExistAt] at H_gs_exist
  dsimp [pdfsExistAt] at H_pdfs_exist
  simp [isGdifferentiable] at H_gdiff_tgt
  dsimp [isGdifferentiable]
-- TODO(dhs): replace once `apply` tactic can handle nesting
  apply And.intro
  .
    simp only [env.insert_get_same H_wf.m_contains_tgt, env.get_insert_same]
    have H_pdiff := pd_is_cdifferentiable costs tgt next_inputs nodes H_wfs.left H_gs_exist_tgt H_pdfs_exist_next H_diff_under_int.left
    simp only [H_can_insert] at H_pdiff
    sorry
    -- simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip θ x inputs H_tgt_neq_ref] at H_pdiff
    -- exact H_pdiff
  .
    apply And.intro
    .
      sorry
      -- apply T.is_cdifferentiable_sumr
      -- intro idx H_idx_in_filter
      -- let ⟨ H_idx_in_riota, H_tgt_eq_dnth_idx ⟩ := of_in_filter _ _ _ H_idx_in_filter
      -- cases of_in_filter _ _ _ H_idx_in_filter with H_idx_in_riota H_tgt_eq_dnth_idx
      -- have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
      -- have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
      -- have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx
      -- have H_gs_exist_ref : gradsExistAt nodes next_inputs ref := (H_gs_exist.right H_tgt_in_parents).right

      -- have H_pdiff := pd_is_cdifferentiable costs ref next_inputs nodes H_wfs.right H_gs_exist_ref H_pdfs_exist_next (H_diff_under_int.right H_tgt_in_parents)
      -- simp only [env.insert_get_same H_wf.m_contains_tgt]
      -- simp only [env.get_insert_same, env.insert_insert_same] at H_pdiff

      -- have H_odiff := op.is_odiff (env.getKs parents inputs) (H_gs_exist.right H_tgt_in_parents).left idx tgt.2 H_tshape_at_idx
      --              (λ x' => E (graph.toDist (λ (m : Env) => ⟦sumCosts m costs⟧)
      --                                      (env.insert tgt (env.get tgt inputs) (env.insert ref x' inputs))
      --                                       nodes)
      --                        Dvec.head)

      -- simp only [λ m => env.dvec_get_get_ks m H_tgt_at_idx] at H_odiff
      -- simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf.m_contains_tgt] at H_odiff
      -- exact H_odiff
      -- exact H_pdiff

    . apply And.intro
      .exact H_gdiff_tgt
      .
        intro idx H_idx_in_riota H_tgt_eq_dnth_idx
        have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
        have H_tshape_at_idx : at_idx parents.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx
        have H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx
        have H_gs_exist_ref : gradsExistAt nodes next_inputs ref := (H_gs_exist.right H_tgt_in_parents).right
        exact is_gdifferentiable_of_pre ref next_inputs nodes H_wfs.right H_gs_exist_ref H_pdfs_exist_next (H_diff_under_int.right H_tgt_in_parents)

| tgt, inputs, (⟨ref, parents, Operator.rand op⟩ :: nodes) => by
  intro H_wf H_gs_exist H_pdfs_exist H_diff_under_int

  let θ := env.get tgt inputs
  let next_inputs := λ (y : T ref.2) => env.insert ref y inputs

-- 0. Collect useful helpers
  have H_ref_in_refs : ref ∈ ref :: map Node.ref nodes := mem_of_cons_same
  have H_ref_notin_parents : ref ∉ parents := ref_notin_parents H_wf.psInEnv H_wf.uids
  have H_tgt_neq_ref : tgt ≠ ref := ref_ne_tgt H_wf.m_contains_tgt H_wf.uids
  have H_insert_θ : env.insert tgt θ inputs = inputs := by rw [env.insert_get_same H_wf.m_contains_tgt]

  have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by
    intro y
    rw [env.get_ks_insert_diff H_ref_notin_parents]

  have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by
    intro y
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_wfs : ∀ y, wellFormedAt costs nodes (next_inputs y) tgt ∧ wellFormedAt costs nodes (next_inputs y) ref := by
    intro y
    exact wf_at_next H_wf

  have H_parents_match : ∀ y, env.getKs parents (next_inputs y) = env.getKs parents inputs := by
    intro y
    rw [env.get_ks_insert_diff H_ref_notin_parents]

  have H_can_insert_y : ∀ y, env.get tgt (next_inputs y) = env.get tgt inputs := by
    intro y
    rw [env.get_insert_diff _ _ H_tgt_neq_ref]

  have H_op_pre : op.pre (env.getKs parents inputs) := H_pdfs_exist.left

  -- begin
  dsimp [isGdifferentiable]
  -- TODO(dhs): use apply and.intro _ (and.intro _ _) once tactic is fixed
  apply And.intro
  .
    unfold E T.dintegral
    have H_g_uint := can_diff_under_ints_alt1 H_diff_under_int
    have H_g_grad_uint := H_diff_under_int.left.right.left.right
    apply T.is_cdifferentiable_integral _ _ _ H_g_uint H_g_grad_uint

    intro y
    apply (T.is_cdifferentiable_scale_f _ _ _).mp

    have H_pdiff := pd_is_cdifferentiable costs tgt (next_inputs y) nodes (H_wfs y).left (H_gs_exist.right y) (H_pdfs_exist.right y) (H_diff_under_int.right y)
    simp only [Dvec.head] at H_pdiff
    simp only [H_can_insert_y] at H_pdiff
    simp only [λ (x : T ref.2) (θ : T tgt.2) => env.insert_insert_flip θ x inputs H_tgt_neq_ref, env.insert_get_same H_wf.m_contains_tgt] at H_pdiff
    exact H_pdiff
  .
      apply T.is_cdifferentiable_sumr
      intro idx H_idx_in_filter
      -- let ⟨ H_idx_in_riota, H_tgt_eq_dnth_idx ⟩ := of_in_filter _ _ _ H_idx_in_filter
      -- have H_tgt_at_idx : at_idx parents idx tgt := ⟨in_riota_lt H_idx_in_riota, H_tgt_eq_dnth_idx⟩
      -- assertv H_tshape_at_idx : at_idx parents^.p2 idx tgt.2 := at_idx_p2 H_tgt_at_idx,
      -- assertv H_tgt_in_parents : tgt ∈ parents := mem_of_at_idx H_tgt_at_idx,

      -- note H_g_uint_idx := H_diff_under_int^.left^.right^.right^.left _ H_tgt_at_idx,
      -- note H_g_grad_uint_idx := H_diff_under_int^.left^.right^.right^.right _ H_tgt_at_idx,

      -- dunfold E T.dintegral,
      -- apply T.is_cdifferentiable_integral _ _ _ H_g_uint_idx H_g_grad_uint_idx,
      -- tactic.rotate 2,
      -- dsimp [dvec.head],

      -- intro y,
      -- apply iff.mp (T.is_cdifferentiable_fscale _ _ _),

      -- note H_pdf_cdiff := @rand.op.pdf_cdiff _ _ op (env.get_ks parents inputs) y idx tgt.2 H_tshape_at_idx H_pdfs_exist^.left,
      -- dsimp [rand.pdf_cdiff] at H_pdf_cdiff,
      -- simp only [env.insert_get_same H_wf^.m_contains_tgt],
      -- simp only [λ m, env.dvec_get_get_ks m H_tgt_at_idx] at H_pdf_cdiff,
      -- exact H_pdf_cdiff,

lemma can_diff_under_ints_of_all_pdfs_std (costs : List ID) : Π (nodes : List Node) (m : Env) (tgt : Reference),
  allPdfsStd nodes
  → canDifferentiateUnderIntegrals costs nodes m tgt
  → canDifferentiateUnderIntegrals costs nodes m tgt
| [], m, tgt, H_std, H_cdi => by trivial

| (⟨ref, parents, Operator.det op⟩ :: nodes), m, tgt, H_std, H_cdi => by
  simp [allPdfsStd] at H_std
  simp [canDifferentiateUnderIntegrals] at H_cdi
  apply And.intro
  .
    apply can_diff_under_ints_of_all_pdfs_std
    exact H_std
    exact H_cdi.left

  .
    intro H_in
    apply can_diff_under_ints_of_all_pdfs_std
    exact H_std
    exact H_cdi.right H_in

| (⟨(ref, .(shape)), [], Operator.rand (rand.op.mvn_std shape)⟩ :: nodes), m, tgt, H_std, H_cdi => by
  dsimp only [allPdfsStd] at H_std
  dsimp only [canDifferentiateUnderIntegrals] at H_cdi
  dsimp  [canDifferentiateUnderIntegrals]
  constructor
  · constructor
    · exact H_cdi.1.1
    · constructor
      · exact And.intro H_cdi.left.left  H_cdi.left.right
      · constructor
        · intros H H_contra
          exfalso
          exact at_idx_over H_contra (Nat.not_lt_zero _)
        · intros H H_contra
          exfalso
          exact at_idx_over H_contra (Nat.not_lt_zero _)
  · intro y
    apply can_diff_under_ints_of_all_pdfs_std
    · exact H_std
    · exact H_cdi.2 y

| (⟨(ref, .(shape)), [(parent₁, .(shape)), (parent₂, .(shape))], Operator.rand (rand.op.mvn shape)⟩ :: nodes), m, tgt, H_std, H_cdi => by
  simp [allPdfsStd] at H_std

-- end
end certigrad
