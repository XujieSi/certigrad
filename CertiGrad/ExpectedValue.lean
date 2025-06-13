/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Expected values.
-/
import CertiGrad.Sprog
import CertiGrad.Graph
import CertiGrad.Tfacts
import CertiGrad.ComputeGrad
import CertiGrad.Tcont
import CertiGrad.Predicates
import CertiGrad.Tactics

namespace certigrad
namespace E
open sprog List

lemma E_ret {oshape : S} : Π {shapes : List S} (xs : Dvec T shapes) (f : Dvec T shapes → T oshape), E (sprog.ret xs) f = f xs
| [], ⟦⟧, f => rfl
| [d], ⟦x⟧, f => rfl
| (d₁::d₂::ds), (x₁ ::: x₂ ::: xs), f => rfl

lemma E_bind {oshape : S} : Π {shapes₁ shapes₂ : List S} (start : sprog shapes₁) (rest : Dvec T shapes₁ → sprog shapes₂) (f : Dvec T shapes₂ → T oshape),
  E (sprog.bind start rest) f = (E start) (λ (x : Dvec T shapes₁) => E (rest x) f)
| shapes₁, [], start, rest, f                => rfl
| shapes₁, [s], start, rest, f               => rfl
| shapes₁, (s₁::s₂::shapes₂), start, rest, f => rfl

noncomputable def is_eintegrable {oshape : S} : Π {shapes : List S}, sprog shapes → (Dvec T shapes → T oshape) → Prop
| shapes, (@sprog.ret .(shapes) xs), f => true

| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f =>
  is_eintegrable start (λ (x : Dvec T shapes₁) => E (rest x) f) ∧ ∀ (x : Dvec T shapes₁), is_eintegrable (rest x) f

| [oshape], (@sprog.prim ishapes .(oshape) pd args), f => T.is_integrable (λ (x : T oshape) => pd.pdf args x • f ⟦x⟧)

lemma is_eintegrable_ret {oshape : S} : Π {shapes : List S} (xs : Dvec T shapes) (f : Dvec T shapes → T oshape), is_eintegrable (sprog.ret xs) f = true
| [], ⟦⟧, f => rfl
| [d], ⟦x⟧, f => rfl
| (d₁::d₂::ds), (x₁ ::: x₂ ::: xs), f => rfl

lemma is_eintegrable_bind {oshape : S} : Π {shapes₁ shapes₂ : List S} (start : sprog shapes₁) (rest : Dvec T shapes₁ → sprog shapes₂) (f : Dvec T shapes₂ → T oshape),
  is_eintegrable (sprog.bind start rest) f = (is_eintegrable start (λ (x : Dvec T shapes₁) => E (rest x) f) ∧ ∀ (x : Dvec T shapes₁), is_eintegrable (rest x) f)
| shapes₁, [], start, rest, f                => rfl
| shapes₁, [s], start, rest, f               => rfl
| shapes₁, (s₁::s₂::shapes₂), start, rest, f => rfl

lemma E_add {fshape : S} : Π {shapes : List S} (d : sprog shapes) (f₁ f₂ : Dvec T shapes → T fshape),
  is_eintegrable d f₁ → is_eintegrable d f₂ →
  E d (λ x => f₁ x + f₂ x) = E d f₁ + E d f₂
  | shapes, (@sprog.ret .(shapes) xs), f₁, f₂, Hf₁, Hf₂ => by simp only [E_ret]
  | shapes, (@sprog.bind shapes₁ .(shapes) start rest), f₁, f₂, Hf₁, Hf₂ =>
      have H₁ : ∀ x, is_eintegrable (rest x) f₁ := by
        simp only [is_eintegrable_bind] at Hf₁
        exact Hf₁.2
      have H₂ : ∀ x, is_eintegrable (rest x) f₂ := by
          simp only [is_eintegrable_bind] at Hf₂
          exact Hf₂.2
      have G₁ : is_eintegrable start fun x => E (rest x) f₁ := by
          simp only [is_eintegrable_bind] at Hf₁
          exact Hf₁.1
      have G₂ : is_eintegrable start fun x => E (rest x) f₂ := by
          simp only [is_eintegrable_bind] at Hf₂
          exact Hf₂.1
      by simp only [E_bind, (λ x => E_add (rest x) _ _ (H₁ x) (H₂ x)), E_add start _ _ G₁ G₂]
  | _, sprog.prim pd args, f₁, f₂, Hf₁, Hf₂ =>
        have H₁ : T.is_dintegrable fun xs => rand.op.pdf pd args xs.head • f₁ xs := by
          unfold T.is_dintegrable Dvec.head
          constructor
          exact Hf₁
          intro x
          exact trivial
        have H₂ : T.is_dintegrable fun xs => rand.op.pdf pd args xs.head • f₂ xs := by
          unfold T.is_dintegrable Dvec.head
          constructor
          exact Hf₂
          intro x
          exact trivial
        by exact T.dintegral_add_middle _ _ _ H₁ H₂


lemma is_eintegrable_add₁ {oshape : S} : Π {shapes : List S} (d : sprog shapes) (f₁ f₂ : Dvec T shapes → T oshape),
  (is_eintegrable d f₁ ∧ is_eintegrable d f₂) → is_eintegrable d (λ x => f₁ x + f₂ x)
| shapes, (@sprog.ret .(shapes) xs), f₁, f₂ => by simp [is_eintegrable_ret]
| [oshape], (@sprog.prim ishapes .(oshape) pd args), f₁, f₂ =>
  -- Use .mp to apply the theorem in the forward direction (P → Q) of the bi-implication (P ↔ Q)
 by apply (T.is_integrable_add_middle _ _ _).mp

| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f₁, f₂ =>
  by
    simp only [is_eintegrable_bind]
    intro H
    let ⟨H₁, H₂⟩ := H
    constructor
    . simp only [(λ x => E_add (rest x) _ _ (H₁.right x) (H₂.right x))]
      apply is_eintegrable_add₁
      apply And.intro H₁.left H₂.left
    . intro x
      apply is_eintegrable_add₁
      apply And.intro (H₁.right x) (H₂.right x)


lemma is_eintegrable_add₂ {oshape : S} : Π {shapes : List S} (d : sprog shapes) (f₁ f₂ : Dvec T shapes → T oshape),
  is_eintegrable d (λ x => f₁ x + f₂ x) → (is_eintegrable d f₁ ∧ is_eintegrable d f₂)
| shapes, (@sprog.ret .(shapes) xs), f₁, f₂ => by simp [is_eintegrable_ret]
| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f₁, f₂ =>
  by
  simp only [is_eintegrable_bind]
  intro H
  let ⟨ H₁, H₂ ⟩ := H
  have H_rest_next: ∀ x, is_eintegrable (rest x) f₁ ∧ is_eintegrable (rest x) f₂ := by
    intro x
    apply is_eintegrable_add₂
    exact H₂ x

  simp only [(λ x => E_add (rest x) f₁ f₂ (H_rest_next x).left (H_rest_next x).right)] at H₁
  constructor
  .
    constructor
    . exact (is_eintegrable_add₂ _ _ _ H₁).left
    . intro x; exact (H_rest_next x).left
  .
    constructor
    .
      exact (is_eintegrable_add₂ _ _ _ H₁).right
    . intro x
      exact (H_rest_next x).right

| [oshape], (@sprog.prim ishapes .(oshape) pd args), f₁, f₂ =>
  by apply (T.is_integrable_add_middle _ _ _).mpr

lemma is_eintegrable_add {oshape : S} : Π {shapes : List S} (d : sprog shapes) (f₁ f₂ : Dvec T shapes → T oshape),
  (is_eintegrable d f₁ ∧ is_eintegrable d f₂) ↔ is_eintegrable d (λ x => f₁ x + f₂ x) := by
  intros shapes d f₁ f₂
  constructor
  . apply is_eintegrable_add₁
  . apply is_eintegrable_add₂

lemma E_congr {shapes : List S} {oshape : S} (d₁ d₂ : sprog shapes) (f : Dvec T shapes → T oshape) (H : d₁ = d₂) :
  E d₁ f = E d₂ f := by rw [H]

lemma E_scale {oshape : S} (α : TReal) : Π {shapes : List S} (d : sprog shapes) (f : Dvec T shapes → T oshape), E d (λ x => α • f x) = α • E d f
| shapes, (@sprog.ret .(shapes) xs), f => by simp only [E_ret]
| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f => by
  simp [E_bind]
  simp [E_scale]

-- Note: The proof above is somewhat unusual here --
| [oshape], (@sprog.prim ishapes .(oshape) pd args), f => by
  unfold E
  exact T.dintegral_scale_middle α _ f

lemma E_scale_mul (α : TReal) : Π {shapes : List S} (d : sprog shapes) (f : Dvec T shapes → TReal), E d (λ x => α • f x) = α • E d f
| shapes, (@sprog.ret .(shapes) xs), f => by simp only [E_ret]
| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f =>
  by
  simp only [E_bind, (λ x => E_scale_mul α (rest x)), E_scale_mul α start]
| [oshape], (@sprog.prim ishapes .(oshape) pd args), f => by
  unfold E
  exact T.dintegral_mul_middle _ _ _

lemma E_fscale {fshape : S} (y : T fshape) : Π {shapes : List S} (d : sprog shapes) (f : Dvec T shapes → TReal), E d (λ x => f x • y) = E d f • y
| shapes, (@sprog.ret .(shapes) xs), f => by simp only [E_ret]
| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f => by
  simp only [E_bind, (λ x => E_fscale y (rest x)), E_fscale y start]
| [oshape], (@sprog.prim ishapes .(oshape) pd args), f => by
  unfold E T.dintegral
  simp [← T.integral_fscale, T.dintegral_scale]


  -- `congr` applies the congruence lemma, reducing the goal to proving equality of the arguments of both sides.
  -- `funext x` applies function extensionality, introducing a variable `x` and reducing the goal to proving equality for all `x`.

  congr
  funext x
  have H: (T.dintegral fun xs => f (x ::: xs) )• y = T.dintegral fun xs => f (x ::: xs) • y := by
    rfl
  rw [← H]
  set a:= T.dintegral fun xs => f (x ::: xs)
  simp [T.smul.def]
  ring

lemma E_neg {oshape : S} : Π {shapes : List S} (d : sprog shapes) (f : Dvec T shapes → T oshape),
  is_eintegrable d f → E d (λ x => - (f x)) = - (E d f)
  --Note that If the first has error, maybe the third has error is the reason --
| shapes, (@sprog.ret .(shapes) xs), f, Hf => by simp only [E_ret]
| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f, Hf =>
  by
  simp only [is_eintegrable_bind] at Hf
  simp only [E_bind, (λ x => E_neg (rest x) _ (Hf.right x)), E_neg start _ Hf.left]

| [oshape], (@sprog.prim ishapes .(oshape) pd args), f, Hf => by
  unfold E
  exact T.dintegral_neg_middle _ f

lemma E_const {shapes : List S} {oshape fshape : S} (op : rand.op shapes oshape) (parents : Dvec T shapes) (H_op_pre : op.pre parents) (y : T fshape) :
  E (sprog.prim op parents) (λ x => y) = y :=
  T.dintegral_const_middle (λ (x : Dvec T [oshape]) => op.pdf parents x.head)
                         (λ (x : Dvec T [oshape]) => op.pdf_pos parents H_op_pre x.head)
                         (op.pdf_int1 parents H_op_pre)
                         y

lemma E_bind_assoc {shapes₁ shapes₂ shapes₃ : List S} {fshape : S}
    (d₁ : sprog shapes₁)
    (d₂ : Dvec T shapes₁ → sprog shapes₂)
    (d₃ : Dvec T shapes₂ → sprog shapes₃)
    (f : Dvec T shapes₃ → T fshape) :
    E (d₁ >>= fun xs₁ => d₂ xs₁ >>= fun xs₂ => d₃ xs₂) f =
    E ((d₁ >>= fun xs₁ => d₂ xs₁) >>= fun xs₂ => d₃ xs₂) f := by
  simp only [E_bind]

lemma E_pull_out_of_sum {X : Type} {ishapes : List S} {oshape fshape : S}
    (op : rand.op ishapes oshape) (parents : Dvec T ishapes) (H_op_pre : op.pre parents)
    (f : X → Dvec T [oshape] → T fshape) :
  ∀ (xs : List X),
  is_eintegrable (sprog.prim op parents) (λ y => sumr (map (λ x => f x y) xs)) →
  sumr (map (λ x => E (sprog.prim op parents) (f x)) xs) = E (sprog.prim op parents) (λ y => sumr (map (λ x => f x y) xs))
  | []      ,H_xs => by unfold sumr map; rw [E_const]; exact H_op_pre
  | (x::xs), H_xs =>
    by
    unfold sumr map
    rw [E_add, E_pull_out_of_sum]
    unfold map sumr at H_xs
    exact (is_eintegrable_add _ _ _).mp H_xs
    exact (is_eintegrable_add _ _ _).mp H_xs

lemma E_k_add {shape : S} (k₁ k₂ : Env → T shape) : ∀ (m : Env) (nodes : List Node),
  isGintegrable  (λ m => ⟦k₁ m⟧) m nodes Dvec.head →
  isGintegrable  (λ m =>  ⟦k₂ m⟧) m nodes Dvec.head →
  E (graph.toDist (λ (m : Env) => ⟦k₁ m + k₂ m⟧) m nodes) Dvec.head
  =
  E (graph.toDist (λ (m : Env) => ⟦k₁ m⟧) m nodes) Dvec.head + E (graph.toDist (λ (m : Env) => ⟦k₂ m⟧) m nodes) Dvec.head
| m, [], Hk₁, Hk₂ => by
  unfold graph.toDist E_ret
  simp

| m, (⟨ref, parents, Operator.det op⟩::nodes), Hk₁, Hk₂ => by
  unfold graph.toDist Operator.det E_ret E_bind
  rw [E_k_add]
  exact Hk₁
  exact Hk₂

| m, (⟨ref, parents, Operator.rand op⟩::nodes), Hk₁, Hk₂ => by
  unfold graph.toDist Operator.toDist
  unfold E at *
  unfold T.dintegral
  simp
  simp [is_gintegrable, dvec.head] at Hk₁ Hk₂

  erw [← T.integral_add _ _ Hk₁.left Hk₂.left]

  apply (congr_arg T.integral)
  apply funext
  intro x
  erw [← T.smul_addr]
  rw [← E_k_add _ _ (Hk₁.right x) (Hk₂.right x)]

lemma E_g_pull_out_of_sum {X : Type} {fshape : S} (f : Env → X → T fshape) :
  ∀ (m : Env) (nodes : List Node) (xs : List X),
  pdfsExistAt nodes m →
  isGintegrable (λ m'=> ⟦sumr (map (λ x => f m' x) xs)⟧) m nodes Dvec.head →
  sumr (map (λ x => E (graph.toDist (λ m'=> ⟦f m' x⟧) m nodes) Dvec.head) xs) = E (graph.toDist (λ m'=> ⟦sumr (map (λ x => f m' x) xs)⟧) m nodes) Dvec.head
| m, [], xs, H_pdfs_exist, H_gint => by simp only [graph.toDist, E_ret, Dvec.head]

| m, (⟨ref, parents, Operator.det op⟩::nodes), xs, H_pdfs_exist, H_gint =>
    unfold graph.to_dist Operator.to_dist
    simp only [E_ret, E_bind]
    apply E_g_pull_out_of_sum
    exact H_pdfs_exist
    exact H_gint

| m, (⟨ref, parents, Operator.rand op⟩::nodes), xs, H_pdfs_exist, H_gint =>
    unfold graph.to_dist Operator
    simp only [E_ret, E_bind]
    rw E_pull_out_of_sum _ _ H_pdfs_exist.left
    apply congr_arg
    apply funext
    intro y
    rw E_g_pull_out_of_sum _ _ _ (H_pdfs_exist.right y.head) (H_gint.right y.head)
    dsimp [is_eintegrable] without Dvec.head
    dsimp [is_gintegrable] without Dvec.head at H_gint,
    simp only [λ (y : Dvec T [ref.2]), E_g_pull_out_of_sum _ _ _ (H_pdfs_exist.right y.head) (H_gint.right y.head)]
    exact H_gint.left

end E
open List
open E
-- TODO(dhs): restructure the library
lemma is_gintegrable_k_add {shape : S} (k₁ k₂ : Env → T shape) : Π (m : Env) (nodes : List Node),
  (isGintegrable (λ m => ⟦k₁ m⟧) m nodes Dvec.head ∧ isGintegrable (λ m => ⟦k₂ m⟧) m nodes Dvec.head) ↔ isGintegrable (λ m => ⟦k₁ m + k₂ m⟧) m nodes Dvec.head
| _, [] => by
    dsimp [isGintegrable]
    constructor
    . intro H; exact trivial
    . intro H; exact (And.intro trivial trivial)

| m, (⟨ref, parents, Operator.det op⟩ :: nodes) => by
    dsimp [isGintegrable]
    apply is_gintegrable_k_add

| m, (⟨ref, parents, Operator.rand op⟩ :: nodes) => by
    dsimp [isGintegrable]
    constructor
    . intro H
      constructor
      . simp only [λ x => E_k_add k₁ k₂ _ _ (H.left.right x) (H.right.right x)]
        apply (T.is_integrable_add_middle _ _ _).mpr
        exact And.intro H.left.left H.right.left
      . intro x
        exact (is_gintegrable_k_add _ _).mp (And.intro (H.left.right x) (H.right.right x))
    . intro H
      have H_kint₁ : ∀ (x : T ref.2), isGintegrable (λ (m : Env) => ⟦k₁ m⟧) (env.insert ref x m) nodes Dvec.head := by
        intro x
        apply (is_gintegrable_k_add _ _).mp (H.right x)
        exact H.left.right x

      have H_kint₂ : ∀ (x : T ref.2), isGintegrable (λ (m : Env) => ⟦k₂ m⟧) (env.insert ref x m) nodes Dvec.head := by
        intro x
        apply (is_gintegrable_k_add _ _).mp (H.right x)
        exact H.left.right x

      constructor
      . simp only [λ x => E_k_add k₁ k₂ _ _ (H.left.right x) (H.right.right x)]
        apply (T.is_integrable_add_middle _ _ _).mpr
        exact And.intro H.left.left H.right.left
      . intro x
        exact (is_gintegrable_k_add _ _).mp (And.intro (H.left.right x) (H.right.right x))



namespace E

lemma E_k_tmulT {shape₁ shape₂ : S} (k : Env → T shape₂) : Π (m : Env) (nodes : List Node) (M : T (shape₁ ++ shape₂)),
  E (graph.toDist (λ (m : Env) => ⟦T.tmulT M (k m)⟧) m nodes) Dvec.head
  =
  T.tmulT M (E (graph.toDist (λ (m : Env) => ⟦k m⟧) m nodes) Dvec.head)
  | m, [], M => by
      unfold graph.toDist E_ret E
      simp only [Dvec.head]

  | m, (⟨ref, parents, Operator.det op⟩::nodes), M => by
      unfold graph.toDist Operator.toDist E
      simp only [E_ret, E_bind]
      rw [E_k_tmulT]

  | m, (⟨ref, parents, Operator.rand op⟩::nodes), M => by
      unfold graph.toDist Operator E
      simp only [E_bind]
      rw [E_k_tmulT]
      rw [T.dintegral_tmulT_middle]

end E

lemma is_gintegrable_tmulT {ishape oshape : S} (M : T (ishape ++ oshape)) (k : Env → T oshape) :
  Π (inputs : Env) (nodes : List Node),
  isGintegrable (λ (m : Env) => ⟦k m⟧) inputs nodes Dvec.head ↔ isGintegrable (λ (m : Env) => ⟦T.tmulT M (k m)⟧) inputs nodes Dvec.head
| inputs, [] => by
    dsimp [isGintegrable]
    constructor
    . intro H; exact trivial
    . intro H; exact trivial

| inputs, (⟨ref, parents, Operator.det op⟩ :: nodes) => by
    dsimp [isGintegrable]
    apply is_gintegrable_tmulT

| inputs, (⟨ref, parents, Operator.rand op⟩ :: nodes) => by
    dsimp [isGintegrable]
    constructor
    . intro H
      constructor
      . simp only [E.E_k_tmulT]
        apply (T.is_integrable_tmulT_middle _ _ _).mpr
        exact H.left
      . intro x
        exact (is_gintegrable_tmulT _ _).mp (H.right x)
    . intro H
      constructor
      . simp only [E.E_k_tmulT]
        apply (T.is_integrable_tmulT_middle _ _ _).mpr
        exact H.left
      . intro x
        exact (is_gintegrable_tmulT _ _).mp (H.right x)


lemma is_gintegrable_of_sumr_map {X : Type} [Inhabited X] {shape : S} (k : Env → X → T shape) (m : Env) (nodes : List Node)
  : ∀ (xs : List X) (H_gint : isGintegrable (λ (m : Env) => ⟦sumr (map (k m) xs)⟧) m nodes Dvec.head) (x : X), x ∈ xs →
      isGintegrable (λ (m : Env) => ⟦k m x⟧) m nodes Dvec.head
| [], _, _, H_in => by
    simp only [not_mem_nil] at H_in
    exact H_in

| (x::xs), H_gint, y, H_in =>
    unfold sumr map at H_gint
    cases (eq_or_mem_of_mem_cons H_in) with H_eq H_in_rec
    . subst H_eq
      exact (is_gintegrable_k_add _ _ _ _).mp H_gint
    . apply is_gintegrable_of_sumr_map xs (is_gintegrable_k_add _ _ _ _).mp H_gint y H_in_rec

namespace E
open sprog list

lemma E_k_scale {shape : S} (k : env → ℝ) (y : T shape) : Π (m : env) (nodes : list node),
  E (graph.to_dist (λ (m : env), ⟦k m ⬝ y⟧) m nodes) dvec.head
  =
  E (graph.to_dist (λ (m : env), ⟦k m⟧) m nodes) dvec.head ⬝ y
| m []                                        := begin dunfold graph.to_dist, simp [E_ret] end
| m (⟨ref, parents, operator.det op⟩::nodes)  :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_ret],
rw E_k_scale
end

| m (⟨ref, parents, operator.rand op⟩::nodes) :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_k_scale, E_fscale],
end

lemma E_k_sum_map {X : Type} [inhabited X] {shape : S} (k : env → X → T shape) : Π (m : env) (nodes : list node) (xs : list X),
  pdfs_exist_at nodes m →
  is_gintegrable (λ m, ⟦sumr (map (k m) xs)⟧) m nodes dvec.head →
  E (graph.to_dist (λ (m : env), ⟦sumr (map (k m) xs)⟧) m nodes) dvec.head
  =
  sumr (map (λ (x : X), E (graph.to_dist (λ (m : env), ⟦k m x⟧) m nodes) dvec.head) xs)
| m [] xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
simp [E_ret, dvec.head],
end

| m (⟨ref, parents, operator.det op⟩::nodes) xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
dsimp [pdfs_exist_at] at H_pdfs,
simp [E_ret, E_bind, dvec.head],
rw E_k_sum_map _ _ _ H_pdfs H_ints
end

| m (⟨ref, parents, operator.rand op⟩::nodes) xs H_pdfs H_ints :=
begin
dunfold graph.to_dist operator.to_dist,
simp only [E_bind],
dunfold pdfs_exist_at at H_pdfs,
dsimp [is_gintegrable] at H_ints,
simp only [λ x, E_k_sum_map _ _ xs (H_pdfs^.right x) (H_ints^.right x)],

rw E_pull_out_of_sum op _ H_pdfs^.left,
dunfold is_eintegrable,

-- TODO(dhs): bad form to do induction in the middle of a proof
-- could make this a lemma
induction xs with x xs IHxs,
{ dunfold sumr map, simp only [T.smul_zero], exact T.is_integrable_zero },
{
dunfold sumr map,
apply iff.mp (T.is_integrable_add_middle (rand.op.pdf op (env.get_ks parents m))
                                      (λ x_1, E (graph.to_dist (λ (m : env), ⟦k m x⟧) (env.insert ref (dvec.head ⟦x_1⟧) m) nodes) dvec.head)
                                      (λ x_1, sumr (map (λ (x : X), E (graph.to_dist (λ (m : env), ⟦k m x⟧) (env.insert ref (dvec.head ⟦x_1⟧) m) nodes) dvec.head) xs))),
dunfold sumr map at H_ints,
simp only [λ x_1, E_k_add (λ m, k m x) (λ m, sumr (map (k m) xs)) (env.insert ref x_1 m) nodes
                      (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right x_1))^.left
                      (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right x_1))^.right] at H_ints,

split,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_ints^.left)^.left,
apply IHxs,
split,
exact (iff.mpr (T.is_integrable_add_middle _ _ _) H_ints^.left)^.right,
intro y,
exact (iff.mpr (is_gintegrable_k_add _ _ _ _) (H_ints^.right y))^.right,
}
end

lemma E_continuous {ishapes : List S} {oshape tshape fshape : S} (pd : rand.op ishapes oshape) (args : T tshape → Dvec T ishapes)
                   (f : Dvec T [oshape] → T tshape → T fshape) (θ : T tshape) :
  (∀ x, T.is_continuous (λ θ₀ => pd^.pdf (args θ₀) x) θ) →
  (∀ x, T.is_continuous (f x) θ) →
  T.is_continuous (λ θ₀ => E (sprog.prim pd (args θ₀)) (λ x₀ => f x₀ θ₀)) θ :=
assume (H_pdf_continuous : ∀ x, T.is_continuous (λ θ₀ => pd^.pdf (args θ₀) x) θ)
       (H_f_continuous : ∀ x, T.is_continuous (f x) θ),
begin
dunfold E T.dintegral,
apply T.integral_continuous,
intro x,
apply T.continuous_scale_fs,
apply H_pdf_continuous,
apply H_f_continuous
end

lemma E_move_fn_to_continuation (shapes : List S) (fshape : S)
                              (k : env → Dvec T shapes) (f : Dvec T shapes → T fshape) :
  Π (inputs : env) (nodes : List node), E (graph.to_dist k inputs nodes) f = E (graph.to_dist (λ m => ⟦f (k m)⟧) inputs nodes) dvec.head

| m [] :=
begin dunfold graph.to_dist, simp [E_ret] end

| m (⟨ref, parents, op⟩::nodes) :=
begin dunfold graph.to_dist, simp [E_bind], apply congr_arg, apply funext, intro x, rw E_move_fn_to_continuation end

lemma E_of_lookup : ∀ {nodes : List Node} {inputs : Env} {loss : Reference} {val : T loss.2},
  loss ∉ map node.ref nodes →
  pdfs_exist_at nodes (env.insert loss val inputs) →
  E (graph.to_dist (λ (m : Env) => ⟦env.get loss m⟧) (env.insert loss val inputs) nodes) Dvec.head = val
| [], inputs, loss, val, H_loss_unused, H_pdfs_exist_at => by
    unfold graph.toDist
    simp [E_ret]
    unfold dvec.head
    rw [env.get_insert_same]

| (⟨ref, parents, operator.det op⟩::nodes) inputs loss val H_loss_unused H_pdfs_exist_at =>
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind, E_ret],
assertv H_loss_neq_ref : loss ≠ ref := ne_of_not_mem_cons H_loss_unused,
assertv H_loss_unused_next : loss ∉ map node.ref nodes := not_mem_of_not_mem_cons H_loss_unused,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref),
dunfold pdfs_exist_at at H_pdfs_exist_at,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref) at H_pdfs_exist_at,
exact (E_of_lookup H_loss_unused_next H_pdfs_exist_at),
end

| (⟨ref, parents, operator.rand op⟩::nodes) inputs loss val H_loss_unused H_pdfs_exist_at =>
begin
dunfold graph.to_dist operator.to_dist,
simp [E_bind],
assertv H_loss_neq_ref : loss ≠ ref := ne_of_not_mem_cons H_loss_unused,
assertv H_loss_unused_next : loss ∉ map node.ref nodes := not_mem_of_not_mem_cons H_loss_unused,
assert H_inside :
E (sprog.prim op (env.get_ks parents (env.insert loss val inputs)))
    (λ (x_1 : dvec T [ref^.snd]),
       E
         (graph.to_dist (λ (m : env), ⟦env.get loss m⟧)
            (env.insert ref (dvec.head x_1) (env.insert loss val inputs))
            nodes)
         dvec.head)
=
E (sprog.prim op (env.get_ks parents (env.insert loss val inputs)))
    (λ (x_1 : dvec T [ref^.snd]), val),
{
apply congr_arg, apply funext, intro x,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref),
dunfold pdfs_exist_at at H_pdfs_exist_at,
note H_pdfs_exist_at_next := H_pdfs_exist_at^.right x^.head,
dsimp [pdfs_exist_at] at H_pdfs_exist_at_next,
rw env.insert_insert_flip _ _ _ (ne.symm H_loss_neq_ref) at H_pdfs_exist_at_next,
exact (E_of_lookup H_loss_unused_next H_pdfs_exist_at_next)
},

rw H_inside, clear H_inside,
dunfold E T.dintegral dvec.head, dsimp,
rw T.integral_fscale,

assert H_pdf_1 : ∫ (λ (x : T (ref^.snd)), rand.op.pdf op (env.get_ks parents (env.insert loss val inputs)) (dvec.head ⟦x⟧)) = 1,
  { exact op^.pdf_int1 _ H_pdfs_exist_at^.left },

dunfold dvec.head at H_pdf_1,
rw H_pdf_1, rw T.one_smul
end

end E

end certigrad
