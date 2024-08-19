
-- -- import system.io data.list.set

import Lean
-- import Init.Core


-- meta constant io.mkdir (s : string) [io.interface] : io nat

-- class has_smul (α β : Type) where
--   smul : α → β → β

-- def smul {α β : Type} [has_smul α β] : α → β → β := has_smul.smul
-- -- infixl ` ⬝ ` := smul
-- infixl:75 " ⬝ " => smul


def pextt {P : Prop} : P → (P = True) := λ Hp => propext (iff_true_intro Hp)
def pextf {P : Prop} : ¬ P → (P = False) := λ Hnp => propext (Iff.intro (λ Hp => Hnp Hp) (λ Hf => False.rec _ Hf))

-- namespace nat

-- -- theorem bit1_ne_bit0_eq {n m : ℕ} : (bit1 n ≠ bit0 m) = true := pextt (nat.bit1_ne_bit0 _ _)
-- -- theorem bit0_ne_bit1_eq {n m : ℕ} : (bit0 n ≠ bit1 m) = true := pextt (nat.bit0_ne_bit1 _ _)

-- theorem bit0_inj_eq {n m : ℕ} : (bit0 n ≠ bit0 m) = (n ≠ m) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- intros H_ne H_eq,
-- exact H_ne (nat.bit0_inj H_eq)
-- end

-- theorem bit1_inj_eq {n m : ℕ} : (bit1 n ≠ bit1 m) = (n ≠ m) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- intros H_ne H_eq,
-- exact H_ne (nat.bit1_inj H_eq)
-- end

-- theorem zero_ne_bit0_eq {n : ℕ} : (0 ≠ bit0 n) = (n ≠ 0) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- apply nat.zero_ne_bit0
-- end

-- theorem bit0_ne_zero_eq {n : ℕ} : (bit0 n ≠ 0) = (n ≠ 0) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- apply nat.bit0_ne_zero
-- end

-- theorem one_ne_bit1_eq {n : ℕ} : (1 ≠ bit1 n) = (n ≠ 0) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- apply nat.one_ne_bit1
-- end

-- theorem bit1_ne_one_eq {n : ℕ} : (bit1 n ≠ 1) = (n ≠ 0) :=
-- begin
-- apply propext,
-- split,
-- intros H_ne H_eq,
-- subst H_eq,
-- exact H_ne rfl,
-- apply nat.bit1_ne_one
-- end

-- theorem one_ne_bit0_eq (n : ℕ) : (1 ≠ bit0 n) = true := pextt (nat.one_ne_bit0 _)
-- theorem bit0_ne_one_eq (n : ℕ) : (bit0 n ≠ 1) = true := pextt (nat.bit0_ne_one _)

-- theorem zero_ne_bit1_eq (n : ℕ) : (0 ≠ bit1 n) = true := pextt (nat.zero_ne_bit1 _)
-- theorem bit1_ne_zero_eq (n : ℕ) : (bit1 n ≠ 0) = true := pextt (nat.bit1_ne_zero _)

-- theorem zero_ne_one_eq : (0 ≠ 1) = true := pextt nat.zero_ne_one
-- theorem one_ne_zero_eq : (1 ≠ 0) = true := pextt nat.one_ne_zero

-- end nat

-- namespace prod
-- section lt
-- universes u v
-- variables {A : Type u} [A_deceq : decidable_eq A] [A_lt : has_lt A] [A_dec_lt : decidable_rel (@has_lt.lt A _)]
--           {B : Type v} [B_lt : has_lt B] [B_dec_lt : decidable_rel (@has_lt.lt B _)]

-- include A_deceq A_lt A_dec_lt B_lt B_dec_lt

-- def less_than : A × B → A × B → Prop
-- | ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := if x₁ < x₂ then true else (if x₂ < x₁ then false else (y₁ < y₂))

-- instance : has_lt (A × B) := ⟨less_than⟩

-- def decidable_less_than : ∀ (p q : A × B), decidable (p < q)
-- | ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := show decidable (if x₁ < x₂ then true else (if x₂ < x₁ then false else (y₁ < y₂))), by apply_instance

-- instance : decidable_rel (@has_lt.lt (A × B) _) := decidable_less_than

-- end lt
-- end prod

-- theorem pair_neq_of_neq₁ {X Y : Type} {x₁ x₂ : X} {y₁ y₂ : Y} : x₁ ≠ x₂ → (x₁, y₁) ≠ (x₂, y₂) :=
-- assume (H : x₁ ≠ x₂) (H_contra : (x₁, y₁) = (x₂, y₂)),
-- by { injection H_contra with Hx Hy, exact H Hx }

-- namespace list
-- section lt
-- variables {A : Type*} [A_deceq : decidable_eq A] [A_lt : has_lt A] [A_dec_lt : decidable_rel (@has_lt.lt A _)]

-- include A_deceq A_lt A_dec_lt

-- def less_than : list A → list A → Prop
-- | []      (y::ys) := true
-- | _       []      := false
-- | (x::xs) (y::ys) := x < y ∨ (x = y ∧ less_than xs ys)

-- instance : has_lt (list A) := ⟨less_than⟩

-- def decidable_less_than : ∀ (xs ys : list A), decidable (xs < ys)
-- | []      (y::ys) := decidable.true
-- | []       []     := decidable.false
-- | (x::xs)  []     := decidable.false
-- | (x::xs) (y::ys) :=
-- show decidable (x < y ∨ (x = y ∧ less_than xs ys)), from
-- have H_lt : decidable (less_than xs ys), by apply decidable_less_than,
-- by apply_instance

-- instance : decidable_rel (@has_lt.lt (list A) _) := decidable_less_than

-- end lt

-- def p1 {X Y : Type} : list (X × Y) → list X
-- | [] := []
-- | (xy::xys) := xy.1 :: p1 xys

-- def p2 {X Y : Type} : list (X × Y) → list Y
-- | [] := []
-- | (xy::xys) := xy.2 :: p2 xys

-- theorem length_p1_same {X Y : Type} : ∀ (xs : list (X × Y)), length xs^.p1 = length xs
-- | []      := rfl
-- | (x::xs) := begin dsimp [length, p1], rw length_p1_same end

-- theorem length_p2_same {X Y : Type} : ∀ (xs : list (X × Y)), length xs^.p2 = length xs
-- | []      := rfl
-- | (x::xs) := begin dsimp [length, p2], rw length_p2_same end

-- def sumr {α : Type} [has_add α] [has_zero α] : list α → α
-- | [] := 0
-- | (x::xs) := x + sumr xs

-- def sumrd {α : Type} [has_add α] (d : α) : list α → α
-- | [] := d
-- | (x::xs) := x + sumrd xs

-- theorem sumrd_sumr {α : Type} [add_comm_group α] (d : α) : ∀ (xs : list α), sumrd d xs = d + sumr xs
-- | []      := begin dunfold sumrd sumr, rw add_zero end
-- | (x::xs) := begin dunfold sumrd sumr, rw sumrd_sumr, rw [-add_assoc, -add_assoc], rw add_comm x d end

-- def sumr₁ {α : Type} [has_add α] [has_zero α] : list α → α
-- | [] := 0
-- | [x] := x
-- | (x::y::xs) := x + sumr₁ (y::xs)

-- theorem sumr_sumr₁ {α : Type} [add_group α] : ∀ (xs : list α), sumr₁ xs = sumr xs
-- | [] := rfl
-- | [x] := begin dunfold sumr sumr₁, rw add_zero, end
-- | (x::y::xs) := begin dunfold sumr sumr₁, rw sumr_sumr₁, reflexivity end

-- def prod {α : Type*} [has_mul α] [has_one α] : list α → α :=
-- foldr has_mul.mul 1

theorem append_single {α : Type} (x : α) (xs : List α) : [x] ++ xs = x :: xs := rfl

theorem append_nil_left {α : Type} (xs : List α) : [] ++ xs = xs := rfl

-- theorem in_filter {α : Type*} (P : α → Prop) [decidable_pred P] : Π (xs : list α) (x : α), x ∈ xs → P x → x ∈ filter P xs
-- | []      x H_x_in HPx := H_x_in
-- | (y::ys) x H_x_in HPx :=
-- have Hx : x = y ∨ x ∈ ys, from iff.mp (mem_cons_iff _ _ _) H_x_in,
-- have Hy : P y ∨ ¬ (P y), from decidable.em _,
-- begin
-- dunfold filter,
-- cases Hx with H_eq H_in,
-- { subst H_eq, simp [HPx] },
-- cases Hy with HPy HnPy,
-- { simp [HPy], exact or.inr (in_filter _ _ H_in HPx) },
-- { simp [HnPy], exact in_filter _ _ H_in HPx }
-- end

-- theorem of_in_filter {α : Type*} (P : α → Prop) [decidable_pred P] : Π (xs : list α) (x : α), x ∈ filter P xs → x ∈ xs ∧ P x
-- | []      x H_x_in := false.rec _ (not_mem_nil _ H_x_in)
-- | (y::ys) x H_x_in :=
-- have Hy : P y ∨ ¬ (P y), from decidable.em _,
-- begin
-- cases Hy with HPy HnPy,
-- dunfold filter at H_x_in,
-- simp [HPy] at H_x_in,
-- split,

-- cases H_x_in with H_eq H_in,
-- { subst H_eq, apply mem_cons_self },
-- { apply mem_cons_of_mem, exact (of_in_filter _ _ H_in)^.left },

-- cases H_x_in with H_eq H_in,
-- { subst H_eq, exact HPy  },
-- { exact (of_in_filter _ _ H_in)^.right  },

-- dunfold filter at H_x_in,
-- simp [HnPy] at H_x_in,
-- split,
-- apply mem_cons_of_mem, exact (of_in_filter _ _ H_x_in)^.left,
-- exact (of_in_filter _ _ H_x_in)^.right
-- end

-- def miota : ℕ → ℕ → list ℕ
-- | i 0     := []
-- | i (k+1) := i :: miota (i+1) k

-- def riota : ℕ → list ℕ
-- | 0 := []
-- | (n+1) := n :: riota n

-- theorem in_riota_lt : ∀ {idx n : ℕ}, idx ∈ riota n → idx < n
-- | idx 0     H_mem := false.rec _ (not_mem_nil (riota 0) H_mem)
-- | idx (n+1) H_mem :=
-- begin
-- dsimp [riota, list.mem] at H_mem,
-- cases H_mem with H_idx_eq H_mem,
-- { rw H_idx_eq, apply nat.lt_succ_self },
-- apply nat.lt.step,
-- apply in_riota_lt,
-- exact H_mem
-- end

-- theorem map_compose {X Y Z : Type} (f : X → Y) (g : Y → Z) (xs : list X) : map g (map f xs) = map (λ x, g (f x)) xs := by apply map_map

-- theorem map_congr_fn {X Y : Type} (f g : X → Y) (xs : list X) : f = g → map f xs = map g xs := begin intro H, rw H end
-- theorem map_congr_fn_pred {X Y : Type} (f g : X → Y) : Π (xs : list X) (H : ∀ x, x ∈ xs → f x = g x), map f xs = map g xs
-- | []      H := rfl
-- | (x::xs) H :=
--   show f x :: map f xs = g x :: map g xs, from
--   have H_x : x ∈ x :: xs, by apply mem_cons_self,
--   have H_rest : ∀ x, x ∈ xs → f x = g x,
--     begin intros y H_y_in_xs, apply H, apply mem_cons_of_mem, exact H_y_in_xs end,
--   begin rw H x H_x, rw (map_congr_fn_pred xs H_rest) end

-- def dnth {α : Type*} [inhabited α] : list α → nat → α
-- | []       n     := default α
-- | (a :: l) 0     := a
-- | (a :: l) (n+1) := dnth l n

-- theorem p1_dnth {α β : Type*} [inhabited α] [inhabited β] : ∀ (xs : list (α × β)) (idx : ℕ), (dnth xs idx).1 = dnth (p1 xs) idx
-- | []      _       := rfl
-- | (x::xs) 0       := rfl
-- | (x::xs) (idx+1) := begin dsimp [p1, dnth], apply p1_dnth end

-- theorem p2_dnth {α β : Type*} [inhabited α] [inhabited β] : ∀ (xs : list (α × β)) (idx : ℕ), (dnth xs idx).2 = dnth (p2 xs) idx
-- | []      _       := rfl
-- | (x::xs) 0       := rfl
-- | (x::xs) (idx+1) := begin dsimp [p2, dnth], apply p2_dnth end

-- def at_idx {X : Type} [inhabited X] (xs : list X) (idx : ℕ) (x : X) : Prop :=
--   idx < length xs ∧ x = dnth xs idx

-- inductive elem_at_idx {X : Type} : Π (xs : list X) (idx : ℕ) (x : X), Prop
-- | base : ∀ (xs : list X) (x : X), elem_at_idx (x::xs) 0 x
-- | step : ∀ (xs : list X) (x y : X) (idx : ℕ), elem_at_idx xs idx y → elem_at_idx (x::xs) (idx+1) y


-- theorem elem_at_idx_of_at_idx {X : Type} [inhabited X] : ∀ {xs : list X} {idx : ℕ} {x : X},
--   at_idx xs idx x → elem_at_idx xs idx x
-- | [] _ _ H_at_idx := false.rec _ (nat.not_lt_zero _ H_at_idx^.left)
-- | (x::xs) 0       x₀ H_at_idx := by { dsimp [at_idx, dnth] at H_at_idx, rw H_at_idx^.right, constructor }
-- | (x::xs) (idx+1) x₀ H_at_idx :=
-- begin
-- dsimp [at_idx, dnth] at H_at_idx,
-- apply elem_at_idx.step,
-- apply elem_at_idx_of_at_idx,
-- apply and.intro,
-- exact nat.lt_of_succ_lt_succ H_at_idx^.left,
-- exact H_at_idx^.right
-- end

-- theorem at_idx_0 {α : Type*} [inhabited α] {x : α} {xs : list α} : at_idx (x::xs) 0 x :=
-- begin dunfold at_idx, split, exact nat.zero_lt_succ (length xs), reflexivity end

-- theorem at_idx_inj {α : Type*} [inhabited α] {x x₁ x₂ : α} {xs : list α} : at_idx (x::xs) 0 x₁ → at_idx (x::xs) 0 x₂ → x₁ = x₂ :=
-- begin dunfold at_idx, intros H₁ H₂, rw [H₁^.right, H₂^.right] end

-- theorem at_idx_of_cons {α : Type*} [inhabited α] {x : α} {xs : list α} {y : α} {idx : ℕ} :
--   at_idx (x::xs) (idx+1) y → at_idx xs idx y :=
-- begin
-- dunfold at_idx,
-- intro H,
-- cases H with H_lt H_dnth,
-- split,
-- exact nat.lt_of_succ_lt_succ H_lt,
-- rw H_dnth, reflexivity
-- end

-- theorem at_idx_cons {α : Type*} [inhabited α] {x : α} {xs : list α} {y : α} {idx : ℕ} :
--   at_idx xs idx y → at_idx (x::xs) (idx+1) y :=
-- begin
-- dunfold at_idx,
-- intro H,
-- cases H with H_lt H_dnth,
-- split,
-- exact nat.succ_lt_succ H_lt,
-- rw H_dnth, reflexivity
-- end

-- theorem at_idx_p1 {α β : Type} [inhabited α] [inhabited β] {xs : list (α × β)} {x : α × β} {idx : ℕ} :
--   at_idx xs idx x → at_idx xs^.p1 idx x.1 :=
-- begin
-- intro H_at_idx,
-- cases H_at_idx with H_lt H_eq,
-- apply and.intro,
-- rw length_p1_same, exact H_lt,
-- rw H_eq,
-- apply p1_dnth
-- end

-- theorem at_idx_p2 {α β : Type} [inhabited α] [inhabited β] {xs : list (α × β)} {x : α × β} {idx : ℕ} :
--   at_idx xs idx x → at_idx xs^.p2 idx x.2 :=
-- begin
-- intro H_at_idx,
-- cases H_at_idx with H_lt H_eq,
-- apply and.intro,
-- rw length_p2_same, exact H_lt,
-- rw H_eq,
-- apply p2_dnth
-- end

-- theorem mem_of_at_idx {α : Type*} [inhabited α] {x : α} {xs : list α} {idx : ℕ} : at_idx xs idx x → x ∈ xs :=
-- begin
-- intro H_at_idx,
-- assert H_elem_at_idx : elem_at_idx xs idx x, { exact elem_at_idx_of_at_idx H_at_idx },
-- clear H_at_idx,
-- induction H_elem_at_idx with xs x xs idx' x y H_elem_at_idx IH,
-- apply mem_cons_self,
-- apply mem_cons_of_mem,
-- exact IH
-- end

-- theorem at_idx_over {X : Type} [inhabited X] {xs : list X} {idx : ℕ} {x : X} : at_idx xs idx x → ¬ (idx < length xs) → false :=
-- assume H_at_idx H_idx_big, H_idx_big H_at_idx^.left

-- instance decidable_at_idx {α : Type*} [decidable_eq α] [inhabited α] (xs : list α) (idx : ℕ) (x : α) : decidable (at_idx xs idx x) :=
-- if H : idx < length xs ∧ x = dnth xs idx then decidable.is_true H else decidable.is_false H

-- theorem mem_of_cons_same {α : Type*} {x : α} {xs : list α} : x ∈ x::xs := by { apply or.inl, reflexivity }

-- definition all_prop {α : Type*} (p : α → Prop) (l : list α) : Prop :=
-- foldr (λ a r, p a ∧ r) true l

-- def rcons {α : Type*} (a : α) : list α → list α
-- | []        := [a]
-- | (x :: xs) := x :: (rcons xs)

-- def dnth_all {A : Type} [inhabited A] (idxs : list ℕ) (xs : list A) : list A := map (λ idx, dnth xs idx) idxs

-- theorem mem_not_mem_neq {X : Type*} {x₁ x₂ : X} {xs : list X} : x₁ ∈ xs → x₂ ∉ xs → x₁ ≠ x₂ :=
-- begin
-- intros H_in H_nin,
-- intro H_eq,
-- subst H_eq,
-- exact H_nin H_in
-- end

-- theorem nodup_cons_neq {X : Type} {x₁ x₂ : X} {xs : list X} : x₂ ∈ xs → nodup (x₁ :: xs) → x₁ ≠ x₂ :=
-- assume H_in H_nd,
-- have H_nin : x₁ ∉ xs, from not_mem_of_nodup_cons H_nd,
-- ne.symm $ mem_not_mem_neq H_in H_nin

-- theorem nodup_at_idx_neq {A : Type} [inhabited A] {x : A} {xs : list A} {y : A} {idx : ℕ} :
--   nodup (x::xs) → at_idx (x::xs) (idx+1) y → y ≠ x :=
-- begin
-- intros H_nd H_at_idx,
-- note H_at_idx' := at_idx_of_cons H_at_idx,
-- assert H_in_xs : y ∈ xs,
-- apply mem_of_at_idx H_at_idx',
-- apply ne.symm,
-- apply nodup_cons_neq H_in_xs H_nd,
-- end

-- theorem sublist_cons_nil {X : Type*} {xs : list X} {x : X} : ¬ (x :: xs <+ []) :=
-- begin
-- intro H_contra,
-- note H := list.eq_nil_of_sublist_nil H_contra,
-- injection H
-- end

-- theorem disjoint_of_sublist_left {α : Type*} {l₁ l₂ l : list α} : l₁ <+ l → disjoint l l₂ → disjoint l₁ l₂ :=
-- λ ss d x xinl₁, d (subset_of_sublist ss xinl₁)

-- theorem disjoint_of_sublist_right {α : Type*} {l₁ l₂ l : list α} : l₂ <+ l → disjoint l₁ l → disjoint l₁ l₂ :=
-- λ ss d x xinl xinl₁, d xinl (subset_of_sublist ss xinl₁)

-- theorem nodup_append_sublist₁ {X : Type*} {ys zs : list X} (xs : list X) : nodup (ys ++ zs) → xs <+ ys → nodup (xs ++ zs) :=
-- assume H_nd H_sl,
-- have H_nd_xs : nodup xs, from nodup_of_sublist H_sl (nodup_of_nodup_append_left H_nd),
-- have H_nd_zs : nodup zs, from nodup_of_nodup_append_right H_nd,
-- have H_dj : disjoint xs zs, from disjoint_of_sublist_left H_sl (disjoint_of_nodup_append H_nd),
-- nodup_append_of_nodup_of_nodup_of_disjoint H_nd_xs H_nd_zs H_dj

-- theorem nodup_append_swap {X : Type} {xs₁ xs₂ : list X} {x : X} : nodup (xs₁ ++ (x :: xs₂)) → nodup ((x::xs₁) ++ xs₂) :=
-- by apply list.nodup_head

-- theorem nodup_mem_append₂ {X : Type} {x : X} {xs₁ xs₂ : list X} : nodup (xs₁ ++ xs₂) → x ∈ xs₂ → x ∉ xs₁ :=
-- assume (H_nd : nodup (xs₁ ++ xs₂)) (H₂ : x ∈ xs₂) (H₁ : x ∈ xs₁),
-- have H_dj : disjoint xs₁ xs₂, from disjoint_of_nodup_append H_nd,
-- H_dj H₁ H₂

-- theorem nodup_append_cons {X : Type} {xs₁ xs₂ : list X} {x : X} : nodup (xs₁ ++ (x :: xs₂)) → nodup (xs₁ ++ [x]) :=
-- assume H_nd,
-- have H_nd₁ : nodup xs₁, from nodup_of_nodup_append_left H_nd,
-- have H_dj : disjoint xs₁ (x :: xs₂), from disjoint_of_nodup_append H_nd,
-- have H_nin : x ∉ xs₁, from disjoint_right H_dj mem_of_cons_same,
-- begin apply nodup_app_comm, simp, apply nodup_cons H_nin H_nd₁ end

-- theorem nodup_append_cons_rest {X : Type} {xs₁ xs₂ : list X} {x : X} : nodup (xs₁ ++ (x :: xs₂)) → nodup (xs₁ ++ xs₂) :=
-- assume H_nd, nodup_of_nodup_cons (nodup_head H_nd)

-- theorem nodup_append_neq {X : Type} {xs₁ xs₂ : list X} {x₁ x₂ : X} : x₁ ∈ xs₁ → x₂ ∈ xs₂ → nodup (xs₁ ++ xs₂) → x₁ ≠ x₂ :=
-- assume H₁_in H₂_in H_nd,
-- have H_dj : disjoint xs₁ xs₂, from disjoint_of_nodup_append H_nd,
-- have H₁_nin : x₁ ∉ xs₂, from disjoint_left H_dj H₁_in,
-- ne.symm $ mem_not_mem_neq H₂_in H₁_nin

-- theorem nodup_append_cons_neq {X : Type} {xs : list X} {x₁ x₂ : X} : x₁ ∈ xs → nodup (xs ++ [x₂]) → x₁ ≠ x₂ :=
-- assume H₁_in H_nd,
-- have H_nd' : nodup (x₂ :: xs), from nodup_app_comm H_nd,
-- have H₂_nin : x₂ ∉ xs, from not_mem_of_nodup_cons H_nd',
-- mem_not_mem_neq H₁_in H₂_nin

-- theorem nodup_of_append_cons_cons {X : Type} {xs ys : list X} {y₁ y₂ : X} : nodup (xs ++ (y₁ :: y₂ :: ys)) → nodup (xs ++ (y₁ :: ys)) :=
-- assume H_nd,
-- have H_nd' : nodup (y₁ :: (xs ++ y₂ :: ys)), from nodup_head H_nd,
-- have H₁_nin : y₁ ∉ xs ++ y₂ :: ys, from not_mem_of_nodup_cons H_nd',
-- have H₁_nin₁ : y₁ ∉ xs, from not_mem_of_not_mem_append_left H₁_nin,
-- have H₁_nin₂ : y₁ ∉ ys, from not_mem_of_not_mem_cons (not_mem_of_not_mem_append_right H₁_nin),
-- have H_nd'' : nodup (xs ++ y₂ :: ys), from nodup_of_nodup_cons H_nd',
-- have H_nd''' : nodup (y₂ :: (xs ++ ys)), from nodup_head H_nd'',
-- have H_nd'''' : nodup (xs ++ ys), from nodup_of_nodup_cons H_nd''',
-- nodup_middle (nodup_cons (not_mem_append H₁_nin₁ H₁_nin₂) H_nd'''')

-- theorem map_filter_congr {α β : Type*} {f g : α → β} {p : α → Prop} [decidable_pred p] :
--   ∀ {xs : list α}, (∀ x, x ∈ xs → p x → f x = g x) → map f (filter p xs) = map g (filter p xs)
-- | []      H := rfl
-- | (x::xs) H :=
-- begin
-- dsimp [map, filter],
-- assert H_px_em : p x ∨ ¬ (p x), { exact decidable.em _ },
-- cases H_px_em,
-- { simph, apply congr_arg, apply map_filter_congr,
--   intros y H_y_in_xs H_py,
--   exact H y (mem_cons_of_mem _ H_y_in_xs) H_py },
-- { simph, apply map_filter_congr,
--   intros y H_y_in_xs H_py,
--   exact H y (mem_cons_of_mem _ H_y_in_xs) H_py }
-- end

-- theorem filter_congr {α : Type*} {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
--   ∀ {xs : list α}, (∀ x, x ∈ xs → (p x ↔ q x)) → filter p xs = filter q xs
-- | [] H := rfl

-- | (y::ys) H :=
-- begin
-- dunfold filter,
-- simp [H y mem_of_cons_same],
-- cases (decidable.em (q y)) with Hq Hq,
-- {
-- simp [Hq],
-- rw filter_congr,
-- intros x H_in_ys,
-- apply H,
-- apply mem_cons_of_mem,
-- exact H_in_ys
-- },
-- {
-- simp [Hq],
-- rw filter_congr,
-- intros x H_in_ys,
-- apply H,
-- apply mem_cons_of_mem,
-- exact H_in_ys
-- }
-- end

-- theorem in_riota_cons : ∀ (idx m : ℕ), idx + 1 ∈ riota (m + 1) → idx ∈ riota m
-- | 0       0 :=
-- begin
-- rw zero_add,
-- dunfold riota,
-- exact dec_trivial
-- end

-- | idx       (m+1) :=
-- begin
-- dunfold riota,
-- intro H,
-- cases eq_or_mem_of_mem_cons H with H_in H_in,
-- {
-- assert H_idx_eq_m : idx = m, exact add_right_cancel H_in,
-- subst H_idx_eq_m,
-- simp,
-- },
-- apply list.mem_cons_of_mem,
-- apply in_riota_cons,
-- exact H_in
-- end

-- | idx 0 :=
-- begin
-- dunfold riota,
-- exact dec_trivial
-- end

-- theorem in_riota_self (idx : ℕ) : idx ∈ riota (idx + 1) := by { dunfold riota, apply mem_of_cons_same }

-- theorem nin_neq_dnth {α : Type*} [inhabited α] [decidable_eq α] (x : α) : ∀ xs, x ∉ xs → ∀ idx, idx ∈ riota (list.length xs) → x ≠ dnth xs idx
-- | []      H_nin idx H_in := begin exfalso, exact not_mem_nil _ H_in end

-- | (y::ys) H_nin 0       H_in :=
-- begin
-- dunfold dnth,
-- exact ne_of_not_mem_cons H_nin
-- end

-- | (y::ys) H_nin (idx+1) H_in :=
-- begin
-- dunfold dnth,
-- apply nin_neq_dnth,
-- exact list.not_mem_of_not_mem_cons H_nin,
-- dunfold riota length at H_in,
-- apply in_riota_cons,
-- exact H_in
-- end

-- theorem lt_length_of_in_riota {α : Type*} : Π (xs : list α) (idx : ℕ), idx ∈ riota (length xs) → idx < length xs
-- | [] idx H_in := begin exfalso, exact list.not_mem_nil _ H_in end

-- | (x::xs) 0 H_in :=
-- begin
-- dunfold riota length at H_in,
-- exact dec_trivial
-- end

-- | (x::xs) (idx+1) H_in :=
-- begin
-- dunfold riota length at H_in,
-- apply nat.succ_lt_succ,
-- apply lt_length_of_in_riota,
-- exact in_riota_cons _ _ H_in
-- end

-- theorem dnth_mem_of_lt_length {α : Type*} [inhabited α] : Π (xs : list α) (idx : ℕ), idx < length xs → dnth xs idx ∈ xs
-- | [] idx H_lt := begin exfalso, exact nat.not_lt_zero _ H_lt end

-- | (x::xs) 0 H_lt := mem_of_cons_same

-- | (x::xs) (idx+1) H_lt :=
-- begin
-- dunfold dnth,
-- apply list.mem_cons_of_mem,
-- apply dnth_mem_of_lt_length,
-- apply nat.lt_of_succ_lt_succ,
-- exact H_lt
-- end

-- theorem filter_false {α : Type*} [decidable_eq α] [inhabited α] : Π (xs : list α), filter (λ x, false) xs = nil
-- | [] := rfl
-- | (x::xs) := begin dunfold filter, simp [filter_false] end

-- theorem not_in_filter_of_match_riota {α : Type*} [decidable_eq α] [inhabited α] (x : α) :
--   ∀ (xs : list α), x ∉ xs → filter (λ (idx : ℕ), x = dnth xs idx) (riota (length xs)) = nil :=
-- assume xs H_nin,
-- have H : filter (λ (idx : ℕ), x = dnth xs idx) (riota (length xs)) = filter (λ idx : ℕ, false) (riota (length xs)),
-- begin
-- apply filter_congr,
-- intros idx H_in,
-- split,
-- intro H_eq,
-- subst H_eq,
-- assert H_x_in : dnth xs idx ∈ xs,
-- apply dnth_mem_of_lt_length,
-- apply lt_length_of_in_riota,
-- exact H_in,
-- exact H_nin H_x_in,
-- intro Hf,
-- exfalso,
-- exact Hf
-- end,
-- begin
-- rw H,
-- rw filter_false
-- end

-- end list

-- namespace monad

-- def foldrM {M : Type → Type} [m : monad M] {X Y : Type} (f : Y → X → M Y) (init : Y) (xs : list X) : M Y :=
--   list.foldr (λ (x : X) (k : Y → M Y) (y : Y), f y x >>= k) return xs init

-- end monad

-- @[simp]
-- def if_is_true {A : Type} (P : Prop) (p : P) (t e : A) :
--   @ite P (is_true p) A t e = t := rfl

-- @[simp]
-- def if_is_false {A : Type} (P : Prop) (np : ¬ P) (t e : A) :
--   @ite P (is_false np) A t e = e := rfl

-- def decidable_and (P Q : Prop) [dP : decidable P] [dQ : decidable Q] : decidable (P ∧ Q) :=
--   match dP, dQ with
--   | is_true p,   is_true q   := is_true (and.intro p q)
--   | is_false np, _           := is_false (λ H : P ∧ Q, np H^.left)
--   | _,           is_false nq := is_false (λ H : P ∧ Q, nq H^.right)
--   end

-- def decidable_or (P Q : Prop) [dP : decidable P] [dQ : decidable Q] : decidable (P ∨ Q) :=
--   match dP, dQ with
--   | is_true p,   _           := is_true (or.inl p)
--   | _,           is_true q   := is_true (or.inr q)
--   | is_false np, is_false nq := is_false (λ H : P ∨ Q, or.rec_on H (λ p, np p) (λ q, nq q))
--   end
