/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Properties of dvecs of tensors.

We often want to do algebra manipulations on an entire dvec at a time,
and this file makes it possible to use standard notation when doing so.
-/
-- import .tensor .dvec .util .graph

import CertiGrad.Tensor
import CertiGrad.Dvec
import CertiGrad.Util
import CertiGrad.Graph

namespace certigrad

namespace tvec

def lift0 (f : ∀ {shape : S}, T shape) : ∀ (shapes : List S), Dvec T shapes
| [] => Dvec.dnil
| (shape::shapes) => Dvec.dcons (f (shape := shape)) (lift0 f shapes)

noncomputable instance {shapes : List S} : Zero (Dvec T shapes) where
zero := lift0 (fun {sh} => 0) shapes


noncomputable instance {shapes : List S} : One (Dvec T shapes) where
one := lift0 (fun {sh} => 1) shapes


def lift1 (f : ∀ {shape : S}, T shape → T shape) : ∀ {shapes : List S}, Dvec T shapes → Dvec T shapes
| [], Dvec.dnil => Dvec.dnil
| (shape::shapes), Dvec.dcons x xs => Dvec.dcons (f x) (lift1 f xs)

-- instance {shapes : List S} : Neg (Dvec T shapes) :=
-- ⟨@tvec.lift1 (λ x => - x) shapes⟩

instance negDvec {shapes : List S} [∀ sh, Neg (T sh)] : Neg (Dvec T shapes) where
  neg := lift1 (fun x => -x)

-- instance {shapes : List S} : Inv (Dvec T shapes) :=
-- ⟨@tvec.lift1 (λ x => x⁻¹) shapes⟩

instance invDvec {shapes : List S} [∀ sh, Inv (T sh)] : Inv (Dvec T shapes) where
  inv := lift1 (fun x => x⁻¹)

noncomputable def sqrtDvec {shapes : List S} (xs : Dvec T shapes) : Dvec T shapes :=
 lift1 (fun x => T.sqrt (x := x)) xs

def lift2 (f : ∀ {shape : S}, T shape → T shape → T shape) : ∀ (shapes : List S), Dvec T shapes → Dvec T shapes → Dvec T shapes
| [], _, _          => Dvec.dnil
| (shape::shapes), (Dvec.dcons x xs), (Dvec.dcons y ys) => Dvec.dcons (f x y) (lift2 f shapes xs ys)

instance addDvec {shapes : List S} [∀ sh, Add (T sh)] : Add (Dvec T shapes) where
  add := lift2 (fun x y => x + y) shapes

instance mulDvec {shapes : List S} [∀ sh, Mul (T sh)] : Mul (Dvec T shapes) where
  mul := lift2 (fun x y => x * y) shapes

instance subDvec {shapes : List S} [∀ sh, Sub (T sh)] : Sub (Dvec T shapes) where
  sub := lift2 (fun x y => x - y) shapes

instance divDvec {shapes : List S} [∀ sh, Div (T sh)] : Div (Dvec T shapes) where
  div := lift2 (fun x y => x / y) shapes

noncomputable def scalarMul : ∀ (shapes : List S), TReal → Dvec T shapes → Dvec T shapes
| [], _,  _                        => Dvec.dnil
| (shape::shapes), α, (Dvec.dcons x xs)   => Dvec.dcons (α • x) (scalarMul shapes α xs)

-- instance {shapes : List S} : SMul TReal (Dvec T shapes) :=
--   ⟨tvec.scalarMul shapes⟩

instance smulDvec {shapes : List S} [∀ sh, SMul TReal (T sh)] : SMul TReal (Dvec T shapes) where
     smul := fun r v => lift1 (fun x => r • x) v


def toEnvCore : ∀ (names : List ID) (shapes : List S) (xs : Dvec T shapes), Env
| (name::names), (shape::shapes), (Dvec.dcons x xs) =>
      env.insert (name, shape) x (toEnvCore names shapes xs)
| _, _, _ => env.mk

def toEnv (refs : List Reference) (xs : Dvec T refs.p2) : Env :=
  toEnvCore refs.p1 refs.p2 xs

-- Build dvec from env
noncomputable def fromEnv : ∀ (tgts : List Reference) (m : Env), Dvec T tgts.p2
| (tgt::tgts), m => Dvec.dcons (env.get tgt m) (fromEnv tgts m)
| [], _ => Dvec.dnil

open List

-- Ensure the following are imported or defined somewhere:
-- open certigrad.dvec (get)
-- open certigrad.env (get)
-- and that at_idx, elem_at_idx, elem_at_idx_of_at_idx are defined or imported

open List
open util_list
lemma get_from_env {refs : List Reference} {idx : ℕ} {ref : Reference} (H_at_idx : at_idx refs idx ref) (m : Env) :
  dvec.get ref.2 _ (fromEnv refs m) idx = env.get ref m := by
  have H_elem_at_idx : elem_at_idx refs idx ref := elem_at_idx_of_at_idx H_at_idx
  induction H_elem_at_idx with
  | base xs x=>
    unfold fromEnv
    erw [dvec.get]
    simp
  | step xs x y idx' H_elem_at_idx IH =>
     unfold fromEnv
     erw [dvec.get]
     exact IH (at_idx_of_cons H_at_idx)


end tvec
end certigrad
