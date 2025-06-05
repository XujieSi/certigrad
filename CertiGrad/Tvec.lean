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

instance {shapes : List S} : Zero (Dvec T shapes) :=
⟨tvec.lift0 (λ {sh} => Zero.zero (T sh)) shapes⟩

instance {shapes : List S} : One (Dvec T shapes) :=
⟨tvec.lift0 (λ {sh} => One.one (T sh)) shapes⟩

def lift1 (f : ∀ {shape : S}, T shape → T shape) : ∀ {shapes : List S}, Dvec T shapes → Dvec T shapes
| [], Dvec.dnil => Dvec.dnil
| (shape::shapes), Dvec.dcons x xs => Dvec.dcons (f (shape := shape) x) (lift1 f xs)

instance {shapes : List S} : Neg (Dvec T shapes) :=
⟨@tvec.lift1 (λ x => - x) shapes⟩

instance {shapes : List S} : Inv (Dvec T shapes) :=
⟨@tvec.lift1 (λ x => x⁻¹) shapes⟩

def sqrt {shapes : List S} (xs : Dvec T shapes) : Dvec T shapes :=
lift1 @T.sqrt xs

def lift2 (f : ∀ {shape : S}, T shape → T shape → T shape) : ∀ (shapes : List S), Dvec T shapes → Dvec T shapes → Dvec T shapes
| [], _, _          => Dvec.dnil
| (shape::shapes), (Dvec.dcons x xs), (Dvec.dcons y ys) => Dvec.dcons (f (shape := shape ) x y) (lift2 f shapes xs ys)

instance {shapes : List S} : Add (Dvec T shapes) :=
⟨tvec.lift2 (λ x y => x + y) shapes⟩

instance {shapes : List S} : Mul (Dvec T shapes) :=
⟨tvec.lift2 (λ x y => x * y) shapes⟩

instance {shapes : List S} : Sub (Dvec T shapes) :=
⟨tvec.lift2 (λ x y => x - y) shapes⟩

instance {shapes : List S} : Div (Dvec T shapes) :=
⟨tvec.lift2 (λ x y => x / y) shapes⟩

def scalarMul : ∀ (shapes : List S), ℝ → Dvec T shapes → Dvec T shapes
| [], _,  _                        => Dvec.dnil
| (shape::shapes), α, (Dvec.dcons x xs)   => Dvec.dcons (α • x) (scalarMul shapes α xs)

instance {shapes : List S} : SMul ℝ (Dvec T shapes) :=
⟨tvec.scalarMul shapes⟩

----- Build env from dvec
def toEnvCore : ∀ (names : List ID) (shapes : List S) (xs : Dvec T shapes), env
| (name::names), (shape::shapes), (Dvec.dcons x xs) => env.insert (name, shape) x (toEnvCore names shapes xs)
| _, _, _ => env.mk

def toEnv (refs : List (ID × S)) (xs : Dvec T (Prod.snd <$> refs)) : env :=
  toEnvCore (Prod.fst <$> refs) (Prod.snd <$> refs) xs

-- Build dvec from env
def fromEnv : ∀ (tgts : List (ID × S)) (m : env), Dvec T (Prod.snd <$> tgts)
| (tgt::tgts) m => Dvec.dcons (env.get tgt m) (fromEnv tgts m)
| [] _ => Dvec.dnil

open List

-- Ensure the following are imported or defined somewhere:
-- open certigrad.dvec (get)
-- open certigrad.env (get)
-- and that at_idx, elem_at_idx, elem_at_idx_of_at_idx are defined or imported

lemma get_fromEnv {refs : List reference} {idx : Nat} {ref : reference}
  (H_at_idx : refs[idx]? = some ref) (m : env) :
  dvec.get (fromEnv refs m) idx = env_get ref m := by
  -- Assuming elem_at_idx and elem_at_idx_of_at_idx are defined elsewhere
  have H_elem_at_idx := List.elem_at_idx_of_at_idx H_at_idx
  induction H_elem_at_idx with
  | hd xs x xs' =>
    simp [fromEnv, dvec.get]
  | tl x y xs idx' H_elem_at_idx' IH =>
    simp [fromEnv, dvec.get]
    exact IH (at_idx_of_cons H_at_idx)

end tvec
end certigrad
