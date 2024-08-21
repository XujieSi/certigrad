/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Interface for deterministic operators.
-/
-- import CertiGrad.tgrads .util .tcont

import CertiGrad.Tgrads
import CertiGrad.Util
import CertiGrad.Tcont
import CertiGrad.Dvec

namespace certigrad
open T util_list dvec

namespace det

def function (ishapes : List S) (oshape : S) : Type := Dvec T ishapes → T oshape
def precondition (shapes : List S) : Type := Dvec T shapes → Prop
def pullback (ishapes : List S) (oshape : S) : Type := Π (xs : Dvec T ishapes) (y gy : T oshape) (idx : Nat) (fshape : S), T fshape

noncomputable def is_odifferentiable {ishapes : List S} {oshape : S} (f : Dvec T ishapes → T oshape) (f_pre : Dvec T ishapes → Prop) : Prop :=
    ∀ (xs : Dvec T ishapes), f_pre xs →
    ∀ (idx : Nat) (fshape : S), at_idx ishapes idx fshape →
    ∀ (k : T oshape → TReal), is_cdifferentiable k (f xs) → is_cdifferentiable (λ θ₀ => k (f $ update_at θ₀ xs idx)) (get fshape _ xs idx)

noncomputable def pullback_correct {ishapes : List S} {oshape : S}
               (f : Dvec T ishapes → T oshape)
               (f_pre : Dvec T ishapes → Prop)
               (f_pb : Dvec T ishapes → T oshape → T oshape → Nat → Π fshape, T fshape) : Prop :=
    ∀ (xs : Dvec T ishapes) (y : T oshape), y = f xs →
      ∀ (g_out : T oshape) {idx : Nat} {fshape : S}, at_idx ishapes idx fshape →
              f_pre xs →
              f_pb xs y g_out idx fshape
               =
              T.tmulT (T.D (λ θ₀ => f (update_at θ₀ xs idx)) (dvec.get fshape _ xs idx)) g_out

noncomputable def is_ocontinuous {ishapes : List S} {oshape : S} (f : Dvec T ishapes → T oshape) (f_pre : Dvec T ishapes → Prop) : Prop :=
  ∀ (xs : Dvec T ishapes) {idx : Nat} {ishape : S}, at_idx ishapes idx ishape →
      f_pre xs → T.is_continuous (λ θ₀ => f (update_at θ₀ xs idx)) (get ishape _ xs idx)

inductive op : Π (ishapes : List S) (oshape : S),  Type
| mk : ∀ {ishapes : List S} {oshape : S} (id : String)
         (f :function ishapes oshape) (f_pre : precondition ishapes) (f_pb : pullback ishapes oshape),
         is_odifferentiable f f_pre → pullback_correct f f_pre f_pb → is_ocontinuous f f_pre →
         op ishapes oshape

-- Note: we keep this separate because we use it in a program transformation
-- (we want to be able to pattern match on it)
| mvn_empirical_kl : Π (shape : S), op [shape, shape, shape] []


namespace op

noncomputable def f : Π {ishapes : List S} {oshape : S}, op ishapes oshape → function ishapes oshape
| _, _, (@op.mk ishapes id oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  =>fn
| _, _, (@op.mvn_empirical_kl shape) => λ xs => T.mvn_empirical_kl (Dvec.head xs) (Dvec.head2 xs) (Dvec.head3 xs)

def pre : Π {ishapes : List S} {oshape : S}, op ishapes oshape → precondition ishapes
| _, _, (@op.mk id ishapes oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  => f_pre
| _, _, (@mvn_empirical_kl shape) => λ xs => False

noncomputable def pb : Π {ishapes : List S} {oshape : S}, op ishapes oshape → pullback ishapes oshape
| _, _, (@op.mk id ishapes oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  => f_pb
| _, _, (@mvn_empirical_kl shape) => λ xs y gy idx fshape => T.error "mvn_empirical_kl: gradients not implemented"



-- is_odifferentiable (f op) (pre op)  constructs the following type:
    -- ∀ (xs : Dvec T ishapes), f_pre xs →
    -- ∀ (idx : Nat) (fshape : S), at_idx ishapes idx fshape →
    -- ∀ (k : T oshape → TReal), is_cdifferentiable k (f xs) → is_cdifferentiable (λ θ₀ => k (f $ update_at θ₀ xs idx)) (get fshape _ xs idx)

-- axiom is_cdifferentiable : {ishape : S} →  (T ishape → TReal) → T ishape → Prop

def is_odiff : Π {ishapes : List S} {oshape : S} (op : op ishapes oshape), is_odifferentiable (f op) (pre op)
| _, _, (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) => f_is_odiff
| _, _, (@mvn_empirical_kl shape) => λ xs H_pre idx fshape H_fshape_at_idx k H_k => False.rec _ H_pre

def pb_correct : Π {ishapes : List S} {oshape : S} (op : op ishapes oshape), pullback_correct (f op) (pre op) (pb op)
| _, _, (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) => f_pb_correct
| _, _, (@mvn_empirical_kl shape) => λ xs y _ g_out _ _ H_at_idx H_pre => False.rec _ H_pre

def is_ocont : Π {ishapes : List S} {oshape : S} (op : op ishapes oshape), is_ocontinuous (f op) (pre op)
| _, _, (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) => f_is_continuous
| _, _, (@mvn_empirical_kl shape) => λ xs idx ishape H_ishape_at_idx H_pre => False.rec _ H_pre

end op
end det
end certigrad
