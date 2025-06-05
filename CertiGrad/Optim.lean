/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Algorithms for optimization.
-/
-- import Mathlib.Data.Real.Basic
import  CertiGrad.Tensor
import CertiGrad.Tvec
import CertiGrad.Dvec


namespace certigrad
namespace optim

namespace adam
structure Params where
  α  : TReal
  β₁ : TReal
  β₂ : TReal
  ε  : TReal

structure State (shapes : List S) where
  m₀ : Dvec T shapes
  v₀ : Dvec T shapes
  t  : Nat

noncomputable def initState {shapes : List S} : State shapes := ⟨0, 0, 0⟩
-- def defaultParams : Params := ⟨1/1000, 9/10, 999/1000, T.pow 10 (-8)⟩

noncomputable def defaultParams : Params :=
  { α  := 1 / 1000
  , β₁ := 9 / 10
  , β₂ := 999 / 1000
  , ε  := T.pow 10 (-8)
  }

noncomputable def stepCoreSlow {shapes : List S} (θ grads : Dvec T shapes) : Params → State shapes → Dvec T shapes × State shapes
| ⟨α, β₁, β₂, ε⟩, ⟨mOld, vOld, tOld⟩ =>
  let t := tOld + 1
  let m := β₁ • mOld + (1 - β₁) • grads
  let v := β₂ • vOld + (1 - β₂) • (grads * grads)
  let m' := m / ((1 - T.pow β₁ (t)) • 1)
  let v' := v / ((1 - T.pow β₂ (t)) • 1)
  (θ - α • (m' / (tvec.sqrtDvec v' + ε • 1)), ⟨m, v, t⟩)

noncomputable def stepCore {shapes : List S} (θ grads : Dvec T shapes) : Params → State shapes → Dvec T shapes × State shapes
| ⟨α, β₁, β₂, ε⟩, ⟨mOld, vOld, tOld⟩ =>
  let t := tOld + 1
  let m := β₁ • mOld + (1 - β₁) • grads
  let v := β₂ • vOld + (1 - β₂) • (grads * grads)
  let γ := α * T.sqrt (1 - T.pow β₂ (t)) / (1 - T.pow β₁ (t))
  (θ - γ • (m / (tvec.sqrtDvec v + ε • 1)), ⟨m, v, t⟩)

noncomputable def step {shapes : List S} (θ grads : Dvec T shapes) : State shapes → Dvec T shapes × State shapes :=
  stepCore θ grads defaultParams

end adam
end optim
end certigrad
