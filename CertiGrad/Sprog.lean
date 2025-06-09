/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic programs.

An `sprog` represents an abstract stochastic computation, in which all primitive stochastic choices
are reified. We denote an `sprog` to a PDF to reason about mathematically, and to an RNG computation
to execute.
-/
-- import .det .rand
import CertiGrad.Det
import CertiGrad.Rand

namespace certigrad

structure Dist (ishapes : List S) : Type := (ev : (oshape : S) → (Dvec T ishapes → T oshape) → T oshape)

noncomputable def pdf {ishapes : List S} (h : Dvec T ishapes → TReal) : Dist ishapes :=
⟨λ (oshape : S) (f : Dvec T ishapes → T oshape) => T.dintegral (λ x => h x • f x)⟩

def delta {ishapes : List S} (x : Dvec T ishapes) : Dist ishapes :=
⟨λ (oshape : S) (f : Dvec T ishapes → T oshape) => f x⟩

-- notation `δ` := delta
notation:max "δ"  => delta


def ev {ishapes : List S} {oshape : S} (d : Dist ishapes) (f : Dvec T ishapes → T oshape) : T oshape := d.ev oshape f

inductive sprog : ∀(shapes : List S), Type
|   ret  : ∀ {shapes : List S}, Dvec T shapes → sprog shapes
| bind : ∀ {shapes₁ shapes₂ : List S}, sprog shapes₁ → (Dvec T shapes₁ → sprog shapes₂) → sprog shapes₂
| prim : ∀ {ishapes : List S} {oshape : S}, rand.op ishapes oshape → Dvec T ishapes → sprog [oshape]


noncomputable def E {oshape : S} : ∀ {shapes : List S}, sprog shapes → (Dvec T shapes → T oshape) → T oshape
| shapes, (@sprog.ret .(shapes) xs), f => f xs

| shapes, (@sprog.bind shapes₁ .(shapes) start rest), f => (E start) (λ (x : Dvec T shapes₁) => (E (rest x) f))

| ([oshape]), (@sprog.prim ishapes .(oshape) pd args), f => T.dintegral (λ (x : Dvec T [oshape]) => pd.pdf args (Dvec.head x) • f x)

namespace sprog

-- we got non-termination error due to op.run
-- use `noncomputable` to suppress the error, which might be problematic.
noncomputable
def to_rngprog : ∀ {shapes : List S}, sprog shapes → StateM RNG (Dvec T shapes)
| shapes, (@ret .(shapes) xs) => return xs
| shapes, (@bind shapes₁ .(shapes) start rest) => do let xs ← (to_rngprog start); to_rngprog (rest xs)
| ([oshape]), (@prim ishapes .(oshape) pd args) => do let x ← pd.run args; return ⟦x⟧

end sprog

end certigrad
