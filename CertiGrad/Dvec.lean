/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Dependently-typed vectors.

These are necessary to store multiple tensors of arbitrary shapes.
-/
-- import .util
import CertiGrad.Util

-- inductive dvec {X : Type} (Y : X → Type) : List X → Type
-- | dnil {}  : Dvec []
-- | cons : Π {x : X}, Y x → Π {xs : List X}, dvec xs → dvec (x::xs)

inductive Dvec {X : Type} (Y : X → Type) : List X → Type
  | dnil : Dvec Y []
  | dcons : Y x → Dvec Y (xs : List X) → Dvec Y (x :: xs)


-- reserve infixr ` ::: `:67
-- notation h `:::` t  := cons h t

infixr :67 " ::: " => Dvec.dcons

open Dvec

-- notation : 60  "⟦" l : (List.foldr "," (h t, Dvec.dcons h t) Dvec.dnil "⟧") => l

/- Declares a parser -/
-- set_option trace.Elab.definition true in
syntax (priority := high) "⟦" term,* "⟧" : term

/- Declares two expansions/syntax transformers -/
macro_rules
  | `(⟦⟧) => `(Dvec.dnil)
  | `(⟦$x⟧) => `(Dvec.dcons $x Dvec.dnil) -- this is necessary, otherwise the parse will fail
  | `(⟦$x, $xs:term,*⟧) => `(Dvec.dcons $x ⟦$xs,*⟧)

-- def x0 := ⟦1, 2, 3⟧

def Dvec.head {X : Type} {Y : X → Type} {x : X} {xs : List X}  (l : Dvec Y (x::xs)) : Y x :=
  match l with
  | (dcons y ys) => y

def Dvec.tail {X : Type} {Y : X → Type} {x : X} {xs : List X} : Dvec Y (x::xs) → Dvec Y xs
| (dcons y ys) => ys

def Dvec.head2 {X : Type} {Y : X → Type} {x₁ x₂ : X} {xs : List X} : Dvec Y (x₁::x₂::xs) → Y x₂
| (dcons y₁ (dcons y₂ ys)) => y₂

def Dvec.head3 {X : Type} {Y : X → Type} {x₁ x₂ x₃ : X} {xs : List X} : Dvec Y (x₁::x₂::x₃::xs) → Y x₃
| (dcons y₁ (dcons y₂ (dcons y₃ ys))) => y₃

namespace dvec

def get {X : Type} [DecidableEq X] {Y : X → Type} (x₀ : X) [Inhabited (Y x₀)] : (xs : List X) → Dvec Y xs → Nat → Y x₀
| [],      _ ,          _     => (default :(Y x₀))
| (x::xs), (dcons y ys), 0     => if H : x = x₀ then (by rw [H] at y; assumption) else (default :(Y x₀))
| (x::xs), (dcons y ys), (n+1) => get x₀ xs ys n

-- theorem singleton_congr {X : Type} {Y : X → Type} {x : X} (y₁ y₂ : Y x) : y₁ = y₂ → ⟦y₁⟧ = ⟦y₂⟧ := assume H, by rw H

-- theorem get₀_head {X : Type} [DecidableEq X] {Y : X → Type} (x₀ : X) [Inhabited (Y x₀)] :
--   ∀ {xs : List X} (ys : Dvec Y (x₀::xs)), get x₀ ys 0 = head ys
-- | xs (y:::ys)   => begin dunfold head get, simp [dif_ctx_simp_congr, dif_pos] end

def update_at {X : Type} [DecidableEq X] {Y : X → Type} {x₀ : X} (y₀ : Y x₀) : {xs : List X} → (ys : Dvec Y xs) → (idx : Nat) → Dvec Y xs
| [],      _,                 _     =>  ⟦⟧ -- dnil
| (x::xs), (dcons y ys), 0     => if H : x₀ = x then dcons (Eq.recOn H y₀) ys else dcons y ys
| (x::xs), (dcons y ys), (n+1) => dcons y (update_at y₀ ys n)

-- protected def to_string_aux {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] : Π {xs : List X}, Dvec Y xs → string
-- | [] _                  => "-------------"
-- | (x::xs) (dcons y ys)  => to_string y ++ "\n" ++ to_string_aux ys

-- protected def to_string {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] {xs : List X} (ys : Dvec Y xs) : string :=
--   "-------------\n" ++ dvec.to_string_aux ys

-- instance {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] {xs : List X} : has_to_string (Dvec Y xs) :=
-- ⟨dvec.to_string⟩

protected def toStringHelper {X : Type} {Y : X → Type} [∀ x, ToString (Y x)] : (xs : List X) → Dvec Y xs → String
  | [], _ =>  "-------------"
  | (z::zs), (dcons y ys)  => (toString y) ++ "\n" ++ (dvec.toStringHelper zs ys)

instance {X : Type} {Y : X → Type} [∀ x, ToString (Y x)] {xs : List X} : ToString (Dvec Y xs) where
  toString : Dvec Y xs → String := fun ys => dvec.toStringHelper xs ys

attribute [simp] Dvec.head Dvec.tail Dvec.head2 Dvec.head3 get update_at

end dvec
