/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LSFourfoldSymbolWords
import Mathlib.Algebra.Ring.Units

/-!
# Milnor Witt Symbol Naturality

Ordinary functoriality of Milnor-Witt coefficients and unit symbols.
The data are uniform in a ring homomorphism and contain no cellular comparison.
-/
namespace Verification.MilnorWittSymbolNaturality
open Verification.MilnorWittSymbolRelations Verification.LSFourfoldSymbolWords
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]

structure Compatible (D₀ : Symbols S B) (D₁ : Symbols T A)
    (f : S →+* T) (F : B →+* A) : Prop where
  g : F D₀.g=D₁.g
  rho : F D₀.rho=D₁.rho
  eta : F D₀.eta=D₁.eta
  symbol : ∀ v, F (D₀.symbol v)=D₁.symbol (Units.map f.toMonoidHom v)

theorem coordinates_map (f : S →+* T) (u a b : Sˣ) (j : Fin 3) (i : Fin 4) :
    Units.map f.toMonoidHom (coordinates u a b j i)=
      coordinates (Units.map f.toMonoidHom u) (Units.map f.toMonoidHom a)
        (Units.map f.toMonoidHom b) j i := by
  fin_cases j <;> fin_cases i <;> simp [coordinates,Units.map_neg]

theorem map_word (F : B →+* A) (x : Fin 4 → B) (s : Fin 16) :
    F (word x s)=word (fun i => F (x i)) s := by fin_cases s <;> simp [word]

variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F)
include h

theorem map_residueTable (a b : Sˣ) (j : Fin 3) (s : Fin 16) :
    F (residueTable D₀ a b j s)=residueTable D₁ (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b) j s := by
  fin_cases j <;> fin_cases s <;> simp [residueTable,h.g,h.rho,h.eta,h.symbol]

theorem map_coordinate_word (u a b : Sˣ) (j : Fin 3) (s : Fin 16) :
    F (word (fun i => D₀.symbol (coordinates u a b j i)) s)=
      word (fun i => D₁.symbol (coordinates (Units.map f.toMonoidHom u)
        (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) j i)) s := by
  rw [map_word]
  congr 1
  funext i
  rw [h.symbol,coordinates_map]

/-- These two rules are the ordinary Laurent symbol contraction: constants
vanish and a new leading parameter symbol is removed. The coefficient ring and
its units remain arbitrary. -/
theorem residue_word (u : Tˣ) (a b : Sˣ) (r : A →+ B)
    (r_constant : ∀ x, r (F x)=0)
    (r_parameter : ∀ x, r (D₁.symbol u*F x)=x)
    (j : Fin 3) (s : Fin 16) :
    r (word (fun i => D₁.symbol (coordinates u (Units.map f.toMonoidHom a)
      (Units.map f.toMonoidHom b) j i)) s)=residueTable D₀ a b j s := by
  rw [word_normal_form,← map_residueTable D₀ D₁ f F h]
  have hc := map_coordinate_word D₀ D₁ f F h 1 a b j s
  simp only [map_one] at hc
  rw [← hc,map_add,r_constant,r_parameter,zero_add]

#print axioms Compatible
#print axioms coordinates_map
#print axioms map_word
#print axioms map_residueTable
#print axioms map_coordinate_word
#print axioms residue_word
end Verification.MilnorWittSymbolNaturality
