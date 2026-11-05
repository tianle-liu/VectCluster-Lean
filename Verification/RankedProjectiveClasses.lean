/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveFreeCoordinates

/-!
# Ranked Projective Classes

Actual isomorphism classes of rank-r finite projective modules and
their stabilization by a trivial line. Equality with the distinguished
class is proved equivalent to actual module freeness.
-/
noncomputable section
namespace Verification.RankedProjectiveClasses
open Verification.ActualProjectiveSplitting Verification.ProjectiveFreeCoordinates
variable (R : Type) [CommRing R] [IsDomain R]

def freeBundle (r : ℕ) : Bundle R where
  object := ModuleCat.of R (Fin r → R)
  finite := inferInstance
  projective := inferInstance

theorem freeBundle_rank (r : ℕ) : HasRank (freeBundle R r) r := by
  intro p
  rw [stalk_rank]
  exact (Module.finrank_fintype_fun_eq_card (R := R)).trans (Fintype.card_fin r)

def Ranked (r : ℕ) := {P : Bundle R // HasRank P r}

def isoSetoid (r : ℕ) : Setoid (Ranked R r) where
  r P Q := Nonempty (P.val.object ≃ₗ[R] Q.val.object)
  iseqv := ⟨fun P => ⟨LinearEquiv.refl R P.val.object⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

def Classes (r : ℕ) := Quotient (isoSetoid R r)

def classOf {r : ℕ} (P : Bundle R) (hr : HasRank P r) : Classes R r :=
  Quotient.mk _ ⟨P,hr⟩

def trivial (r : ℕ) : Classes R r := classOf R (freeBundle R r) (freeBundle_rank R r)

theorem eq_trivial {r : ℕ} (P : Bundle R) (hr : HasRank P r) :
    classOf R P hr=trivial R r ↔ Trivial P := by
  constructor
  · intro h
    obtain ⟨e⟩ := Quotient.exact h
    change P.object ≃ₗ[R] (Fin r → R) at e
    exact Module.Free.of_equiv e.symm
  · intro hf
    exact Quotient.sound ⟨freeEquiv P hr hf⟩

def stabilize (r : ℕ) : Classes R r → Classes R (r+1) :=
  Quotient.map (fun P => ⟨sum P.val line,sum_rank P.property line_rank⟩)
    (by intro P Q h; exact ⟨h.some.prodCongr (LinearEquiv.refl R R)⟩)

theorem stabilize_class {r : ℕ} (P : Bundle R) (hr : HasRank P r) :
    stabilize R r (classOf R P hr)=classOf R (sum P line) (sum_rank hr line_rank) := rfl

theorem stabilize_trivial (r : ℕ) : stabilize R r (trivial R r)=trivial R (r+1) := by
  apply (eq_trivial R _ _).mpr
  exact inferInstanceAs (Module.Free R ((Fin r → R) × R))

theorem cancel_line {r : ℕ} (hi : Function.Injective (stabilize R r))
    (P : Bundle R) (hr : HasRank P r) (hf : Trivial (sum P line)) : Trivial P := by
  apply (eq_trivial R P hr).mp
  apply hi
  rw [stabilize_trivial,stabilize_class]
  exact (eq_trivial R _ _).mpr hf

#print axioms freeBundle
#print axioms freeBundle_rank
#print axioms Ranked
#print axioms isoSetoid
#print axioms Classes
#print axioms classOf
#print axioms trivial
#print axioms eq_trivial
#print axioms stabilize
#print axioms stabilize_class
#print axioms stabilize_trivial
#print axioms cancel_line
end Verification.RankedProjectiveClasses
