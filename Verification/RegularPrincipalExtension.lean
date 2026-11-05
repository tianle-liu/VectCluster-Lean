/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Regular Principal Extension

Relations can be checked after inverting a regular parameter. This
allows coefficient maps which use only extending units to descend across
the actual boundary, without assuming extension of the quotient map.
-/
noncomputable section
namespace Verification.RegularPrincipalExtension
variable {A : Type*} [CommRing A] (t : A) (ht : IsSMulRegular A t)

include ht in
theorem injective : Function.Injective (algebraMap A (Localization.Away t)) := by
  apply (IsLocalization.injective_iff_isRegular (S := Localization.Away t) (Submonoid.powers t)).mpr
  intro s
  obtain ⟨n, hn⟩ := s.property
  have h : IsLeftRegular (t ^ n) := ht.pow n
  rw [← hn]
  exact ⟨h, h.right_of_commute (fun b => mul_comm _ b)⟩

variable {S : Type*} [CommRing S] (I : Ideal S) (f : S →+* A)
variable (g : (S ⧸ I) →+* Localization.Away t)
variable (commutes : ∀ a, algebraMap A (Localization.Away t) (f a) = g (Ideal.Quotient.mk I a))

include ht commutes in
theorem relations : I ≤ RingHom.ker f := by
  intro a ha
  apply injective t ht
  rw [map_zero, commutes, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def lift : (S ⧸ I) →+* A := Ideal.Quotient.lift I f (relations t ht I f g commutes)

theorem lift_mk (a : S) : lift t ht I f g commutes (Ideal.Quotient.mk I a) = f a := rfl

theorem open_lift (a : S ⧸ I) :
    algebraMap A (Localization.Away t) (lift t ht I f g commutes a) = g a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact commutes a

theorem unit_extends (u : (S ⧸ I)ˣ) : IsUnit (lift t ht I f g commutes u) :=
  u.isUnit.map (lift t ht I f g commutes)

#print axioms injective
#print axioms relations
#print axioms lift
#print axioms lift_mk
#print axioms open_lift
#print axioms unit_extends
end Verification.RegularPrincipalExtension
