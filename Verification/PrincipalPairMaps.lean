/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Principal Pair Maps

Canonical maps of principal open/closed pairs for an exact parameter
identity. This is the geometry-independent domain of the cited natural
purity theorem; its open and closed maps are constructed, not inputs.
-/
noncomputable section
universe u
namespace Verification.PrincipalPairMaps
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : A) (b : B)
variable (φ : A →ₐ[R] B) (h : φ a = b)

abbrev Closed (A : Type u) [CommRing A] (a : A) := A ⧸ Ideal.span {a}
abbrev Open (A : Type u) [CommRing A] (a : A) := Localization.Away a

def closedMap : Closed A a →ₐ[R] Closed B b :=
  Ideal.Quotient.liftₐ (Ideal.span {a}) ((Ideal.Quotient.mkₐ R (Ideal.span {b})).comp φ) (by
    change Ideal.span {a} ≤ RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {b})).comp φ).toRingHom
    apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = a := Set.mem_singleton_iff.mp hx
    subst x
    change Ideal.Quotient.mk (Ideal.span {b}) (φ a) = 0
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton b)))

theorem closed_square : (closedMap R A B a b φ h).comp (Ideal.Quotient.mkₐ R (Ideal.span {a})) =
    (Ideal.Quotient.mkₐ R (Ideal.span {b})).comp φ := rfl

def openCoefficient : A →ₐ[R] Open B b :=
  (IsScalarTower.toAlgHom R B (Open B b)).comp φ

include h in
theorem coefficient_units (m : Submonoid.powers a) : IsUnit (openCoefficient R A B b φ m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn,map_pow]
  change IsUnit ((algebraMap B (Open B b) (φ a)) ^ n)
  rw [h]
  exact (IsLocalization.Away.algebraMap_isUnit b).pow n

def openMap : Open A a →ₐ[R] Open B b :=
  IsLocalization.liftAlgHom (coefficient_units R A B a b φ h)

theorem open_coefficient (x : A) :
    openMap R A B a b φ h (algebraMap A (Open A a) x) =
      algebraMap B (Open B b) (φ x) := IsLocalization.lift_eq _ _

theorem open_square : (openMap R A B a b φ h).comp (IsScalarTower.toAlgHom R A (Open A a)) =
    (IsScalarTower.toAlgHom R B (Open B b)).comp φ := by
  apply AlgHom.ext
  exact open_coefficient R A B a b φ h

#print axioms Closed
#print axioms Open
#print axioms closedMap
#print axioms closed_square
#print axioms openCoefficient
#print axioms coefficient_units
#print axioms openMap
#print axioms open_coefficient
#print axioms open_square
end Verification.PrincipalPairMaps
