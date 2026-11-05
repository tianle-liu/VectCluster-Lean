/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingAlgebra
import Verification.FreezingOriginalIndex
import Verification.PartialZeroOriginal

/-!
# Actual Freezing Base

The coefficient base of the actual freezing divisor is the polynomial
algebra on the remaining originals over the torus of the neighbours and
frozen coordinates. This equivalence precedes the equation at v.
-/
noncomputable section
namespace Verification.ActualFreezingBase
open MvPolynomial Verification.ActualDivisorPresentation Verification.ActualFreezingFactor
open Verification.ActualFreezingDivisor Verification.FreezingIndex Verification.FreezingOriginalIndex
open Verification.LocallyClosedPresentation Verification.StratumPresentation
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

abbrev TargetIndex := Remaining κ n B v ⊕ (Neighbor κ n B v ⊕ κ)
abbrev SourceQuotient := Verification.ActualStratum.OriginalPolynomial R (Fin n) κ ⧸ coefficientZeroIdeal R κ n v
abbrev TargetQuotient := OriginalQuotient R PUnit.{1} (TargetIndex κ n B v)

omit [Fintype κ] in
theorem rename_zeroIdeal :
    (coefficientZeroIdeal R κ n v).map (renameEquiv R (originals κ n B v)).toRingHom =
      zeroCoordinateIdeal R PUnit.{1} (TargetIndex κ n B v) := by
  rw [coefficientZeroIdeal, Ideal.map_span, Set.image_singleton]
  have hX : (renameEquiv R (originals κ n B v)).toRingHom (X (Sum.inl v)) =
      X (originals κ n B v (Sum.inl v)) := by
    change rename (originals κ n B v) (X (Sum.inl v)) = _
    rw [rename_X]
  rw [hX]
  rw [originals_free, zeroCoordinateIdeal]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro rfl
    exact Set.mem_range_self PUnit.unit
  · rintro ⟨u,rfl⟩
    cases u
    exact Set.mem_singleton _

def coefficientEquiv : SourceQuotient R κ n v ≃ₐ[R] TargetQuotient R κ n B v :=
  Ideal.quotientEquivAlg _ _ (renameEquiv R (originals κ n B v)) (rename_zeroIdeal R κ n B v).symm

omit [Fintype κ] in
theorem coefficientEquiv_coordinate (a : Fin n ⊕ κ) :
    coefficientEquiv R κ n B v (Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X a)) =
      Ideal.Quotient.mk (zeroCoordinateIdeal R PUnit.{1} (TargetIndex κ n B v)) (X (originals κ n B v a)) := by
  change Ideal.Quotient.mk _ (rename (originals κ n B v) (X a)) = _
  rw [rename_X]

omit [Fintype κ] in
theorem map_openMonoid :
    (coefficientOpenMonoid (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)).map
      (coefficientEquiv R κ n B v).toMonoidHom =
        Verification.PartialZeroOriginal.coordinateMonoid R PUnit.{1}
          (Remaining κ n B v) (Neighbor κ n B v ⊕ κ) := by
  rw [coefficientOpenMonoid, MonoidHom.map_mclosure, ← Set.range_comp]
  change Submonoid.closure (Set.range (fun a : Neighbor κ n B v ⊕ κ =>
    coefficientEquiv R κ n B v (Ideal.Quotient.mk (coefficientZeroIdeal R κ n v)
      (X (invertedOriginal κ n B v a))))) = _
  simp only [coefficientEquiv_coordinate, originals_inverted]
  rfl

def partitionedEquiv : Base R κ n B v ≃ₐ[R]
    Verification.PartialZeroOriginal.Base R PUnit.{1} (Remaining κ n B v) (Neighbor κ n B v ⊕ κ) :=
  IsLocalization.algEquivOfAlgEquiv
    (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v))
    (Verification.PartialZeroOriginal.Base R PUnit.{1} (Remaining κ n B v) (Neighbor κ n B v ⊕ κ))
    (coefficientEquiv R κ n B v) (map_openMonoid R κ n B v)

omit [Fintype κ] in
theorem partitionedEquiv_coordinate (a : Fin n ⊕ κ) :
    partitionedEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v) (X a)) =
        Verification.PartialZeroOriginal.coordinate R PUnit.{1} (Remaining κ n B v)
          (Neighbor κ n B v ⊕ κ) (originals κ n B v a) := by
  have h := IsLocalization.algEquivOfAlgEquiv_eq
    (S := LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v))
    (Q := Verification.PartialZeroOriginal.Base R PUnit.{1} (Remaining κ n B v) (Neighbor κ n B v ⊕ κ))
    (h := coefficientEquiv R κ n B v) (map_openMonoid R κ n B v)
    (Ideal.Quotient.mk (coefficientZeroIdeal R κ n v) (X a))
  refine h.trans ?_
  rw [coefficientEquiv_coordinate]
  rfl

def baseEquiv : Base R κ n B v ≃ₐ[R]
    MvPolynomial (Remaining κ n B v) (Verification.OriginalTorus.Torus R (Neighbor κ n B v ⊕ κ)) :=
  (partitionedEquiv R κ n B v).trans (Verification.PartialZeroOriginal.baseEquiv R PUnit.{1}
    (Remaining κ n B v) (Neighbor κ n B v ⊕ κ))

omit [Fintype κ] in
theorem baseEquiv_remaining (i : Remaining κ n B v) :
    baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v) (X (Sum.inl i.val))) = X i := by
  change Verification.PartialZeroOriginal.baseEquiv R PUnit.{1} _ _
    (partitionedEquiv R κ n B v (baseMap _ _ (X (Sum.inl i.val)))) = _
  rw [partitionedEquiv_coordinate, originals_remaining, Verification.PartialZeroOriginal.baseEquiv_coordinate]
  rfl

omit [Fintype κ] in
theorem baseEquiv_inverted (a : Neighbor κ n B v ⊕ κ) :
    baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (X (invertedOriginal κ n B v a))) =
      C (Verification.OriginalTorus.torusCoordinate R (Neighbor κ n B v ⊕ κ) a) := by
  change Verification.PartialZeroOriginal.baseEquiv R PUnit.{1} _ _
    (partitionedEquiv R κ n B v (baseMap _ _ (X (invertedOriginal κ n B v a)))) = _
  rw [partitionedEquiv_coordinate, originals_inverted, Verification.PartialZeroOriginal.baseEquiv_coordinate]
  rfl

omit [Fintype κ] in
theorem baseEquiv_original (i : Remaining κ n B v) :
    baseEquiv R κ n B v (original R κ n B v (Sum.inl (Sum.inr i))) = X i :=
  baseEquiv_remaining R κ n B v i

#print axioms TargetIndex
#print axioms SourceQuotient
#print axioms TargetQuotient
#print axioms rename_zeroIdeal
#print axioms coefficientEquiv
#print axioms coefficientEquiv_coordinate
#print axioms map_openMonoid
#print axioms partitionedEquiv
#print axioms partitionedEquiv_coordinate
#print axioms baseEquiv
#print axioms baseEquiv_remaining
#print axioms baseEquiv_inverted
#print axioms baseEquiv_original
end Verification.ActualFreezingBase
