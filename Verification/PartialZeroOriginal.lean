/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.KilledOriginalPolynomial
import Verification.PartialOriginalLocalization

/-!
# Partial Zero Original

Kill one family of original coordinates and invert a disjoint family,
leaving all remaining originals polynomial. This is the actual coefficient
base of a freezing divisor before its character constraint is imposed.
-/
noncomputable section
namespace Verification.PartialZeroOriginal
open MvPolynomial Verification.StratumPresentation
variable (R α ι κ : Type*) [CommRing R]

abbrev QuotientBase := OriginalQuotient R α (ι ⊕ κ)

def coordinateMonoid : Submonoid (QuotientBase R α ι κ) :=
  Submonoid.closure (Set.range (fun k : κ =>
    Ideal.Quotient.mk (zeroCoordinateIdeal R α (ι ⊕ κ)) (X (Sum.inr (Sum.inr k)))))

abbrev Base := Localization (coordinateMonoid R α ι κ)

def coordinate (v : α ⊕ (ι ⊕ κ)) : Base R α ι κ :=
  algebraMap (QuotientBase R α ι κ) (Base R α ι κ)
    (Ideal.Quotient.mk (zeroCoordinateIdeal R α (ι ⊕ κ)) (X v))

theorem coordinate_zero (a : α) : coordinate R α ι κ (Sum.inl a) = 0 := by
  simp only [coordinate, KilledOriginalPolynomial.killed_variable, map_zero]

theorem coordinate_unit (k : κ) : IsUnit (coordinate R α ι κ (Sum.inr (Sum.inr k))) :=
  IsLocalization.map_units (M := coordinateMonoid R α ι κ) (Base R α ι κ)
    ⟨_, Submonoid.subset_closure (Set.mem_range_self k)⟩

def quotientToOpen : QuotientBase R α ι κ →ₐ[R] Verification.PartialOriginalLocalization.OpenOriginal R ι κ :=
  (IsScalarTower.toAlgHom R (MvPolynomial (ι ⊕ κ) R)
    (Verification.PartialOriginalLocalization.OpenOriginal R ι κ)).comp
      (Verification.KilledOriginalPolynomial.quotientEquiv R α (ι ⊕ κ)).toAlgHom

theorem quotientToOpen_coordinate (v : ι ⊕ κ) :
    quotientToOpen R α ι κ (Ideal.Quotient.mk (zeroCoordinateIdeal R α (ι ⊕ κ)) (X (Sum.inr v))) =
      Verification.PartialOriginalLocalization.coordinate R ι κ v := by
  change algebraMap (MvPolynomial (ι ⊕ κ) R) (Verification.PartialOriginalLocalization.OpenOriginal R ι κ)
    (KilledOriginalPolynomial.quotientEquiv R α (ι ⊕ κ)
      (Ideal.Quotient.mk (zeroCoordinateIdeal R α (ι ⊕ κ)) (X (Sum.inr v)))) = _
  rw [KilledOriginalPolynomial.quotientEquiv_remaining]
  rfl

theorem quotientToOpen_units (m : coordinateMonoid R α ι κ) : IsUnit (quotientToOpen R α ι κ m) := by
  apply Verification.SplitExchangeChart.units_on_closure (quotientToOpen R α ι κ).toRingHom
    (fun k : κ => Ideal.Quotient.mk (zeroCoordinateIdeal R α (ι ⊕ κ)) (X (Sum.inr (Sum.inr k)))) _ m
  intro k
  change IsUnit (quotientToOpen R α ι κ (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr k)))))
  rw [quotientToOpen_coordinate]
  exact Verification.PartialOriginalLocalization.coordinate_unit R ι κ k

def toOpen : Base R α ι κ →ₐ[R] Verification.PartialOriginalLocalization.OpenOriginal R ι κ :=
  IsLocalization.liftAlgHom (quotientToOpen_units R α ι κ)

theorem toOpen_coordinate (v : ι ⊕ κ) :
    toOpen R α ι κ (coordinate R α ι κ (Sum.inr v)) =
      Verification.PartialOriginalLocalization.coordinate R ι κ v := by
  change IsLocalization.lift (quotientToOpen_units R α ι κ) (algebraMap _ _ _) = _
  rw [IsLocalization.lift_eq]
  exact quotientToOpen_coordinate R α ι κ v

def fromPolynomial : MvPolynomial (ι ⊕ κ) R →ₐ[R] Base R α ι κ :=
  aeval (fun v => coordinate R α ι κ (Sum.inr v))

theorem fromPolynomial_units (m : Verification.PartialOriginalLocalization.coordinateMonoid R ι κ) :
    IsUnit (fromPolynomial R α ι κ m) := by
  apply Verification.SplitExchangeChart.units_on_closure (fromPolynomial R α ι κ).toRingHom
    (fun k : κ => (X (Sum.inr k) : MvPolynomial (ι ⊕ κ) R)) _ m
  intro k
  change IsUnit (aeval (fun v => coordinate R α ι κ (Sum.inr v)) (X (Sum.inr k)))
  rw [aeval_X]
  exact coordinate_unit R α ι κ k

def fromOpen : Verification.PartialOriginalLocalization.OpenOriginal R ι κ →ₐ[R] Base R α ι κ :=
  IsLocalization.liftAlgHom (fromPolynomial_units R α ι κ)

theorem fromOpen_coordinate (v : ι ⊕ κ) :
    fromOpen R α ι κ (Verification.PartialOriginalLocalization.coordinate R ι κ v) =
      coordinate R α ι κ (Sum.inr v) := by
  change IsLocalization.lift (fromPolynomial_units R α ι κ) (algebraMap _ _ (X v)) = _
  rw [IsLocalization.lift_eq]
  exact aeval_X _ _

theorem toOpen_fromOpen : (toOpen R α ι κ).comp (fromOpen R α ι κ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Verification.PartialOriginalLocalization.coordinateMonoid R ι κ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change toOpen R α ι κ (fromOpen R α ι κ (algebraMap R _ r)) = algebraMap R _ r
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro v
    change toOpen R α ι κ (fromOpen R α ι κ (Verification.PartialOriginalLocalization.coordinate R ι κ v)) = _
    rw [fromOpen_coordinate, toOpen_coordinate]
    rfl

theorem fromOpen_toOpen : (fromOpen R α ι κ).comp (toOpen R α ι κ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (coordinateMonoid R α ι κ)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change fromOpen R α ι κ (toOpen R α ι κ (algebraMap R _ r)) = algebraMap R _ r
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro v
    change fromOpen R α ι κ (toOpen R α ι κ (coordinate R α ι κ v)) = coordinate R α ι κ v
    cases v with
    | inl a => rw [coordinate_zero, map_zero, map_zero]
    | inr v => rw [toOpen_coordinate, fromOpen_coordinate]

def localizationEquiv : Base R α ι κ ≃ₐ[R] Verification.PartialOriginalLocalization.OpenOriginal R ι κ :=
  AlgEquiv.ofAlgHom (toOpen R α ι κ) (fromOpen R α ι κ)
    (toOpen_fromOpen R α ι κ) (fromOpen_toOpen R α ι κ)

def baseEquiv : Base R α ι κ ≃ₐ[R] MvPolynomial ι (Verification.OriginalTorus.Torus R κ) :=
  (localizationEquiv R α ι κ).trans (Verification.PartialOriginalLocalization.openOriginalEquiv R ι κ)

theorem baseEquiv_coordinate (v : ι ⊕ κ) :
    baseEquiv R α ι κ (coordinate R α ι κ (Sum.inr v)) =
      Sum.elim X (fun k => C (Verification.OriginalTorus.torusCoordinate R κ k)) v := by
  change Verification.PartialOriginalLocalization.toTarget R ι κ
    (toOpen R α ι κ (coordinate R α ι κ (Sum.inr v))) = _
  rw [toOpen_coordinate]
  exact Verification.PartialOriginalLocalization.toTarget_coordinate R ι κ v

#print axioms QuotientBase
#print axioms coordinateMonoid
#print axioms Base
#print axioms coordinate
#print axioms coordinate_zero
#print axioms coordinate_unit
#print axioms quotientToOpen
#print axioms quotientToOpen_coordinate
#print axioms quotientToOpen_units
#print axioms toOpen
#print axioms toOpen_coordinate
#print axioms fromPolynomial
#print axioms fromPolynomial_units
#print axioms fromOpen
#print axioms fromOpen_coordinate
#print axioms toOpen_fromOpen
#print axioms fromOpen_toOpen
#print axioms localizationEquiv
#print axioms baseEquiv
#print axioms baseEquiv_coordinate
end Verification.PartialZeroOriginal
