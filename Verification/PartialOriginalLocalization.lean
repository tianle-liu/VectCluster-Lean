/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTorus
import Verification.SplitExchangeChart

/-!
# Partial Original Localization

Keep the selected original coordinates as polynomial variables and
invert only the complementary coordinates. The actual localization is
identified with a polynomial ring over the complementary split torus.
No selected coordinate is killed in this construction.
-/

noncomputable section
namespace Verification.PartialOriginalLocalization
open MvPolynomial MonoidAlgebra Verification.PrimitiveCharacters
variable (R ι κ : Type*) [CommRing R]

def coordinateMonoid : Submonoid (MvPolynomial (ι ⊕ κ) R) :=
  Submonoid.closure (Set.range (fun k : κ => (X (Sum.inr k) : MvPolynomial (ι ⊕ κ) R)))

abbrev OpenOriginal := Localization (coordinateMonoid R ι κ)
abbrev Torus := Verification.OriginalTorus.Torus R κ
abbrev Target := MvPolynomial ι (Torus R κ)

def coordinate (v : ι ⊕ κ) : OpenOriginal R ι κ :=
  algebraMap (MvPolynomial (ι ⊕ κ) R) (OpenOriginal R ι κ) (X v)

theorem coordinate_unit (k : κ) : IsUnit (coordinate R ι κ (Sum.inr k)) :=
  IsLocalization.map_units (OpenOriginal R ι κ)
    (⟨X (Sum.inr k), Submonoid.subset_closure (Set.mem_range_self k)⟩ : coordinateMonoid R ι κ)

def coordinateUnits (k : κ) : (OpenOriginal R ι κ)ˣ := (coordinate_unit R ι κ k).unit

def polynomialMap : MvPolynomial (ι ⊕ κ) R →ₐ[R] Target R ι κ :=
  aeval (Sum.elim X (fun k => C (Verification.OriginalTorus.torusCoordinate R κ k)))

theorem polynomialMap_units (m : coordinateMonoid R ι κ) : IsUnit (polynomialMap R ι κ m) := by
  apply Verification.SplitExchangeChart.units_on_closure (polynomialMap R ι κ).toRingHom
    (fun k : κ => (X (Sum.inr k) : MvPolynomial (ι ⊕ κ) R)) _ m
  intro k
  simpa [polynomialMap] using
    (Verification.OriginalTorus.torusCoordinate_isUnit R κ k).map (C : Torus R κ →+* Target R ι κ)

def toTarget : OpenOriginal R ι κ →ₐ[R] Target R ι κ :=
  IsLocalization.liftAlgHom (polynomialMap_units R ι κ)

theorem toTarget_coordinate (v : ι ⊕ κ) :
    toTarget R ι κ (coordinate R ι κ v) =
      Sum.elim X (fun k => C (Verification.OriginalTorus.torusCoordinate R κ k)) v := by
  change IsLocalization.lift (polynomialMap_units R ι κ)
    (algebraMap (MvPolynomial (ι ⊕ κ) R) _ (X v)) = _
  rw [IsLocalization.lift_eq]
  simp [polynomialMap]

def fromTorus : Torus R κ →ₐ[R] OpenOriginal R ι κ :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom _).comp
    (basisCharacter (Finsupp.basisSingleOne : Basis κ ℤ (κ →₀ ℤ)) (coordinateUnits R ι κ)))

theorem fromTorus_coordinate (k : κ) :
    fromTorus R ι κ (Verification.OriginalTorus.torusCoordinate R κ k) =
      coordinate R ι κ (Sum.inr k) := by
  rw [fromTorus, Verification.OriginalTorus.torusCoordinate, MonoidAlgebra.lift_of]
  change (basisCharacter (Finsupp.basisSingleOne : Basis κ ℤ (κ →₀ ℤ))
    (coordinateUnits R ι κ) (Multiplicative.ofAdd (Finsupp.basisSingleOne k)) : OpenOriginal R ι κ) = _
  rw [basisCharacter_apply]
  exact (coordinate_unit R ι κ k).unit_spec

def fromTarget : Target R ι κ →ₐ[R] OpenOriginal R ι κ :=
  aevalTower (fromTorus R ι κ) (fun i => coordinate R ι κ (Sum.inl i))

theorem fromTarget_X (i : ι) : fromTarget R ι κ (X i) = coordinate R ι κ (Sum.inl i) :=
  aevalTower_X _ _ _

theorem fromTarget_C (t : Torus R κ) : fromTarget R ι κ (C t) = fromTorus R ι κ t :=
  aevalTower_C _ _ _

theorem toTarget_fromTorus :
    (toTarget R ι κ).comp (fromTorus R ι κ) =
      IsScalarTower.toAlgHom R (Torus R κ) (Target R ι κ) := by
  apply MonoidAlgebra.algHom_ext'
  apply MonoidHom.eq_of_eqOn_dense
    (basis_generates (Finsupp.basisSingleOne : Basis κ ℤ (κ →₀ ℤ)))
  rintro _ ⟨k,rfl⟩
  change toTarget R ι κ (fromTorus R ι κ (Verification.OriginalTorus.torusCoordinate R κ k)) =
    C (Verification.OriginalTorus.torusCoordinate R κ k)
  rw [fromTorus_coordinate, toTarget_coordinate]
  rfl

theorem toTarget_fromTarget : (toTarget R ι κ).comp (fromTarget R ι κ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro t
    change toTarget R ι κ (fromTarget R ι κ (C t)) = C t
    rw [fromTarget_C]
    exact AlgHom.congr_fun (toTarget_fromTorus R ι κ) t
  · intro i
    change toTarget R ι κ (fromTarget R ι κ (X i)) = X i
    rw [fromTarget_X, toTarget_coordinate]
    rfl

theorem fromTarget_toTarget : (fromTarget R ι κ).comp (toTarget R ι κ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (coordinateMonoid R ι κ)
  apply MvPolynomial.ringHom_ext
  · intro r
    change fromTarget R ι κ (toTarget R ι κ (algebraMap R _ r)) = algebraMap R _ r
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro v
    change fromTarget R ι κ (toTarget R ι κ (coordinate R ι κ v)) = coordinate R ι κ v
    rw [toTarget_coordinate]
    cases v with
    | inl i => exact fromTarget_X R ι κ i
    | inr k => exact (fromTarget_C R ι κ _).trans (fromTorus_coordinate R ι κ k)

def openOriginalEquiv : OpenOriginal R ι κ ≃ₐ[R] Target R ι κ :=
  AlgEquiv.ofAlgHom (toTarget R ι κ) (fromTarget R ι κ)
    (toTarget_fromTarget R ι κ) (fromTarget_toTarget R ι κ)

#print axioms coordinateMonoid
#print axioms OpenOriginal
#print axioms Torus
#print axioms Target
#print axioms coordinate
#print axioms coordinate_unit
#print axioms coordinateUnits
#print axioms polynomialMap
#print axioms polynomialMap_units
#print axioms toTarget
#print axioms toTarget_coordinate
#print axioms fromTorus
#print axioms fromTorus_coordinate
#print axioms fromTarget
#print axioms fromTarget_X
#print axioms fromTarget_C
#print axioms toTarget_fromTorus
#print axioms toTarget_fromTarget
#print axioms fromTarget_toTarget
#print axioms openOriginalEquiv
end Verification.PartialOriginalLocalization
