/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveCharacters
import Verification.StratumPresentation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Original Torus

Identifying the actual locally closed coordinate base with its torus
group algebra. The left side first kills the selected original variables
and then localizes all complementary variables, as in the manuscript's
zero-stratum construction. Both maps and their values on coordinates are
proved, so later character calculations use the same coordinate ring.
-/
namespace Verification.OriginalTorus
open MvPolynomial MonoidAlgebra Verification.StratumPresentation
open Verification.PrimitiveCharacters
variable (R ι κ : Type*) [CommRing R]

abbrev Lattice := κ →₀ ℤ
abbrev Torus := MonoidAlgebra R (Multiplicative (Lattice κ))

noncomputable def torusCoordinate (k : κ) : Torus R κ :=
  of R _ (Multiplicative.ofAdd (Finsupp.single k 1))

theorem torusCoordinate_isUnit (k : κ) : IsUnit (torusCoordinate R κ k) :=
  ((of R (Multiplicative (Lattice κ))).toHomUnits
    (Multiplicative.ofAdd (Finsupp.single k 1))).isUnit

noncomputable def polynomialMap : MvPolynomial (ι ⊕ κ) R →ₐ[R] Torus R κ :=
  aeval (Sum.elim (fun _ => 0) (torusCoordinate R κ))

theorem polynomialMap_vanishes : zeroCoordinateIdeal R ι κ ≤
    RingHom.ker (polynomialMap R ι κ).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  simp [polynomialMap]

noncomputable def quotientMap : OriginalQuotient R ι κ →ₐ[R] Torus R κ :=
  Ideal.Quotient.liftₐ _ (polynomialMap R ι κ) (polynomialMap_vanishes R ι κ)

theorem quotientMap_units (z : nonzeroCoordinateMonoid R ι κ) :
    IsUnit (quotientMap R ι κ z) := by
  suffices h : ∀ y ∈ nonzeroCoordinateMonoid R ι κ, IsUnit (quotientMap R ι κ y) from
    h z z.property
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨k,rfl⟩ := hy
    change IsUnit (polynomialMap R ι κ (X (Sum.inr k)))
    simpa [polynomialMap] using torusCoordinate_isUnit R κ k
  | one => simp
  | mul y z hy hz ihy ihz => simpa only [map_mul] using ihy.mul ihz

noncomputable def toTorus : OriginalStratum R ι κ →ₐ[R] Torus R κ :=
  IsLocalization.liftAlgHom (quotientMap_units R ι κ)

theorem toTorus_coordinate (k : κ) :
    toTorus R ι κ (originalCoordinate R ι κ (Sum.inr k)) = torusCoordinate R κ k := by
  change IsLocalization.lift (quotientMap_units R ι κ)
    (algebraMap (OriginalQuotient R ι κ) _
      (Ideal.Quotient.mk _ (X (Sum.inr k)))) = _
  rw [IsLocalization.lift_eq]
  change polynomialMap R ι κ (X (Sum.inr k)) = _
  simp [polynomialMap]

noncomputable def inverseCharacter : Multiplicative (Lattice κ) →* OriginalStratum R ι κ :=
  (Units.coeHom _).comp
    (basisCharacter (Finsupp.basisSingleOne : Basis κ ℤ (Lattice κ)) (coordinateUnit R ι κ))

noncomputable def fromTorus : Torus R κ →ₐ[R] OriginalStratum R ι κ :=
  MonoidAlgebra.lift R _ _ (inverseCharacter R ι κ)

theorem fromTorus_coordinate (k : κ) :
    fromTorus R ι κ (torusCoordinate R κ k) = originalCoordinate R ι κ (Sum.inr k) := by
  rw [torusCoordinate, fromTorus, MonoidAlgebra.lift_of]
  change (basisCharacter (Finsupp.basisSingleOne : Basis κ ℤ (Lattice κ))
    (coordinateUnit R ι κ) (Multiplicative.ofAdd (Finsupp.single k 1)) : OriginalStratum R ι κ) = _
  change (basisCharacter (Finsupp.basisSingleOne : Basis κ ℤ (Lattice κ))
    (coordinateUnit R ι κ) (Multiplicative.ofAdd (Finsupp.basisSingleOne k)) : OriginalStratum R ι κ) = _
  rw [basisCharacter_apply, coordinateUnit_val]

theorem toTorus_fromTorus :
    (toTorus R ι κ).comp (fromTorus R ι κ) = AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext'
  apply MonoidHom.eq_of_eqOn_dense
    (basis_generates (Finsupp.basisSingleOne : Basis κ ℤ (Lattice κ)))
  rintro _ ⟨k,rfl⟩
  change toTorus R ι κ (fromTorus R ι κ (torusCoordinate R κ k)) = torusCoordinate R κ k
  rw [fromTorus_coordinate, toTorus_coordinate]

theorem fromTorus_toTorus :
    (fromTorus R ι κ).comp (toTorus R ι κ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (nonzeroCoordinateMonoid R ι κ)
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change fromTorus R ι κ (toTorus R ι κ (algebraMap R _ r)) = algebraMap R _ r
    simp only [AlgHom.commutes]
  · intro v
    cases v with
    | inl i =>
      change fromTorus R ι κ (toTorus R ι κ (originalCoordinate R ι κ (Sum.inl i))) =
        originalCoordinate R ι κ (Sum.inl i)
      rw [originalCoordinate_zero, map_zero, map_zero]
    | inr k =>
      change fromTorus R ι κ (toTorus R ι κ (originalCoordinate R ι κ (Sum.inr k))) =
        originalCoordinate R ι κ (Sum.inr k)
      rw [toTorus_coordinate, fromTorus_coordinate]

noncomputable def originalTorusEquiv : OriginalStratum R ι κ ≃ₐ[R] Torus R κ :=
  AlgEquiv.ofAlgHom (toTorus R ι κ) (fromTorus R ι κ)
    (toTorus_fromTorus R ι κ) (fromTorus_toTorus R ι κ)

#print axioms Lattice
#print axioms Torus
#print axioms torusCoordinate
#print axioms torusCoordinate_isUnit
#print axioms polynomialMap
#print axioms polynomialMap_vanishes
#print axioms quotientMap
#print axioms quotientMap_units
#print axioms toTorus
#print axioms toTorus_coordinate
#print axioms inverseCharacter
#print axioms fromTorus
#print axioms fromTorus_coordinate
#print axioms toTorus_fromTorus
#print axioms fromTorus_toTorus
#print axioms originalTorusEquiv
end Verification.OriginalTorus
