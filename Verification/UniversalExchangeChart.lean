/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeParameters
import Verification.SplitExchangeChart

/-!
# Universal Exchange Chart

The universal character exchange chart is literally the polynomial
chart in x,y with every x_i*y_i-1 inverted. All maps are constructed from
the quotient and localization universal properties.
-/
noncomputable section
universe u
namespace Verification.UniversalExchangeChart
open MvPolynomial Verification.LocalExchangeSmooth
variable (R κ : Type u) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def targetUnit (k : κ) : (Target R κ)ˣ := SmithCharacters.coordinateUnit R κ k
abbrev Universal := LocalAlgebra (targetUnit R κ)
abbrev Polynomial := MvPolynomial (κ ⊕ κ) R

def value (k : κ) : Polynomial R κ := X (Sum.inl k) * X (Sum.inr k) - 1
abbrev OpenPolynomial := SplitExchangeChart.ValueLocalization (value R κ)

def polynomialMap : Polynomial R κ →ₐ[R] Universal R κ :=
  aeval (Sum.elim (x (targetUnit R κ)) (y (targetUnit R κ)))

theorem polynomialMap_value (k : κ) : polynomialMap R κ (value R κ k) =
    algebraMap (Target R κ) (Universal R κ) (targetUnit R κ k : Target R κ) := by
  simpa only [polynomialMap, value, map_sub, map_mul, map_one, aeval_X,
    Sum.elim_inl, Sum.elim_inr] using equation (targetUnit R κ) k

def valueUnit (k : κ) : (OpenPolynomial R κ)ˣ :=
  (IsLocalization.map_units (OpenPolynomial R κ)
    (⟨value R κ k, Submonoid.subset_closure (Set.mem_range_self k)⟩ :
      SplitExchangeChart.valueMonoid (value R κ))).unit

theorem valueUnit_val (k : κ) : (valueUnit R κ k : OpenPolynomial R κ) =
    algebraMap (Polynomial R κ) (OpenPolynomial R κ) (value R κ k) :=
  IsUnit.unit_spec _

def fromPolynomial : OpenPolynomial R κ →ₐ[R] Universal R κ :=
  IsLocalization.liftAlgHom (M := SplitExchangeChart.valueMonoid (value R κ))
    (f := polynomialMap R κ) (SplitExchangeChart.units_on_closure (polynomialMap R κ).toRingHom
      (value R κ) (fun k => by
        change IsUnit (polynomialMap R κ (value R κ k))
        rw [polynomialMap_value]
        exact (targetUnit R κ k).isUnit.map _))

theorem fromPolynomial_generator (p : Polynomial R κ) :
    fromPolynomial R κ (algebraMap (Polynomial R κ) (OpenPolynomial R κ) p) =
      polynomialMap R κ p := IsLocalization.lift_eq _ p

def toPolynomial : Universal R κ →ₐ[R] OpenPolynomial R κ :=
  lift (targetUnit R κ) (PartialPowerSmooth.evaluateUnits (valueUnit R κ))
    (fun k => algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X (Sum.inl k)))
    (fun k => algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X (Sum.inr k))) (fun k => by
      rw [show PartialPowerSmooth.evaluateUnits (valueUnit R κ) (targetUnit R κ k : Target R κ) =
        (valueUnit R κ k : OpenPolynomial R κ) from
          PartialPowerSmooth.evaluateUnits_coordinate (valueUnit R κ) k]
      rw [valueUnit_val]
      simp only [value, map_sub, map_mul, map_one])

theorem toPolynomial_x (k : κ) : toPolynomial R κ (x (targetUnit R κ) k) =
    algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X (Sum.inl k)) := lift_x _ _ _ _ _ k

theorem toPolynomial_y (k : κ) : toPolynomial R κ (y (targetUnit R κ) k) =
    algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X (Sum.inr k)) := lift_y _ _ _ _ _ k

theorem toPolynomial_coefficient (z : Target R κ) :
    toPolynomial R κ (algebraMap (Target R κ) (Universal R κ) z) =
      PartialPowerSmooth.evaluateUnits (valueUnit R κ) z := lift_coefficient _ _ _ _ _ z

theorem fromPolynomial_toPolynomial :
    (fromPolynomial R κ).comp (toPolynomial R κ) = AlgHom.id R (Universal R κ) := by
  apply hom_ext (targetUnit R κ)
  · have h : (fromPolynomial R κ).comp (PartialPowerSmooth.evaluateUnits (valueUnit R κ)) =
        IsScalarTower.toAlgHom R (Target R κ) (Universal R κ) := by
      apply DiagonalPowerFibers.laurent_hom_ext
      intro k
      change fromPolynomial R κ
        (PartialPowerSmooth.evaluateUnits (valueUnit R κ) (DiagonalPowerFibers.laurentCoordinate R κ k)) = _
      rw [PartialPowerSmooth.evaluateUnits_coordinate, valueUnit_val, fromPolynomial_generator,
        polynomialMap_value]
      rfl
    intro z
    rw [AlgHom.comp_apply, toPolynomial_coefficient]
    exact AlgHom.congr_fun h z
  · intro k
    rw [AlgHom.comp_apply, toPolynomial_x, fromPolynomial_generator]
    exact aeval_X _ _
  · intro k
    rw [AlgHom.comp_apply, toPolynomial_y, fromPolynomial_generator]
    exact aeval_X _ _

theorem toPolynomial_fromPolynomial :
    (toPolynomial R κ).comp (fromPolynomial R κ) = AlgHom.id R (OpenPolynomial R κ) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (SplitExchangeChart.valueMonoid (value R κ))
  apply MvPolynomial.ringHom_ext
  · intro r
    change toPolynomial R κ (fromPolynomial R κ
      (algebraMap R (OpenPolynomial R κ) r)) = algebraMap R (OpenPolynomial R κ) r
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro v
    change toPolynomial R κ (fromPolynomial R κ
      (algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X v))) = _
    rw [fromPolynomial_generator]
    change toPolynomial R κ (polynomialMap R κ (X v)) =
      algebraMap (Polynomial R κ) (OpenPolynomial R κ) (X v)
    simp only [polynomialMap, aeval_X]
    cases v with
    | inl k => exact toPolynomial_x R κ k
    | inr k => exact toPolynomial_y R κ k

def polynomialEquiv : Universal R κ ≃ₐ[R] OpenPolynomial R κ :=
  AlgEquiv.ofAlgHom (toPolynomial R κ) (fromPolynomial R κ)
    (toPolynomial_fromPolynomial R κ) (fromPolynomial_toPolynomial R κ)

#print axioms targetUnit
#print axioms Universal
#print axioms Polynomial
#print axioms value
#print axioms OpenPolynomial
#print axioms polynomialMap
#print axioms polynomialMap_value
#print axioms valueUnit
#print axioms valueUnit_val
#print axioms fromPolynomial
#print axioms fromPolynomial_generator
#print axioms toPolynomial
#print axioms toPolynomial_x
#print axioms toPolynomial_y
#print axioms toPolynomial_coefficient
#print axioms fromPolynomial_toPolynomial
#print axioms toPolynomial_fromPolynomial
#print axioms polynomialEquiv
end Verification.UniversalExchangeChart
