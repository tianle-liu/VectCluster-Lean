/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalTransverseOpenEquiv
import Verification.ActualTransverseLocalization
import Verification.ActualOpenCoefficients

/-!
# Actual Transverse Open

Transport of the actual open-layer presentation from the literal local
exchange quotient back to the original global quotient and localization.
The original x_v parameter and complementary x-coordinates are preserved.
-/
noncomputable section
universe u
namespace Verification.ActualTransverseOpen
set_option synthInstance.maxHeartbeats 100000
open MvPolynomial Verification.ActualOpenChart Verification.ActualTransverseSlice
open Verification.ActualTransverseLocalization Verification.ActualOpenCoefficients
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)

theorem map_partial :
    (partialIdeal R ι κ τ j B v).map (globalOpenEquiv R ι κ τ j B hB).toRingHom =
      LocalTransverseOpen.partialIdeal (characters R ι κ τ B) v := by
  rw [partialIdeal, Ideal.map_span, ← Set.range_comp, LocalTransverseOpen.partialIdeal]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact globalOpenEquiv_coordinate R ι κ τ j B hB i.1

def partialEquiv : Intermediate R ι κ τ j B v ≃ₐ[R]
    LocalTransverseOpen.Partial (characters R ι κ τ B) v :=
  Ideal.quotientEquivAlg _ _ (globalOpenEquiv R ι κ τ j B hB)
    (map_partial R ι κ τ j B hB v).symm

theorem partialEquiv_mk (z : GlobalOpen R ι κ τ j B) :
    partialEquiv R ι κ τ j B hB v (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z) =
      LocalTransverseOpen.quotient (characters R ι κ τ B) v
        (globalOpenEquiv R ι κ τ j B hB z) := rfl

theorem partialEquiv_parameter :
    partialEquiv R ι κ τ j B hB v (originalParameter R ι κ τ j B v) =
      LocalTransverseOpen.parameter (characters R ι κ τ B) v := by
  rw [originalParameter, partialEquiv_mk, globalOpenEquiv_coordinate]
  rfl

theorem map_parameterPowers :
    (Submonoid.powers (originalParameter R ι κ τ j B v)).map
      (partialEquiv R ι κ τ j B hB v).toMonoidHom =
        Submonoid.powers (LocalTransverseOpen.parameter (characters R ι κ τ B) v) := by
  rw [Submonoid.map_powers]
  change Submonoid.powers (partialEquiv R ι κ τ j B hB v (originalParameter R ι κ τ j B v)) = _
  rw [partialEquiv_parameter]

def openEquiv : OpenSource R ι κ τ j B v ≃ₐ[R]
    LocalTransverseOpen.Open (characters R ι κ τ B) v :=
  IsLocalization.algEquivOfAlgEquiv _ _ (partialEquiv R ι κ τ j B hB v)
    (map_parameterPowers R ι κ τ j B hB v)

theorem openEquiv_include (z : GlobalOpen R ι κ τ j B) :
    openEquiv R ι κ τ j B hB v
      (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)
        (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) z)) =
      LocalTransverseOpen.includeOpen (characters R ι κ τ B) v
        (globalOpenEquiv R ι κ τ j B hB z) := by
  rw [openEquiv, IsLocalization.algEquivOfAlgEquiv_eq, partialEquiv_mk]
  rfl

def affineEquiv : OpenSource R ι κ τ j B v ≃ₐ[R]
    LocalTransverseOpen.Affine (characters R ι κ τ B) v :=
  (openEquiv R ι κ τ j B hB v).trans
    ((LocalTransverseOpenEquiv.affineEquiv (characters R ι κ τ B) v).restrictScalars R)

theorem affineEquiv_parameter : affineEquiv R ι κ τ j B hB v
    (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)
      (originalParameter R ι κ τ j B v)) =
    C (algebraMap (Polynomial (LocalTransverseOpen.OldFiber (characters R ι κ τ B) v))
      (LocalTransverseOpen.Laurent (characters R ι κ τ B) v) Polynomial.X) := by
  change LocalTransverseOpenEquiv.affineEquiv (characters R ι κ τ B) v
    (openEquiv R ι κ τ j B hB v (algebraMap (Intermediate R ι κ τ j B v)
      (OpenSource R ι κ τ j B v) (originalParameter R ι κ τ j B v))) = _
  change LocalTransverseOpenEquiv.affineEquiv (characters R ι κ τ B) v
    (openEquiv R ι κ τ j B hB v (algebraMap (Intermediate R ι κ τ j B v)
      (OpenSource R ι κ τ j B v) (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v)
        (globalCoordinate R ι κ τ j B v)))) = _
  rw [openEquiv_include, globalOpenEquiv_coordinate,
    LocalTransverseOpenEquiv.affineEquiv_parameter]

theorem affineEquiv_outside (k : κ) : affineEquiv R ι κ τ j B hB v
    (algebraMap (Intermediate R ι κ τ j B v) (OpenSource R ι κ τ j B v)
      (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) (originalOutside R ι κ τ j B k))) =
    algebraMap (Coefficients R κ) (LocalTransverseOpen.Affine (characters R ι κ τ B) v)
      (OriginalTorus.torusCoordinate R κ k) := by
  change LocalTransverseOpenEquiv.affineEquiv (characters R ι κ τ B) v
    (openEquiv R ι κ τ j B hB v (algebraMap (Intermediate R ι κ τ j B v)
      (OpenSource R ι κ τ j B v)
      (Ideal.Quotient.mk (partialIdeal R ι κ τ j B v) (originalOutside R ι κ τ j B k)))) = _
  rw [openEquiv_include, globalOpenEquiv_outside, AlgHom.commutes, AlgEquiv.commutes]

#print axioms map_partial
#print axioms partialEquiv
#print axioms partialEquiv_mk
#print axioms partialEquiv_parameter
#print axioms map_parameterPowers
#print axioms openEquiv
#print axioms openEquiv_include
#print axioms affineEquiv
#print axioms affineEquiv_parameter
#print axioms affineEquiv_outside
end Verification.ActualTransverseOpen
