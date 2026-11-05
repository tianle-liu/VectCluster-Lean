/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveExchangeSplit
import Verification.ActualOpenGeometry

/-!
# Actual Open Split

The literal independent-set open exchange ring is an open polynomial
chart over its complementary torus, with all original normal x_i fixed.
-/
noncomputable section
namespace Verification.ActualOpenSplit
open Verification.ActualOpenChart Verification.ActualOpenGeometry
open Verification.LocalExchangeSmooth Verification.CharacterMapSmooth
variable (R ι κ τ : Type) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

def characterIdentification : LocalAlgebra (characters R ι κ τ B) ≃ₐ[R]
    LocalAlgebra (characterUnits R (columnMap ι κ τ B)) :=
  LocalExchangeTransport.localEquiv (AlgEquiv.refl : Torus R (κ →₀ ℤ) ≃ₐ[R] _)
    (characters R ι κ τ B) (characterUnits R (columnMap ι κ τ B))
    (fun i => congrArg Units.val (congrFun (characters_eq R ι κ τ B) i))

omit [Fintype ι] in
theorem characterIdentification_x (i : ι) :
    characterIdentification R ι κ τ B (x (characters R ι κ τ B) i)=
      x (characterUnits R (columnMap ι κ τ B)) i :=
  LocalExchangeTransport.localEquiv_x _ _ _ _ i

variable (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0)
variable (hinj : Function.Injective (columnMap ι κ τ B))
variable (hsat : FreezingLattice.Saturated (LinearMap.range (columnMap ι κ τ B)))

def coordinates : GlobalOpen R ι κ τ j B ≃ₐ[R]
    UniversalExchangeChart.OpenPolynomial
      (Torus R ((κ →₀ ℤ) ⧸ LinearMap.range (columnMap ι κ τ B))) ι :=
  ((globalOpenEquiv R ι κ τ j B hB).trans (characterIdentification R ι κ τ B)).trans
    (PrimitiveExchangeSplit.asChart R (columnMap ι κ τ B) hinj hsat)

theorem coordinates_x (i : ι) :
    coordinates R ι κ τ j B hB hinj hsat (globalCoordinate R ι κ τ j B i)=
      algebraMap
        (UniversalExchangeChart.Polynomial (Torus R ((κ →₀ ℤ) ⧸ LinearMap.range (columnMap ι κ τ B))) ι)
        (UniversalExchangeChart.OpenPolynomial (Torus R ((κ →₀ ℤ) ⧸ LinearMap.range (columnMap ι κ τ B))) ι)
          (MvPolynomial.X (Sum.inl i)) := by
  change PrimitiveExchangeSplit.asChart R (columnMap ι κ τ B) hinj hsat
    (characterIdentification R ι κ τ B
      (globalOpenEquiv R ι κ τ j B hB (globalCoordinate R ι κ τ j B i)))=_
  rw [globalOpenEquiv_coordinate,characterIdentification_x]
  exact PrimitiveExchangeSplit.asChart_x _ _ _ _ _

#print axioms characterIdentification
#print axioms characterIdentification_x
#print axioms coordinates
#print axioms coordinates_x
end Verification.ActualOpenSplit
