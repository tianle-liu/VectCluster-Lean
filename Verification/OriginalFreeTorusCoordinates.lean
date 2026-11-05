/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeCoordinateData
import Verification.FreeCharacterQuotientCoordinates

/-!
# Original Free Torus Coordinates

Free torus coordinates for the exchange-stratum presentation. The fiber
isomorphism preserves the free character coordinates and induces the corresponding
stratum isomorphism.
-/

noncomputable section
namespace Verification.OriginalFreeTorusCoordinates
open Verification.IndependentChartIndex Verification.ActualOpenChart
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def fiberEquiv :=
  FreeCharacterQuotientCoordinates.equiv R ((Other n I⊕κ)→₀ℤ)
    (FreeIndex κ n I B→₀ℤ) (RemainingIndex κ n I B→₀ℤ) (Selected n I)
    (splitting κ n I B) (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B))
    (fun _=>-1) (columns_free_zero κ n I B)
    (ExchangeTransverseSlice.fiberIdeal (characters R (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B)))
    (fiberIdeal_eq R κ n I B)

theorem fiberEquiv_coordinate (j : FreeIndex κ n I B) :
    fiberEquiv R κ n I B (Ideal.Quotient.mk _
      (MonoidAlgebra.of R _ (Multiplicative.ofAdd (Finsupp.single j.val 1)))) =
        OriginalTorus.torusCoordinate (RemainingRing R κ n I B) (FreeIndex κ n I B) j := by
  exact FreeCharacterQuotientCoordinates.free_of_image R ((Other n I⊕κ)→₀ℤ)
    (FreeIndex κ n I B→₀ℤ) (RemainingIndex κ n I B→₀ℤ) (Selected n I)
    (splitting κ n I B) (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B))
    (fun _=>-1) (columns_free_zero κ n I B) _ (fiberIdeal_eq R κ n I B)
    (Finsupp.single j.val 1) (Finsupp.single j 1)
    (CoordinateLatticePartition.coordinate (Other n I⊕κ) (FreeCoordinate κ n I B) j)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔ FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

def stratumEquiv :=
  (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI).trans
    (MvPolynomial.mapAlgEquiv (R := R) (Selected n I) (fiberEquiv R κ n I B))

#print axioms fiberEquiv
#print axioms fiberEquiv_coordinate
#print axioms stratumEquiv
end Verification.OriginalFreeTorusCoordinates
