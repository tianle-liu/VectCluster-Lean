/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateLatticePartition
import Verification.FreeCharacterFactor
import Verification.ActualColumnRank
import Verification.IndependentStratumCoordinates

/-!
# Original Free Coordinate Data

Simultaneously separate the named mutable coordinates absent from
all old exchange characters. The actual original torus fiber and zero
stratum retain these independent Laurent variables. No Smith basis is
allowed to mix them with the complementary character lattice.
-/
noncomputable section
namespace Verification.OriginalFreeTorusCoordinates
open Verification.IndependentChartIndex Verification.ActualOpenChart
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def FreeCoordinate : (Other n I ⊕ κ)→Prop
  | Sum.inl j => ∀ i : Selected n I,B (Sum.inl j.val) (Sum.inl i.val)=0
  | Sum.inr _ => False

#print axioms FreeCoordinate

abbrev FreeIndex := {j : Other n I⊕κ // FreeCoordinate κ n I B j}
abbrev RemainingIndex := {j : Other n I⊕κ // ¬FreeCoordinate κ n I B j}

def splitting := CoordinateLatticePartition.equiv (Other n I⊕κ) (FreeCoordinate κ n I B)

theorem columns_free_zero (i : Selected n I) :
    (splitting κ n I B (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B) i)).1=0 := by
  apply CoordinateLatticePartition.column_first_zero
  intro j hj
  rw [ActualColumnRank.actual_column_apply]
  cases j with
  | inl j => exact hj i
  | inr k => exact hj.elim

def remainingIdeal := FreeCharacterFactor.coefficientIdeal R ((Other n I⊕κ)→₀ℤ)
  (FreeIndex κ n I B→₀ℤ) (RemainingIndex κ n I B→₀ℤ) (Selected n I)
  (splitting κ n I B) (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B)) (fun _=>-1)

abbrev RemainingRing := MonoidAlgebra R (Multiplicative (RemainingIndex κ n I B→₀ℤ)) ⧸
  remainingIdeal R κ n I B

theorem fiberIdeal_eq :
    ExchangeTransverseSlice.fiberIdeal (characters R (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B)) =
      FreeCharacterFactor.sourceIdeal R ((Other n I⊕κ)→₀ℤ) (Selected n I)
        (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B)) (fun _=>-1) := by
  unfold ExchangeTransverseSlice.fiberIdeal FreeCharacterFactor.sourceIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change 1+MonoidAlgebra.of R (Multiplicative ((Other n I⊕κ)→₀ℤ))
    (Multiplicative.ofAdd (column (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B) i)) = _
  simp only [map_neg,map_one,sub_neg_eq_add,add_comm]

#print axioms FreeIndex
#print axioms RemainingIndex
#print axioms splitting
#print axioms columns_free_zero
#print axioms remainingIdeal
#print axioms RemainingRing
#print axioms fiberIdeal_eq
end Verification.OriginalFreeTorusCoordinates
