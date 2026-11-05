/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeTorusCoordinates
import Verification.FreezingSupport
import Verification.ExplicitStratumCoordinates

/-!
# Original Free Coordinate Graph

The retained Laurent variables are precisely A(I). Their images are
the original mutable coordinates, so the splitting is suitable for the
componentwise residue calculation.
-/
noncomputable section
namespace Verification.OriginalFreeCoordinateGraph
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.OriginalFreeTorusCoordinates
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

include hsupport in
omit [Fintype κ] in
theorem zero_entry_nonadjacent (a i : Fin n) (h : B (Sum.inl a) (Sum.inl i)=0) :
    ¬ExchangeRing.Adjacent (laterWeights κ n B) a i := by
  rintro (⟨_,hai⟩|⟨_,hia⟩)
  · apply hai
    apply (hsupport a i).mp
    change (B (Sum.inl a) (Sum.inl i)).toNat=0
    rw [h,Int.toNat_zero]
  · apply hia
    change (-B (Sum.inl a) (Sum.inl i)).toNat=0
    rw [h,neg_zero,Int.toNat_zero]

include hpos hneg hsupport in
omit [Fintype κ] in
theorem free_iff (j : Other n I) : FreeCoordinate κ n I B (Sum.inl j) ↔
    ∀ i∈I,¬ExchangeRing.Adjacent (laterWeights κ n B) j.val i := by
  constructor
  · intro h i hi
    exact zero_entry_nonadjacent κ n B hsupport j.val i (h ⟨i,hi⟩)
  · intro h i
    exact FreezingSupport.nonadjacent_entry κ n B hpos hneg hsupport j.val i.val (h i.val i.property)

def boundaryCoordinate (j : Other n I)
    (hj : ∀ i∈I,¬ExchangeRing.Adjacent (laterWeights κ n B) j.val i) : FreeIndex κ n I B :=
  ⟨Sum.inl j,(free_iff κ n I B hpos hneg hsupport j).mpr hj⟩

include hpos hneg hsupport in
omit [Fintype κ] in
theorem enlargement_free (j : Other n I)
    (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) (insert j.val I)) :
    FreeCoordinate κ n I B (Sum.inl j) := by
  apply (free_iff κ n I B hpos hneg hsupport j).mpr
  intro i hi
  exact hJ j.val (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)

variable (R : Type) [CommRing R]
variable (hI : ExchangeOpenCover.Independent (laterWeights κ n B) I)

theorem stratum_original_coordinate (j : FreeIndex κ n I B) :
    stratumEquiv R κ n I B hpos hneg hsupport hI
      (ExplicitStratumCoordinates.original R κ n I B
        ((GlobalSelectedColumns.rowEquiv κ n I).symm j.val).val) =
      MvPolynomial.C (OriginalTorus.torusCoordinate (RemainingRing R κ n I B)
        (FreeIndex κ n I B) j) := by
  dsimp only [stratumEquiv,AlgEquiv.trans_apply]
  rw [ExplicitStratumCoordinates.affineEquiv_original]
  rw [MvPolynomial.mapAlgEquiv_apply,MvPolynomial.map_C]
  change MvPolynomial.C (fiberEquiv R κ n I B
    (Ideal.Quotient.mk _ (OriginalTorus.torusCoordinate R (Other n I⊕κ)
      (GlobalSelectedColumns.rowEquiv κ n I ((GlobalSelectedColumns.rowEquiv κ n I).symm j.val))))) = _
  rw [Equiv.apply_symm_apply]
  exact congrArg MvPolynomial.C (fiberEquiv_coordinate R κ n I B j)

#print axioms zero_entry_nonadjacent
#print axioms free_iff
#print axioms boundaryCoordinate
#print axioms enlargement_free
#print axioms stratum_original_coordinate
end Verification.OriginalFreeCoordinateGraph
