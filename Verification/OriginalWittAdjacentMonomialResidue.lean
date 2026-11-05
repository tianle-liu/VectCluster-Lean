/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalASAdjacentUnitCharacter
import Verification.OriginalWittFullMonomialComparison
import Verification.WittMonomialResidue

/-!
# Original Witt Adjacent Monomial Residue

The ordinary genuine Witt Laurent residue of every literal source
basis element is computed on the actual adjacent geometric map.
-/
noncomputable section
open scoped Classical TensorProduct
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
namespace Verification.OriginalWittAdjacentMonomialResidue
open CategoryTheory AlgebraicGeometry Opposite
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
open Verification.WittSheafSectionsInput
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (hD : ∀ l i : Selected n J, IndependentChartIndex.matrix κ n J B (Sum.inl l) (Sum.inl i)=0)
variable (hfI : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B (J.erase v.val)))
variable (hsI : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B (J.erase v.val))))
variable (hfJ : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hsJ : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (laterWeights κ n B) (J.erase v.val))
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n J) (Other n J ⊕ κ) (Other n J) (IndependentChartIndex.matrix κ n J B))
local notation "Laur" => LaurentBasepoint.Laurent New
local notation "CI" => OriginalASFullUnitCharacter.character κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI
local notation "CJ" => OriginalASFullUnitCharacter.character κ n J R B hfJ hsJ hpos hneg hsupport hJ
local notation "src" => OriginalSourceLaurentGenerators.map R κ n J B v hD
local notation "proj" => OriginalCanonicalFiberProjection.projection R κ n J B hpos hneg hsupport hJ


def fiberSmooth : Algebra.Smooth R New := by
  letI := TorusSmooth.torus_smooth R (Fin (ExplicitStratumTorus.torusRank κ n J B))
  exact Algebra.Smooth.of_equiv (ExplicitStratumTorus.fiberEquiv R κ n J B hfJ hsJ).symm

variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (D : Symbols R W)
variable (T : TorusBasis R W D) (H : WittSheafAffineInvariance.Standard R W)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (E : Comparison R W site N) (K : StandardThomContractionNormalization.Grading R site N)
variable (Norm : LaurentNormalization R W D site N E K)

include Norm in
theorem monomial (m : OriginalWittQuotient.Bits (Fin n) κ) (q : ℤ) (a : RingSection W R) :
    WittSheafLaurentResidue.residue R W site N E K New (fiberSmooth R κ n J B hfJ hsJ) q
      (pullback W (src).toRingHom
        (OriginalWittSectionCoordinates.equiv R κ n (J.erase v.val) B hfI hsI hpos hneg hsupport hI W D T H
          (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a))) =
      if m (Sum.inl v.val)=0 then 0 else
        pullback W (proj).toRingHom
          (OriginalWittSectionCoordinates.equiv R κ n J B hfJ hsJ hpos hneg hsupport hJ W D T H
            (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a)) := by
  rw [OriginalWittFullMonomialComparison.monomial,OriginalWittFullMonomialComparison.monomial,
    ← OriginalASFullUnitCharacter.integerVector_character κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI,
    ← OriginalASFullUnitCharacter.integerVector_character κ n J R B hfJ hsJ hpos hneg hsupport hJ]
  have hu := OriginalASAdjacentUnitCharacter.factorization_apply R κ n J B v hD hfI hsI hfJ hsJ
    hpos hneg hsupport hI hJ (OriginalASFullUnitCharacter.integerVector κ n m)
  change Units.map (src).toRingHom.toMonoidHom (CI (Multiplicative.ofAdd (OriginalASFullUnitCharacter.integerVector κ n m))) =
    LaurentPolynomialUniversal.parameterUnit New ^ ((m (Sum.inl v.val)).val : ℤ) *
      Units.map (LaurentBasepoint.coefficient R New).toRingHom.toMonoidHom
        (Units.map (proj).toRingHom.toMonoidHom (CJ (Multiplicative.ofAdd (OriginalASFullUnitCharacter.integerVector κ n m)))) at hu
  rw [zpow_natCast] at hu
  rw [WittMonomialResidue.residue R W D site N E K Norm
    (OriginalASMonomialUnits.smooth R κ n (J.erase v.val) B hfI hsI hpos hneg hsupport hI)
    (OriginalASMonomialUnits.smooth R κ n J B hfJ hsJ hpos hneg hsupport hJ)
    (fiberSmooth R κ n J B hfJ hsJ) (src) (proj) _ _ _ hu]
  simp only [Nat.mod_eq_of_lt (ZMod.val_lt _),ZMod.val_eq_zero]

#print axioms fiberSmooth
#print axioms monomial
end Verification.OriginalWittAdjacentMonomialResidue
