/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingCoordinates
import Verification.OriginalRemainingBoundaryIndex
import Verification.RegularPrincipalExtension
import Verification.AdjacentStratumLocalization

/-!
# Original Remaining Extension

The entire coefficient ring Y_I in the A(I)-preserving presentation
extends across each allowed boundary. Its defining relations are verified
after the proved injective localization, so no extension hypothesis is used.
-/
noncomputable section
namespace Verification.OriginalRemainingExtension
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
open Verification.FrozenAcyclicCover Verification.OriginalRemainingBoundaryIndex
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
local notation "I" => J.erase v.val
local notation "W" => OriginalBoundaryBranches.Ambient R κ n J B v
local notation "t" => OriginalBoundaryBranches.parameter R κ n J B v
local notation "S" => RemainingRing R κ n (J.erase v.val) B
local notation "Q" => RemainingIndex κ n (J.erase v.val) B
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)

include hJ in
omit [Fintype κ] in
theorem old_independent : ExchangeOpenCover.Independent (laterWeights κ n B) (J.erase v.val) :=
  fun a ha b hb => hJ a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)

def torusMap : OriginalTorus.Torus R Q →ₐ[R] W :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom W).comp
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne
      (coordinateUnit κ n J B v hpos hneg hsupport hJ R)))

theorem torusMap_coordinate (k : Q) :
    torusMap R κ n J B v hpos hneg hsupport hJ (OriginalTorus.torusCoordinate R Q k) =
      OriginalBoundaryBranches.coordinate R κ n J B v
        (IndependentChartPresentation.complementEmbedding κ n I k.val) := by
  rw [torusMap, OriginalTorus.torusCoordinate, MonoidAlgebra.lift_of]
  change (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne
    (coordinateUnit κ n J B v hpos hneg hsupport hJ R)
      (Multiplicative.ofAdd (Finsupp.basisSingleOne k)) : W) = _
  rw [PrimitiveCharacters.basisCharacter_apply, coordinateUnit_val]

def sourceInclusion : S →ₐ[R] Localization.Away t :=
  ((AdjacentStratumLocalization.sourceEquiv (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) J v).restrictScalars R).toAlgHom.comp
    (OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport
      (old_independent κ n J B v hJ))

omit [Fintype κ] in
theorem row_original (k : Other n I ⊕ κ) :
    ((GlobalSelectedColumns.rowEquiv κ n I).symm k).val =
      IndependentChartPresentation.complementEmbedding κ n I k := by
  cases k <;> rfl

theorem open_coordinate (k : Q) :
    algebraMap W (Localization.Away t)
      (torusMap R κ n J B v hpos hneg hsupport hJ (OriginalTorus.torusCoordinate R Q k)) =
    sourceInclusion R κ n J B v hpos hneg hsupport hJ
      (Ideal.Quotient.mk (remainingIdeal R κ n I B) (OriginalTorus.torusCoordinate R Q k)) := by
  rw [torusMap_coordinate]
  change _ = AdjacentStratumLocalization.sourceEquiv (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) J v
      (OriginalRemainingCoordinates.inclusion R κ n I B hpos hneg hsupport
        (old_independent κ n J B v hJ) _)
  rw [OriginalRemainingCoordinates.inclusion_generator, row_original]
  exact (AdjacentStratumLocalization.source_original (Global R κ n B) (Fin n)
    (fun i => initial R κ n B (Sum.inl i)) J v
      (initial R κ n B (IndependentChartPresentation.complementEmbedding κ n I k.val))).symm

theorem open_torus :
    (IsScalarTower.toAlgHom R W (Localization.Away t)).comp
      (torusMap R κ n J B v hpos hneg hsupport hJ) =
    (sourceInclusion R κ n J B v hpos hneg hsupport hJ).comp
      (Ideal.Quotient.mkₐ R (remainingIdeal R κ n I B)) := by
  apply MonoidAlgebra.algHom_ext'
  apply MonoidHom.eq_of_eqOn_dense
    (PrimitiveCharacters.basis_generates (Finsupp.basisSingleOne : Basis Q ℤ (Q →₀ ℤ)))
  rintro _ ⟨k, rfl⟩
  exact open_coordinate R κ n J B v hpos hneg hsupport hJ k

variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))

def extension : S →+* W :=
  RegularPrincipalExtension.lift t
    (OriginalBoundaryBranches.parameter_regular R κ n J B v hpos hneg hsupport hJ hf)
    (remainingIdeal R κ n I B)
    (torusMap R κ n J B v hpos hneg hsupport hJ).toRingHom
    (sourceInclusion R κ n J B v hpos hneg hsupport hJ).toRingHom
    (fun a => AlgHom.congr_fun (open_torus R κ n J B v hpos hneg hsupport hJ) a)

theorem open_extension (a : S) :
    algebraMap W (Localization.Away t) (extension R κ n J B v hpos hneg hsupport hJ hf a) =
      sourceInclusion R κ n J B v hpos hneg hsupport hJ a :=
  RegularPrincipalExtension.open_lift _ _ _ _ _ _ a

theorem unit_extends (u : Sˣ) : IsUnit (extension R κ n J B v hpos hneg hsupport hJ hf u) :=
  u.isUnit.map (extension R κ n J B v hpos hneg hsupport hJ hf)

#print axioms old_independent
#print axioms torusMap
#print axioms torusMap_coordinate
#print axioms sourceInclusion
#print axioms row_original
#print axioms open_coordinate
#print axioms open_torus
#print axioms extension
#print axioms open_extension
#print axioms unit_extends
end Verification.OriginalRemainingExtension
