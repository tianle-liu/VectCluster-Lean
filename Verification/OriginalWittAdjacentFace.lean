/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittAdjacentMonomialResidue
import Verification.GroupRingQuotientTensorExt
import Verification.WittSheafAffineProjection

/-!
# Original Witt Adjacent Face

Every adjacent map of the literal integer quotient complex, extended
by arbitrary actual Witt coefficients, agrees with the genuine geometric
Witt Laurent residue. The agreement is proved on monomials and extended
by quotient and tensor induction.
-/
noncomputable section
open scoped Classical TensorProduct
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
namespace Verification.OriginalWittAdjacentFace
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


variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (D : Symbols R W)
variable (T : TorusBasis R W D) (H : WittSheafAffineInvariance.Standard R W)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (E : Comparison R W site N) (K : StandardThomContractionNormalization.Grading R site N)
variable (Norm : LaurentNormalization R W D site N E K)


def integerFace (A : Type) [AddCommGroup A] :
    (OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i)) (J.erase v.val) ⊗[ℤ] A) →ₗ[ℤ]
      (OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i)) J ⊗[ℤ] A) :=
  TensorProduct.map (OriginalWittQuotient.residue (fun a i => B a (Sum.inl i))
    (J.erase v.val) J v.val (Finset.erase_subset _ _) (Finset.not_mem_erase _ _)
      (fun i => IndependentChartIndex.independent_principal_zero κ n J B hpos hneg hsupport hJ
        v.val i.val v.property (Finset.mem_of_mem_erase i.property))) (LinearMap.id : A →ₗ[ℤ] A)

omit [Fintype κ] in
theorem integerFace_monomial (A : Type) [AddCommGroup A]
    (m : OriginalWittQuotient.Bits (Fin n) κ) (a : A) :
    integerFace κ n J B v hpos hneg hsupport hJ A
      (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a) =
      if m (Sum.inl v.val)=0 then 0 else
        Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a := by
  rw [integerFace,TensorProduct.map_tmul,OriginalWittQuotient.residue_monomial,
    OriginalWittQuotient.weight_coordinate]
  change (((m (Sum.inl v.val)).val : ℤ) • _) ⊗ₜ[ℤ] a = _
  by_cases hm : m (Sum.inl v.val)=0
  · simp [hm]
  · have hv : (m (Sum.inl v.val)).val=1 := by
      have hlt := ZMod.val_lt (m (Sum.inl v.val))
      have hn : (m (Sum.inl v.val)).val ≠ 0 := by
        intro h
        exact hm ((ZMod.val_eq_zero _).mp h)
      omega
    simp [hm,hv]

include Norm in
theorem comparison (q : ℤ) :
    (WittSheafLaurentResidue.residue R W site N E K New
      (OriginalWittAdjacentMonomialResidue.fiberSmooth R κ n J B hfJ hsJ) q).comp
      ((pullback W (src).toRingHom).toAddMonoidHom.comp
        (OriginalWittSectionCoordinates.equiv R κ n (J.erase v.val) B hfI hsI hpos hneg hsupport hI W D T H).toAddMonoidHom) =
      (pullback W (proj).toRingHom).toAddMonoidHom.comp
        ((OriginalWittSectionCoordinates.equiv R κ n J B hfJ hsJ hpos hneg hsupport hJ W D T H).toAddMonoidHom.comp
          (integerFace κ n J B v hpos hneg hsupport hJ (RingSection W R)).toAddMonoidHom) := by
  apply GroupRingQuotientTensorExt.ext
  intro m a
  change WittSheafLaurentResidue.residue R W site N E K New _ q
    (pullback W (src).toRingHom (OriginalWittSectionCoordinates.equiv R κ n (J.erase v.val) B hfI hsI hpos hneg hsupport hI W D T H _))=_
  refine (OriginalWittAdjacentMonomialResidue.monomial R κ n J B v hD hfI hsI hfJ hsJ
    hpos hneg hsupport hI hJ W D T H site N E K Norm (Multiplicative.toAdd m) q a).trans ?_
  change _=pullback W (proj).toRingHom
    (OriginalWittSectionCoordinates.equiv R κ n J B hfJ hsJ hpos hneg hsupport hJ W D T H
      (integerFace κ n J B v hpos hneg hsupport hJ (RingSection W R)
        (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ m) ⊗ₜ[ℤ] a)))
  refine Eq.trans ?_ (congrArg (fun x => pullback W (proj).toRingHom
    (OriginalWittSectionCoordinates.equiv R κ n J B hfJ hsJ hpos hneg hsupport hJ W D T H x))
      (integerFace_monomial κ n J B v hpos hneg hsupport hJ (RingSection W R) (Multiplicative.toAdd m) a)).symm
  split_ifs
  · exact ((congrArg (pullback W (proj).toRingHom)
      (OriginalWittSectionCoordinates.equiv R κ n J B hfJ hsJ hpos hneg hsupport hJ W D T H).map_zero).trans
        (pullback W (proj).toRingHom).map_zero).symm
  · rfl

#print axioms integerFace
#print axioms integerFace_monomial
#print axioms comparison
end Verification.OriginalWittAdjacentFace
