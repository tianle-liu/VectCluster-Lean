/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostPrincipalResidueInput
import Verification.RostComponentEvaluation
import Verification.BranchComponentPullback

/-!
# Rost Reduced Divisor Residues

The ordinary principal residue on every actual component of a reduced
product divisor. Generic primes, DVRs and multiplicity one are constructed
from the quotient ring. The component-selector values are derived, and are
not additional fields of the cited Rost input.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace Verification.RostReducedDivisorResidues
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
open Verification.RostPrincipalLocalizationInput (OpenRing ClosedRing)
open Verification.RostPrincipalResidueInput
open Verification.ReducedBoundaryBranchOrder
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : GenericZeroEvaluation T F Z) (U : OriginalRostUnitTerms.UnitsConvention T)
variable (N : Normalization T P F Z E U)
variable (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
variable (t : A) (ht : IsRegular t) [Algebra.Smooth k (OpenRing A t)]
variable [IsNoetherianRing A]
variable {J : Type} (D : J → Type) [∀ j,CommRing (D j)] [∀ j,IsDomain (D j)]
variable (e : ClosedRing A t ≃+* ∀ j,D j) (j : J)

omit [Field k] [Algebra k A] [Algebra.Smooth k A] [Algebra.Smooth k (OpenRing A t)]
    [IsNoetherianRing A] in
theorem sourcePrime_branch :
    (sourcePrime A t (RostComponentEvaluation.point D e j)).asIdeal = branch A t D e j := rfl

/-- The j-th actual generic value of the principal boundary. -/
def residue : Additive (OpenRing A t)ˣ →+ ℤ :=
  genericResidue T P F Z E U k A t ht (RostComponentEvaluation.point D e j)
    (RostComponentEvaluation.point_minimal D e j)

include N in
theorem parameter (u : (OpenRing A t)ˣ)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) t) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) = 1 := by
  letI : IsDomain (Local A t (RostComponentEvaluation.point D e j)) :=
    localDomain A t D e j ht.left.isSMulRegular
  letI : IsDiscreteValuationRing (Local A t (RostComponentEvaluation.point D e j)) :=
    discreteValuation A t D e j ht.left.isSMulRegular
  exact residue_parameter T P F Z E U k A t ht N
    (RostComponentEvaluation.point D e j) (RostComponentEvaluation.point_minimal D e j)
    (parameter_nonzero A t D e j ht.left.isSMulRegular) u hu
    (maximalIdeal_generated A t D e j)

include N in
theorem not_mem (u : (OpenRing A t)ˣ) (a : A)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) a)
    (ha : a ∉ branch A t D e j) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) = 0 := by
  letI : IsDomain (Local A t (RostComponentEvaluation.point D e j)) :=
    localDomain A t D e j ht.left.isSMulRegular
  letI : IsDiscreteValuationRing (Local A t (RostComponentEvaluation.point D e j)) :=
    discreteValuation A t D e j ht.left.isSMulRegular
  exact residue_not_mem T P F Z E U k A t ht N
    (RostComponentEvaluation.point D e j) (RostComponentEvaluation.point_minimal D e j)
    (parameter_nonzero A t D e j ht.left.isSMulRegular) u a hu ha

include N in
theorem selector_zero (u : (OpenRing A t)ˣ) (a : A)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) (BoundaryComponentSelector.element a t))
    (ha : projection A t D e j a = 0) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) = 0 := by
  apply not_mem T P F Z E U N k A t ht D e j u (BoundaryComponentSelector.element a t) hu
  change projection A t D e j (BoundaryComponentSelector.element a t) ≠ 0
  rw [BoundaryComponentSelector.projection_element, ha, sub_zero]
  exact one_ne_zero

include N in
theorem selector_one (u : (OpenRing A t)ˣ) (a : A)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) (BoundaryComponentSelector.element a t))
    (ha : a * a = a) (hp : projection A t D e j a ≠ 0) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) = 1 := by
  letI : IsDomain (Local A t (RostComponentEvaluation.point D e j)) :=
    localDomain A t D e j ht.left.isSMulRegular
  letI : IsDiscreteValuationRing (Local A t (RostComponentEvaluation.point D e j)) :=
    discreteValuation A t D e j ht.left.isSMulRegular
  let L := Local A t (RostComponentEvaluation.point D e j)
  let hnt : algebraMap A L t ≠ 0 := parameter_nonzero A t D e j ht.left.isSMulRegular
  change genericResidue T P F Z E U k A t ht _ _ _ = _
  rw [N.dvr k A t ht _ _ hnt]
  apply DVRFractionOrder.openOrder_of_image_parameter _ _ _ _ _ u
  · rw [hu,DVRFractionOrder.openMap_algebraMap]
    have hlocal : algebraMap A L a = 1 :=
      BoundaryComponentSelector.local_idempotent_one A t D e j a ha hp
    have hs : algebraMap A L (BoundaryComponentSelector.element a t) = algebraMap A L t := by
      rw [BoundaryComponentSelector.map_element,BoundaryComponentSelector.element,
        hlocal,sub_self,zero_add,one_mul]
    rw [hs]
  · exact maximalIdeal_generated A t D e j

include N in
theorem selector_indicator (u : (OpenRing A t)ˣ) (a : A)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) (BoundaryComponentSelector.element a t))
    (ha : a * a = a) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) =
      @ite ℤ (projection A t D e j a = 0) (Classical.propDecidable _) 0 1 := by
  classical
  by_cases hp : projection A t D e j a = 0
  · rw [if_pos hp]
    exact selector_zero T P F Z E U N k A t ht D e j u a hu hp
  · rw [if_neg hp]
    exact selector_one T P F Z E U N k A t ht D e j u a hu ha hp

omit [IsNoetherianRing A] in
theorem component_value [Fintype J] (u : Additive (OpenRing A t)ˣ) :
    residue T P F Z E U k A t ht D e j u =
      (RostComponentZero.componentIso T F Z D e).hom (unitBoundary T P U k A t ht u)
        (ConnectedComponents.mk (RostComponentEvaluation.point D e j)) :=
  RostComponentEvaluation.component_value T F Z E D e j _

variable {S I : Type} [CommRing S] [Finite I]
variable (C : I → Type) [∀ i,CommRing (C i)] (Ciso : S ≃+* ∀ i,C i) (f : S →+* A)

include N in
theorem selector_component_pullback (i : I) (u : (OpenRing A t)ˣ)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t)
      (BoundaryComponentSelector.element (f (ProductComponentIdempotents.indicator C Ciso i)) t)) :
    residue T P F Z E U k A t ht D e j (Additive.ofMul u) =
      @ite ℤ (BranchComponentPullback.sourcePoint t D e j f ∈
        Set.range (StratumComponents.componentMap C Ciso i)) (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hp : BranchComponentPullback.sourcePoint t D e j f ∈
      Set.range (StratumComponents.componentMap C Ciso i)
  · rw [if_pos hp]
    apply selector_one T P F Z E U N k A t ht D e j u
      (f (ProductComponentIdempotents.indicator C Ciso i)) hu
    · rw [← map_mul,ProductComponentIdempotents.indicator_idempotent]
    · exact (BranchComponentPullback.indicator_nonzero_iff t D e j C Ciso f i).mpr hp
  · rw [if_neg hp]
    apply selector_zero T P F Z E U N k A t ht D e j u
      (f (ProductComponentIdempotents.indicator C Ciso i)) hu
    exact Classical.not_not.mp (fun hn => hp
      ((BranchComponentPullback.indicator_nonzero_iff t D e j C Ciso f i).mp hn))

include N in
theorem boundary_component_pullback [Fintype J] (i : I) (u : (OpenRing A t)ˣ)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t)
      (BoundaryComponentSelector.element (f (ProductComponentIdempotents.indicator C Ciso i)) t)) :
    (RostComponentZero.componentIso T F Z D e).hom
        (unitBoundary T P U k A t ht (Additive.ofMul u))
        (ConnectedComponents.mk (RostComponentEvaluation.point D e j)) =
      @ite ℤ (BranchComponentPullback.sourcePoint t D e j f ∈
        Set.range (StratumComponents.componentMap C Ciso i)) (Classical.propDecidable _) 1 0 := by
  rw [← component_value T P F Z E U k A t ht D e j]
  exact selector_component_pullback T P F Z E U N k A t ht D e j C Ciso f i u hu

#print axioms sourcePrime_branch
#print axioms residue
#print axioms parameter
#print axioms not_mem
#print axioms selector_zero
#print axioms selector_one
#print axioms selector_indicator
#print axioms component_value
#print axioms selector_component_pullback
#print axioms boundary_component_pullback
end Verification.RostReducedDivisorResidues
