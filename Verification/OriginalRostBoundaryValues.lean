/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRostBoundaryCharts
import Verification.OriginalRostComponentValues
import Verification.RostChowBlock

/-!
# Original Rost Boundary Values

Pointwise residues of the actual exchange support row. The first
boundary is the original row block, normalized only by degree equalities.
Its source/target ring changes are the constructed adjacent-stratum maps.
-/
noncomputable section
namespace Verification.OriginalRostBoundaryValues
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "A" => Global R κ n B
local notation "xs" => (initial R κ n B ∘ Sum.inl)
local notation "Allowed" => Independent (laterWeights κ n B)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I, Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I ⊕ κ) m), ∀ i, IsUnit ((sm.a i).natAbs : R))


variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T) (P : RostPrincipalLocalizationInput.Theory T)
variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : RostCanonicalCoefficients.UnitsNaturality T F U)
variable (C : OriginalRostBoundaryCharts.Standard R κ n B hpos hneg hsupport hf htame T S P)

include hpos hneg hsupport hf htame in
theorem source_smooth (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    Algebra.Smooth R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  obtain ⟨m,sm,he⟩ := htame I hI
  exact OriginalRostUnitTerms.stratum_smooth R κ n B hpos hneg hsupport I hI (hf I hI) sm he

include hpos hneg hsupport hf htame in
theorem open_smooth (J : Finset (Fin n)) (hJ : Independent (laterWeights κ n B) J) (v : J) :
    Algebra.Smooth R (RostPrincipalLocalizationInput.OpenRing
      (RostSupportDivisorInput.Face A (Fin n) xs J v)
      (RostSupportDivisorInput.parameter A (Fin n) xs J v)) := by
  letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J hJ v
  letI : Algebra.Smooth (RostSupportDivisorInput.Face A (Fin n) xs J v)
    (RostPrincipalLocalizationInput.OpenRing (RostSupportDivisorInput.Face A (Fin n) xs J v)
      (RostSupportDivisorInput.parameter A (Fin n) xs J v)) :=
    Algebra.Smooth.of_isLocalization_Away (RostSupportDivisorInput.parameter A (Fin n) xs J v)
  exact Algebra.Smooth.comp R (RostSupportDivisorInput.Face A (Fin n) xs J v) _

variable (p : ℕ) (I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p)
variable (J : PrimeLayerCover.Index (Independent (laterWeights κ n B)) (p+1))

def block : RostCanonicalCoefficients.Sections T (GlobalNormalFrame.ZeroLayer R κ n I.val B) 1 ⟶
    RostCanonicalCoefficients.Sections T (GlobalNormalFrame.ZeroLayer R κ n J.val B) 0 :=
  RostChowBlock.block T A (Fin n) xs Allowed p I J
    (OriginalRostSupport.support T S R κ n B hpos hneg hsupport hf htame (p+1))

include C in
theorem nonincident (h : ¬ I.val ⊆ J.val) :
    block R κ n B hpos hneg hsupport hf htame T S p I J = 0 := by
  unfold block RostChowBlock.block
  rw [OriginalRostBoundaryCharts.nonincident R κ n B hpos hneg hsupport hf htame T S P C
    (p+1) p I J h]
  simp

include C in
theorem adjacent (v : J.val) (h : I.val = J.val.erase v.val) :
    letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    let e : RostSupportDivisorInput.Coordinates A (Fin n) xs I.val J.val v :=
      h ▸ OriginalRostBoundaryCharts.coordinates R κ n B J.val v
    block R κ n B hpos hneg hsupport hf htame T S p I J =
      (RostCanonicalCoefficients.transport T e.source.toRingEquiv 1).toAddCommGrpIso.hom ≫
      P.boundary R (RostSupportDivisorInput.Face A (Fin n) xs J.val v)
        (RostSupportDivisorInput.parameter A (Fin n) xs J.val v)
        (OriginalRostBoundaryCharts.face_regular R κ n B hpos hneg hsupport hf J.val J.property.2 v) 1 ≫
      (RostCanonicalCoefficients.transport T e.target.toRingEquiv 0).toAddCommGrpIso.hom := by
  letI := OriginalRostBoundaryCharts.globalSmooth R κ n B hpos hneg hsupport hf htame
  letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  unfold block RostChowBlock.block
  rw [OriginalRostBoundaryCharts.adjacent R κ n B hpos hneg hsupport hf htame T S P C
    (p+1) p I J v h]
  exact RostChowBlock.localBoundary T A (Fin n) xs Allowed p I J P R v _ _



include C UN in
theorem component_value (v : J.val) (h : I.val = J.val.erase v.val) (j : (OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2).Index)
    (a : RostCanonicalCoefficients.Sections T (GlobalNormalFrame.ZeroLayer R κ n I.val B) 1) :
    letI := source_smooth R κ n B hpos hneg hsupport hf htame I.val I.property.2
    letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    letI := open_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
    let e : RostSupportDivisorInput.Coordinates A (Fin n) xs I.val J.val v :=
      h ▸ OriginalRostBoundaryCharts.coordinates R κ n B J.val v
    (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z J.val J.property.2).hom
      (block R κ n B hpos hneg hsupport hf htame T S p I J a)
      (ConnectedComponents.mk (OriginalRostComponentValues.point R κ n B hpos hneg hsupport hf htame J.val J.property.2 j)) =
    RostPrincipalResidueInput.genericResidue T P F Z E U R
      (RostSupportDivisorInput.Face A (Fin n) xs J.val v)
      (RostSupportDivisorInput.parameter A (Fin n) xs J.val v)
      (OriginalRostBoundaryCharts.face_regular R κ n B hpos hneg hsupport hf J.val J.property.2 v)
      (PrimeSpectrum.comap e.target.toRingEquiv.toRingHom
        (OriginalRostComponentValues.point R κ n B hpos hneg hsupport hf htame J.val J.property.2 j))
      (RostCanonicalCoefficients.transportPoint_minimal e.target.toRingEquiv _
        (OriginalRostComponentValues.point_minimal R κ n B hpos hneg hsupport hf htame J.val J.property.2 j))
      (Additive.ofMul (Units.map e.source.toRingEquiv.toMonoidHom
        (Additive.toMul ((U.units R (GlobalNormalFrame.ZeroLayer R κ n I.val B)).hom a)))) := by
  letI := source_smooth R κ n B hpos hneg hsupport hf htame I.val I.property.2
  letI := OriginalRostBoundaryCharts.face_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  letI := open_smooth R κ n B hpos hneg hsupport hf htame J.val J.property.2 v
  let e : RostSupportDivisorInput.Coordinates A (Fin n) xs I.val J.val v :=
    h ▸ OriginalRostBoundaryCharts.coordinates R κ n B J.val v
  rw [adjacent R κ n B hpos hneg hsupport hf htame T S P C p I J v h]
  exact RostBoundaryTransportValues.component_value T P F Z E U UN R
    (RostSupportDivisorInput.Face A (Fin n) xs J.val v)
    (GlobalNormalFrame.ZeroLayer R κ n I.val B) (GlobalNormalFrame.ZeroLayer R κ n J.val B)
    (RostSupportDivisorInput.parameter A (Fin n) xs J.val v)
    (OriginalRostBoundaryCharts.face_regular R κ n B hpos hneg hsupport hf J.val J.property.2 v)
    e.source.toRingEquiv e.target.toRingEquiv (OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2).Factor (OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame J.val J.property.2).equiv j a

#print axioms source_smooth
#print axioms open_smooth
#print axioms block
#print axioms nonincident
#print axioms adjacent
#print axioms component_value
end Verification.OriginalRostBoundaryValues
