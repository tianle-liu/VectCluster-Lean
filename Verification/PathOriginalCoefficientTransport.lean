/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientQuotient
import Verification.OriginalFiberPartnerQuotient

/-!
# Path Original Coefficient Transport

A generator-preserving equivalence of literal path layers identifies their
actual selected-partner quotients, hence their canonical coefficient fibers.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalCoefficientTransport
open Verification.PathCompression Verification.PathLiteralStratum
open Verification.PathSignedStratumCoefficients Verification.PathCoefficientProjection
open Verification.PathOriginalStratumTransport Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover Verification.IndependentBasicOpen
open Verification.ExchangeOpenCover
variable (R S κ : Type) [CommRing R] [CommRing S] [Algebra R S] [Fintype κ]
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : S)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (e : Layer S hI a b ≃ₐ[R] GlobalNormalFrame.ZeroLayer R κ n (mutableSet n I) B)
variable (hy : ∀ i : I, e (layerY S hI a b (mutableIndex hI i))=
  OriginalFiberPartnerProjection.partner R κ n (mutableSet n I) B (selectedEquiv hI i))

include hy in
theorem map_partnerIdeal : (partnerIdeal hI S a b).map e.toRingHom=
    OriginalFiberPartnerQuotient.partnerIdeal R κ n (mutableSet n I) B := by
  rw [partnerIdeal,Ideal.map_span,OriginalFiberPartnerQuotient.partnerIdeal]
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨selectedEquiv hI i,(hy i).symm⟩
  · rintro ⟨i,rfl⟩
    refine ⟨layerY S hI a b (mutableIndex hI ((selectedEquiv hI).symm i)),
      ⟨(selectedEquiv hI).symm i,rfl⟩,?_⟩
    change e (layerY S hI a b (mutableIndex hI ((selectedEquiv hI).symm i))) = _
    rw [hy,Equiv.apply_symm_apply]

def quotientEquiv :
    (Layer S hI a b ⧸ partnerIdeal hI S a b) ≃ₐ[R]
      (GlobalNormalFrame.ZeroLayer R κ n (mutableSet n I) B ⧸
        OriginalFiberPartnerQuotient.partnerIdeal R κ n (mutableSet n I) B) :=
  Ideal.quotientEquivAlg _ _ e (map_partnerIdeal R S κ hI a b B e hy).symm

theorem quotientEquiv_mk (c : Layer S hI a b) :
    quotientEquiv R S κ hI a b B e hy (Ideal.Quotient.mk (partnerIdeal hI S a b) c)=
      Ideal.Quotient.mk (OriginalFiberPartnerQuotient.partnerIdeal R κ n (mutableSet n I) B) (e c) := rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hD : Independent (laterWeights κ n B) (mutableSet n I))

abbrev Fiber := ExchangeTransverseSlice.Fiber
  (ActualOpenChart.characters R (Selected n (mutableSet n I))
    (Other n (mutableSet n I) ⊕ κ) (Other n (mutableSet n I))
    (IndependentChartIndex.matrix κ n (mutableSet n I) B))

def coefficientEquiv : Coefficients S hI a b ≃ₐ[R] Fiber (I := I) R κ B :=
  ((PathCoefficientQuotient.equiv S hI a b).restrictScalars R).symm.trans
    ((quotientEquiv R S κ hI a b B e hy).trans
      (OriginalFiberPartnerQuotient.quotientEquiv R κ n (mutableSet n I) B hpos hneg hsupport hD))

theorem coefficientEquiv_projection (c : Layer S hI a b) :
    coefficientEquiv R S κ hI a b B e hy hpos hneg hsupport hD (projection hI S a b c)=
      OriginalCanonicalFiberProjection.projection R κ n (mutableSet n I) B hpos hneg hsupport hD (e c) := by
  rw [← PathCoefficientQuotient.equiv_mk S hI a b c]
  change OriginalFiberPartnerQuotient.quotientEquiv R κ n (mutableSet n I) B hpos hneg hsupport hD
    (quotientEquiv R S κ hI a b B e hy
      ((PathCoefficientQuotient.equiv S hI a b).symm
        ((PathCoefficientQuotient.equiv S hI a b) (Ideal.Quotient.mk _ c))))=_
  rw [AlgEquiv.symm_apply_apply,quotientEquiv_mk,OriginalFiberPartnerQuotient.quotientEquiv_mk]

#print axioms map_partnerIdeal
#print axioms quotientEquiv
#print axioms quotientEquiv_mk
#print axioms Fiber
#print axioms coefficientEquiv
#print axioms coefficientEquiv_projection
end Verification.PathOriginalCoefficientTransport
