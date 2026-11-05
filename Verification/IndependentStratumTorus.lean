/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentStratumCoordinates
import Verification.ActualTransversePairSmooth
import Verification.PrimitiveTorusRank

/-!
# Independent Stratum Torus

AS is applied to the actual selected columns. It produces a coefficient-
preserving torus coordinate isomorphism of every original zero stratum and
the exact dimension d-2|I|, without a supplied stratum decomposition.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.IndependentStratumTorus
open CategoryTheory
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.GlobalExchangeSmooth Verification.ActualOpenChart
open Verification.ExchangeOpenCover Verification.PrimitiveTorusRank
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def torusRank : ℕ := Module.finrank ℤ (((Other n I ⊕ κ) →₀ ℤ) ⧸ LinearMap.range (selectedMap κ n B I))

variable (hf : Function.Injective (selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))

def fiberEquiv : ExchangeTransverseSlice.Fiber
    (characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)) ≃ₐ[R]
      MonoidAlgebra R (Multiplicative (Fin (torusRank κ n I B) →₀ ℤ)) :=
  (Ideal.quotientEquivAlgOfEq R (ActualTransversePairSmooth.fiberIdeal_eq R
    (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B))).trans
      ((PrimitiveCharacters.primitive_prescribed_fiber (R := R) (selectedMap κ n B I)
        hf hs Finsupp.basisSingleOne (fun _ => -1)).some.trans
          (quotientTorusEquiv R (selectedMap κ n B I) hs))

include hf hs in
omit [CommRing R] in
theorem rank_formula : torusRank κ n I B + 2 * I.card = n + Fintype.card κ := by
  have hr := quotient_rank (selectedMap κ n B I) Finsupp.basisSingleOne hf hs
  have hc : Fintype.card (Selected n I) = I.card := Fintype.card_coe I
  have hp : Fintype.card (Selected n I) + Fintype.card (Other n I) = n := by
    simpa only [Fintype.card_fin,Fintype.card_sum] using (Fintype.card_congr (split n I)).symm
  rw [Fintype.card_sum,hc] at hr
  rw [hc] at hp
  unfold torusRank
  omega

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)

def affineTorusEquiv : GlobalNormalFrame.ZeroLayer R κ n I B ≃ₐ[R]
    MvPolynomial (Selected n I)
      (MonoidAlgebra R (Multiplicative (Fin (torusRank κ n I B) →₀ ℤ))) :=
  (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI).trans
    (MvPolynomial.mapAlgEquiv (Selected n I) (fiberEquiv R κ n I B hf hs))

def schemeIso : AlgebraicGeometry.Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B)) ≅
    AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Selected n I)
      (MonoidAlgebra R (Multiplicative (Fin (torusRank κ n I B) →₀ ℤ))))) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).toRingEquiv.toCommRingCatIso.symm.op

#print axioms torusRank
#print axioms fiberEquiv
#print axioms rank_formula
#print axioms affineTorusEquiv
#print axioms schemeIso
end Verification.IndependentStratumTorus
