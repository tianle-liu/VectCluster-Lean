/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittCoefficientCoordinates
import Verification.WittTorusCharacters

/-!
# Original Witt Section Coordinates

Actual Witt sheaf sections of the original AS stratum. The isomorphism
uses its explicit affine-torus chart and the very same integral splitting
as the signed quotient, followed by ordinary Witt affine invariance.
-/
noncomputable section
open scoped Classical TensorProduct
namespace Verification.OriginalWittSectionCoordinates
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput Verification.OriginalWittQuotient
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)
variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (D : Symbols R W)
variable (T : TorusBasis R W D) (H : WittSheafAffineInvariance.Standard R W)

def torusToStratum :
    RingSection W (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B))) ≃+*
      RingSection W (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  (WittSheafAffineInvariance.polynomialEquiv R W H _ (IndependentChartIndex.Selected n I)
    (TorusSmooth.torus_smooth R _)).trans
    (WittSheafAffineInvariance.ringEquiv W
      (ExplicitStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm.toRingEquiv)

def equiv : Stratum (fun a v => B a (Sum.inl v)) I ⊗[ℤ] RingSection W R ≃+
    RingSection W (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  ((OriginalWittCoefficientCoordinates.equiv κ n I B hf hs
    (fun i j => IndependentChartIndex.independent_principal_zero κ n I B
      hpos hneg hsupport hI j.val i.val j.property i.property) (RingSection W R)).toAddEquiv.trans
        (T.equiv (Fin (ExplicitStratumTorus.torusRank κ n I B))).toAddEquiv).trans
          (torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H).toAddEquiv

theorem monomial (m : Bits (Fin n) κ) (a : RingSection W R) :
    equiv R κ n I B hf hs hpos hneg hsupport hI W D T H
      (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd m)) ⊗ₜ[ℤ] a) =
    torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H
      (T.equiv (Fin (ExplicitStratumTorus.torusRank κ n I B))
        (Finsupp.single (Multiplicative.ofAdd (OriginalWittCharacterSplitting.splitting κ n I B hf hs m).2)
          ((BinarySignedFiber.character (OriginalWittStratumFree.signs I)
            (Multiplicative.ofAdd (OriginalWittCharacterSplitting.splitting κ n I B hf hs m).1) : ℤ) • a))) := by
  change torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H
    (T.equiv _ (OriginalWittCoefficientCoordinates.equiv κ n I B hf hs _ (RingSection W R) _)) = _
  rw [OriginalWittCoefficientCoordinates.monomial]

#print axioms torusToStratum
#print axioms equiv
#print axioms monomial
end Verification.OriginalWittSectionCoordinates
