/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostComponentZero
import Verification.OriginalStratumUnits

/-!
# Original Rost Component Terms

The terminal term in the original Milnor support row is identified
with integer functions on the actual connected components of each original
stratum. The zero-layer fields and the topological component equivalence
are constructed internally. Boundary compatibility remains a separate step.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalRostComponentTerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))


variable (Z : RostWeightZero.IntegralConvention T)

/-- A choice retains the actual ring decomposition as data, rather than
choosing an arbitrary additive-group isomorphism from a Nonempty proof. -/
structure DomainProduct (A : Type) [CommRing A] where
  Index : Type
  [finite : Fintype Index]
  Factor : Index → Type
  [commRing : ∀ j,CommRing (Factor j)]
  [domain : ∀ j,IsDomain (Factor j)]
  equiv : A ≃+* ∀ j,Factor j

attribute [instance] DomainProduct.finite DomainProduct.commRing DomainProduct.domain

def decomposition (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    DomainProduct (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  Classical.choice (by
    obtain ⟨m,sm,he⟩ := htame I hI
    obtain ⟨J,hJ,L,hL,aL,e,_⟩ := OriginalStratumUnits.component_units R κ n B hpos hneg hsupport I hI
      (hf I hI) sm he
    letI := hJ
    letI := hL
    letI := aL
    letI : Fintype J := Fintype.ofFinite J
    exact ⟨{ Index := J, Factor := _, equiv := e }⟩)

def stratumComponents (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))) 0).homology 0 ≅
      AddCommGrp.of (ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B))→ℤ) :=
  let D := decomposition R κ n B hpos hneg hsupport hf htame I hI
  RostComponentZero.componentIso T F Z D.Factor D.equiv

def terminalIso (p : ℕ)
    (D : RostSupportInput.Data T (Global R κ n B) (Fin n)
      (fun i => initial R κ n B (Sum.inl i)) (Independent (laterWeights κ n B)) p) :
    D.row.X p ≅ AddCommGrp.of
      (∀ I : PrimeLayerCover.Index (Independent (laterWeights κ n B)) p,
        ConnectedComponents (PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I.val B))→ℤ) := by
  refine D.rowTerm p ≪≫ ?_
  apply AddEquiv.toAddCommGrpIso
  apply AddEquiv.piCongrRight
  intro I
  have hc : (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I.val B)))
      ((p:ℤ)-p)).homology 0 =
    (T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I.val B))) 0).homology 0 :=
    congrArg (fun s => (T.cycles (Spec (CommRingCat.of
      (GlobalNormalFrame.ZeroLayer R κ n I.val B))) s).homology 0) (sub_self (p:ℤ))
  exact (eqToIso hc).addCommGroupIsoToAddEquiv.trans
    (stratumComponents T F R κ n B hpos hneg hsupport hf htame Z I.val I.property.2).addCommGroupIsoToAddEquiv

#print axioms DomainProduct
#print axioms decomposition
#print axioms stratumComponents
#print axioms terminalIso
end Verification.OriginalRostComponentTerms
