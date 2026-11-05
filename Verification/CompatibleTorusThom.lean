/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualContractedSections
import Verification.ExplicitStratumTorus

/-!
# Compatible Torus Thom

The actual geometric Thom term is transported through a supplied affine
coefficient equivalence. Its explicit AS specialization uses exactly the
monomial splitting retained in the original sign-label coordinates.
-/
noncomputable section
namespace Verification.CompatibleTorusThom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.ActualCellThom Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def thomIsoOn (r : ℕ) (i : Index κ n B r) (τ α : Type)
    (e : GlobalNormalFrame.ZeroLayer R κ n i.val B ≃ₐ[R] TorusThomInput.BaseRing R τ α) :
    localThom G R κ n B r i ≅ TorusThomInput.thom R (Selected n i.val) τ α G :=
  CoordinatePairEquiv.relativeIso MvPolynomial.X MvPolynomial.X
    (MvPolynomial.mapAlgEquiv (Selected n i.val) e).toRingEquiv
    (fun j => MvPolynomial.map_X _ j) G

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def explicitIso (r : ℕ) (i : Index κ n B r) : localThom G R κ n B r i ≅
    TorusThomInput.thom R (Selected n i.val) (Selected n i.val)
      (Fin (IndependentStratumTorus.torusRank κ n i.val B)) G :=
  thomIsoOn G R κ n B r i (Selected n i.val) (Fin (ExplicitStratumTorus.torusRank κ n i.val B))
    (ExplicitStratumTorus.affineTorusEquiv R κ n i.val B (hf i.val i.property.2)
      (hs i.val i.property.2) hpos hneg hsupport i.property.2)

variable (J : GrothendieckTopology Scheme.{0}) (M : ℤ → C)
variable (N : ℤ → Sheaf J (ModuleCat.{0} ℤ))
variable (T : ContractedSectionTheory.Standard G J M N)
variable (E : OpenConeExcision.StandardExcision G)
variable (P : CoordinatePurityInput.StandardPurity ℝ G)

def termEvaluation (r : ℕ) (j : ℤ) :
    ((GeometricCellularSource.source ℝ G κ n B).X r ⟶ M j) ≃ₗ[ℤ]
      (∀ i : Index κ n B r, ActualContractedSections.sectionGroup J N κ n B r j i) :=
  ActualContractedSections.termEvaluationOn G J M N T κ n B E P hpos hneg hsupport hf hs r j
    (explicitIso G ℝ κ n B hpos hneg hsupport hf hs r)

#print axioms thomIsoOn
#print axioms explicitIso
#print axioms termEvaluation
end Verification.CompatibleTorusThom
