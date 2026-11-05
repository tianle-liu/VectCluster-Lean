/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualTorusThom
import Verification.ContractedSectionsTransport

/-!
# Actual Contracted Sections

Actual sections of each geometric cellular term, obtained by literal
precomposition through finite excision and framed purity, followed by the
standard contracted-section representation on a torus. The torus coordinate
isomorphisms are explicit parameters, so a compatible monomial choice can be
used for signature comparison. No differential identification is assumed.
-/
noncomputable section
namespace Verification.ActualContractedSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.ActualCellThom Verification.ExchangeOpenCover Verification.FrozenAcyclicCover
open Verification.IndependentChartIndex Verification.IndependentStratumTorus
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]

def sumHom (ι : Type) [Fintype ι] (X : ι → C) (M : C) :
    (⨁ X ⟶ M) ≃ₗ[ℤ] (∀ i, X i ⟶ M) :=
  AddEquiv.toIntLinearEquiv {
    toFun := fun f i => biproduct.ι X i ≫ f
    invFun := fun f => biproduct.desc f
    left_inv := fun f => by apply biproduct.hom_ext'; intro i; simp
    right_inv := fun f => by funext i; simp
    map_add' := fun f g => by funext i; simp }

variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (J : GrothendieckTopology Scheme.{0}) (M : ℤ → C)
variable (N : ℤ → Sheaf J (ModuleCat.{0} ℤ))
variable (T : ContractedSectionTheory.Standard G J M N)
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def sectionGroup (r : ℕ) (j : ℤ) (i : Index κ n B r) :=
  (N (j-r)).val.obj (Opposite.op (RealTorusScheme.torus (Fin (torusRank κ n i.val B))))

def localEvaluationOn (r : ℕ) (j : ℤ) (i : Index κ n B r)
    (e : localThom G ℝ κ n B r i ≅ TorusThomInput.thom ℝ (Selected n i.val)
      (Selected n i.val) (Fin (torusRank κ n i.val B)) G) :
    (ActualCellTerms.localTerm G ℝ κ n B r i ⟶ M j) ≃ₗ[ℤ] sectionGroup J N κ n B r j i := by
  have hc : Fintype.card (Selected n i.val) = r := (Fintype.card_coe i.val).trans i.property.1
  have z := ContractedSectionsTransport.evaluateOn G J M N T (Selected n i.val) (Selected n i.val)
      (Fin (torusRank κ n i.val B)) j (localThom G ℝ κ n B r i) e
  change ((DerivedCategory.homologyFunctor C (-(Fintype.card (Selected n i.val) : ℤ))).obj
    (localThom G ℝ κ n B r i) ⟶ M j) ≃ₗ[ℤ]
    (N (j - Fintype.card (Selected n i.val))).val.obj
      (Opposite.op (RealTorusScheme.torus (Fin (torusRank κ n i.val B)))) at z
  rw [hc] at z
  exact z

variable (E : OpenConeExcision.StandardExcision G)
variable (P : CoordinatePurityInput.StandardPurity ℝ G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def termEvaluationOn (r : ℕ) (j : ℤ)
    (e : ∀ i : Index κ n B r, localThom G ℝ κ n B r i ≅
      TorusThomInput.thom ℝ (Selected n i.val) (Selected n i.val)
        (Fin (torusRank κ n i.val B)) G) :
    ((GeometricCellularSource.source ℝ G κ n B).X r ⟶ M j) ≃ₗ[ℤ]
      (∀ i : Index κ n B r, sectionGroup J N κ n B r j i) :=
  (HomIntegerIso.precompose (ActualCellTerms.termIso G E ℝ κ n B P hpos hneg hsupport hf hs r)
      (M j)).trans ((sumHom (Index κ n B r) (ActualCellTerms.localTerm G ℝ κ n B r) (M j)).trans
        (LinearEquiv.piCongrRight (fun i => localEvaluationOn G J M N T κ n B r j i (e i))))

def termEvaluation (r : ℕ) (j : ℤ) :
    ((GeometricCellularSource.source ℝ G κ n B).X r ⟶ M j) ≃ₗ[ℤ]
      (∀ i : Index κ n B r, sectionGroup J N κ n B r j i) :=
  termEvaluationOn G J M N T κ n B E P hpos hneg hsupport hf hs r j
    (ActualTorusThom.thomIso G ℝ κ n B hpos hneg hsupport hf hs r)

#print axioms sumHom
#print axioms sectionGroup
#print axioms localEvaluationOn
#print axioms termEvaluationOn
#print axioms termEvaluation
end Verification.ActualContractedSections
