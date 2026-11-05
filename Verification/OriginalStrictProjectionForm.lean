/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictProjectionDetection

/-!
# Original Strict Projection Form

The actual coordinate projection is precisely its biproduct split projection, including the positive degree cast.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictProjectionForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

attribute [local instance] Abelian.hasFiniteBiproducts
variable (r : ℕ) (a : ActualCellThom.Index κ n B r)
variable (τ α : Type) [Fintype τ] [Fintype α] [LinearOrder α]
variable (ea : GlobalNormalFrame.ZeroLayer R κ n a.val B ≃ₐ[R] TorusThomInput.BaseRing R τ α)
variable (site : GrothendieckTopology Scheme.{0}) (M : ℤ → A)
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (V : LocalizedThomSections.Standard J L G R site M N)
variable (Z₀ : A) (W : GradedMilnorWittSheaf.Standard site N)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)
local notation "SourceCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r a


omit [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem projection (i : BinaryWordCoordinates.Index (Fintype.card α))
    (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) i≠0) :
    OriginalCoordinateProjectionSymbols.projection J L G R T κ n B hpos hneg hsupport hf hs r a τ α ea site M N V Z₀ W Q i hi=
    (OriginalStrictProjectionDetection.splitSource J L G R T κ n B hpos hneg hsupport hf hs r a τ α ea site M N V Z₀ W Q).hom ≫
      biproduct.π _ i ≫ eqToHom (if_neg hi) := by
  simp only [OriginalCoordinateProjectionSymbols.projection,OriginalStrictProjectionDetection.splitSource,
    StrictTorusSymbolRedegree.projection,StrictTorusSymbolRedegree.split,StrictTorusSymbolInput.positiveProjection,
    StrictTorusSymbolInput.projection,Iso.trans_hom,Category.assoc]

#print axioms projection
end Verification.OriginalStrictProjectionForm
