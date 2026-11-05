/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualSheafContractionRestriction

/-!
# Actual Contraction Section Naturality

Under the proved actual AS hypotheses, the actual reduced character
restriction is the ordinary pullback on the coefficient sheaf's u=1 kernel.
Both old and new smoothness premises are supplied internally.
-/
noncomputable section
namespace Verification.ActualContractionSectionNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R ι κ τ : Type) [CommRing R] [Fintype ι] [Fintype κ]
variable (inc : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (v : ι)
variable (hf : Function.Injective (ActualOpenGeometry.columnMap ι κ τ B))
variable (hs : FreezingLattice.Saturated (LinearMap.range (ActualOpenGeometry.columnMap ι κ τ B)))
variable (μ : Type) [Fintype μ] [LinearOrder μ] (r : ℕ) (hr : Fintype.card μ = r)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V) (j : ℤ)
local notation "Old" => ActualTorusReducedRestriction.OldBase R ι κ τ B v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R ι κ τ B)
local notation "F" => AffineRelativeThom.theory R μ G
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))

def oldEquiv :
    (L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R Old F))⟦(1 : ℤ)⟧)) ⟶ Coef) ≃+
      (AffineSheafContraction.sheafAtOne R Old site N (j-r)).ker := by
  letI := ActualOldFiberSmooth.old_smooth R ι κ τ B v inc hB hf hs
  exact AffineSheafContraction.contractionEquiv J L G R Old μ r hr site M N V hV j

def newEquiv :
    (L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R New F))⟦(1 : ℤ)⟧)) ⟶ Coef) ≃+
      (AffineSheafContraction.sheafAtOne R New site N (j-r)).ker := by
  letI := (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ inc B hB hf hs v).1
  exact AffineSheafContraction.contractionEquiv J L G R New μ r hr site M N V hV j

omit [J.Additive] in
theorem equiv_naturality
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R Old F))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    newEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j
      ((DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫ a) =
    ActualSheafContractionRestriction.restriction site R ι κ τ B v N (j-r)
      (oldEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j a) := by
  letI := ActualOldFiberSmooth.old_smooth R ι κ τ B v inc hB hf hs
  letI := (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ inc B hB hf hs v).1
  have h := ActualLocalizedReducedSections.equiv_naturality R F L (1 : ℤ) Coef ι κ τ B v a
  change AffineSheafContraction.kernelEvaluation J L G R New μ r hr site M N V hV j
      (ActualLocalizedReducedSections.equiv R New F L (1 : ℤ) Coef
        ((DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫ a)) =
    ActualSheafContractionRestriction.restriction site R ι κ τ B v N (j-r)
      (AffineSheafContraction.kernelEvaluation J L G R Old μ r hr site M N V hV j
        (ActualLocalizedReducedSections.equiv R Old F L (1 : ℤ) Coef a))
  rw [h]
  apply Subtype.ext
  exact AffineShiftedThomNaturality.shifted_evaluate_naturality J L G R
    (LaurentBasepoint.Laurent Old) (LaurentBasepoint.Laurent New) μ r hr
    (ActualTorusFace.torusFace R ι κ τ B v) site M N V hV
    (ActualOldFiberSmooth.laurent_smooth R Old) (ActualOldFiberSmooth.laurent_smooth R New) j
    (ActualLocalizedReducedSections.equiv R Old F L (1 : ℤ) Coef a).val

#print axioms oldEquiv
#print axioms newEquiv
#print axioms equiv_naturality
end Verification.ActualContractionSectionNaturality
