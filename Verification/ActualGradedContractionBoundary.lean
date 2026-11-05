/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualContractionSectionNaturality
import Verification.ActualStandardLineContraction
import Verification.ActualLaurentSheafBaseChange
import Verification.SheafContractionNaturality

/-!
# Actual Graded Contraction Boundary

The actual transverse boundary on graded coefficient sections is
contraction at u=1 followed by the actual character-fiber pullback.
Smoothness, kernel preservation, and specialization of the standard line
are proved internally. Only ordinary uniform contraction and Thom
suspension representability supply the grading normalization.
-/
noncomputable section
namespace Verification.ActualGradedContractionBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ m : ℤ, (CategoryTheory.shiftFunctor D m).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
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
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (P : LocalizedPrincipalPurity.Standard L R
  (AffineRelativeThom.theory R μ G)
  (AffineRelativeThom.theory R (Option μ) G ⋙ DerivedCategory.Q ⋙ L))
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hK : SheafContractionNaturality.Standard R site N K)
variable (W : StandardThomContractionNormalization.Standard J L G R site M N V hV H μ r hr P K)
variable (j : ℤ)
set_option quotPrecheck false
local notation "Old" => ActualTorusReducedRestriction.OldBase R ι κ τ B v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R ι κ τ B)
local notation "F" => AffineRelativeThom.theory R μ G
local notation "T" => AffineRelativeThom.theory R (Option μ) G ⋙ DerivedCategory.Q ⋙ L
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((r+1 : ℕ) : ℤ)) (M j)))
local notation "hsNew" => (ActualTransversePairSmooth.pair_smooth_AS R ι κ τ inc B hB hf hs v).1
local notation "hsOld" => ActualOldFiberSmooth.old_smooth R ι κ τ B v inc hB hf hs
local instance optionOrder : LinearOrder (Option μ) := inferInstanceAs (LinearOrder (WithBot μ))

def lineIso : (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R) New)) ≅
    L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R New F))⟦(1 : ℤ)⟧)) := by
  letI : IsIso (L.map (DerivedCategory.Q.map (ActualTransverseBasepoint.lineProjection R ι κ τ B F))) :=
    LocalizedAffineThomInvariance.polynomial_projection L R G H New μ hsNew
  exact LocalizedTorusContraction.thomContractionIso R ι κ τ inc B hB v hf hs L F T P

include W in
omit [J.Additive] in
theorem line_evaluation
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R New F))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    AffineShiftedThomSections.evaluate J L G R New (Option μ) (r+1)
      (by simp only [Fintype.card_option,hr]) site M N V hsNew j
      ((lineIso L G R ι κ τ inc B hB v hf hs μ H P).hom ≫ a) =
    StandardThomContractionNormalization.lower R site N K New hsNew r j
      (ActualContractionSectionNaturality.newEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j a) := by
  exact W.standard_line New hsNew j a

include hK in
omit [J.Additive] [HasZeroObject D] [Pretriangulated D] [L.IsTriangulated] in
theorem graded_restriction
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R Old F))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    StandardThomContractionNormalization.lower R site N K New hsNew r j
      (ActualContractionSectionNaturality.newEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j
        ((DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫ a)) =
    ActualSheafContractionRestriction.pullback site (N (j-(r+1 : ℕ)))
      (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v).toRingHom
      (StandardThomContractionNormalization.lower R site N K Old hsOld r j
        (ActualContractionSectionNaturality.oldEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j a)) := by
  rw [ActualContractionSectionNaturality.equiv_naturality, ActualLaurentSheafBaseChange.kernelMap_eq]
  exact SheafContractionNaturality.lower_naturality R site N K Old New hsOld hsNew
    (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v) hK r j _

include W hK in
omit [J.Additive] in
theorem boundary_evaluation
    (a : L.obj (DerivedCategory.Q.obj ((kernel (LaurentBasepoint.projection R Old F))⟦(1 : ℤ)⟧)) ⟶ Coef) :
    AffineShiftedThomSections.evaluate J L G R New (Option μ) (r+1)
      (by simp only [Fintype.card_option,hr]) site M N V hsNew j
      ((lineIso L G R ι κ τ inc B hB v hf hs μ H P).hom ≫
        (DerivedCategory.Q ⋙ L).map ((ActualTorusReducedRestriction.reducedRestriction R ι κ τ B v F)⟦(1 : ℤ)⟧') ≫ a) =
    ActualSheafContractionRestriction.pullback site (N (j-(r+1 : ℕ)))
      (ActualTorusReducedRestriction.fiberRestriction R ι κ τ B v).toRingHom
      (StandardThomContractionNormalization.lower R site N K Old hsOld r j
        (ActualContractionSectionNaturality.oldEquiv J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV j a)) := by
  rw [line_evaluation J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV H P K W j]
  exact graded_restriction J L G R ι κ τ inc B hB v hf hs μ r hr site M N V hV K hK j a

#print axioms optionOrder
#print axioms lineIso
#print axioms line_evaluation
#print axioms graded_restriction
#print axioms boundary_evaluation
end Verification.ActualGradedContractionBoundary
