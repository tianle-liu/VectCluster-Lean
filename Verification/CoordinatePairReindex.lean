/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairEquiv

/-!
# Coordinate Pair Reindex

Reindexing the actual normal coordinates preserves the punctured
scheme and gives the literal induced isomorphism of localization cones.
-/
noncomputable section
namespace Verification.CoordinatePairReindex
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable (A ι κ : Type) [CommRing A] (x : ι → A) (e : κ ≃ ι)

theorem puncture_eq : puncture A κ (x ∘ e) = puncture A ι x := by
  ext p
  change p ∈ (⨆ i,PrimeSpectrum.basicOpen (x (e i)) : TopologicalSpace.Opens (PrimeSpectrum A)) ↔
    p ∈ (⨆ i,PrimeSpectrum.basicOpen (x i) : TopologicalSpace.Opens (PrimeSpectrum A))
  rw [TopologicalSpace.Opens.mem_iSup,TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨e i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.symm i,by simpa only [e.apply_symm_apply] using hi⟩

def openIso : (puncture A ι x).toScheme ≅ (puncture A κ (x ∘ e)).toScheme :=
  (Spec (CommRingCat.of A)).isoOfEq (puncture_eq A ι κ x e).symm

theorem open_square : (openIso A ι κ x e).hom ≫ (puncture A κ (x ∘ e)).ι = (puncture A ι x).ι :=
  Scheme.isoOfEq_hom_ι _ _

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem pair_square : pairArrow A ι x G ≫ 𝟙 _ = G.map (openIso A ι κ x e).hom ≫ pairArrow A κ (x ∘ e) G := by
  simp only [pairArrow,Category.comp_id,← CategoryTheory.Functor.map_comp,open_square]

def relativeIso : relative A ι x G ≅ relative A κ (x ∘ e) G :=
  ConeDerivedComparison.coneIso _ _ (G.map (openIso A ι κ x e).hom) (𝟙 _) (pair_square A ι κ x e G)

theorem positive_boundary : (relativeIso A ι κ x e G).hom ≫
    TransverseDerivedBoundary.boundary (pairArrow A κ (x ∘ e) G) =
      TransverseDerivedBoundary.boundary (pairArrow A ι x G) ≫
        DerivedCategory.Q.map ((G.map (openIso A ι κ x e).hom)⟦(1 : ℤ)⟧') :=
  ConeDerivedComparison.coneIso_boundary _ _ _ _ _

#print axioms puncture_eq
#print axioms openIso
#print axioms open_square
#print axioms pair_square
#print axioms relativeIso
#print axioms positive_boundary
end Verification.CoordinatePairReindex
