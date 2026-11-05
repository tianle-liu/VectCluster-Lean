/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairEquiv

/-!
# Coordinate Pair Map

Functorial maps of literal coordinate pairs. The punctured schemes,
quotient maps and cone maps all come from the given ring homomorphism and
its proved coordinate identities; no purity comparison is assumed here.
-/
noncomputable section
namespace Verification.CoordinatePairMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable {A B ι : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : ι → B) (f : A →+* B) (hf : ∀ i, f (x i) = y i)

include hf in
theorem puncture_preimage : Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ puncture A ι x = puncture B ι y := by
  ext p
  change (PrimeSpectrum.comap f p) ∈ (⨆ i, PrimeSpectrum.basicOpen (x i) : TopologicalSpace.Opens (PrimeSpectrum A)) ↔
    p ∈ (⨆ i, PrimeSpectrum.basicOpen (y i) : TopologicalSpace.Opens (PrimeSpectrum B))
  rw [TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_iSup]
  apply exists_congr
  intro i
  change f (x i) ∉ p.asIdeal ↔ y i ∉ p.asIdeal
  rw [hf i]

def punctureMap : (puncture B ι y).toScheme ⟶ (puncture A ι x).toScheme :=
  ((Spec (CommRingCat.of B)).isoOfEq (puncture_preimage x y f hf).symm).hom ≫
    morphismRestrict (Spec.map (CommRingCat.ofHom f)) (puncture A ι x)

theorem puncture_square : (puncture B ι y).ι ≫ Spec.map (CommRingCat.ofHom f) =
    punctureMap x y f hf ≫ (puncture A ι x).ι := by
  simp only [punctureMap, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

include hf in
theorem ideal_map : Ideal.map f (ConormalFrame.ideal x) ≤ ConormalFrame.ideal y := by
  rw [ConormalFrame.ideal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
  rw [hf i]
  exact Ideal.subset_span ⟨i, rfl⟩

def closedMap : A ⧸ ConormalFrame.ideal x →+* B ⧸ ConormalFrame.ideal y :=
  Ideal.quotientMap _ f ((Ideal.map_le_iff_le_comap).mp (ideal_map x y f hf))

theorem closedMap_mk (a : A) : closedMap x y f hf (Ideal.Quotient.mk _ a) =
    Ideal.Quotient.mk _ (f a) := rfl

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem pair_square : pairArrow B ι y G ≫ G.map (Spec.map (CommRingCat.ofHom f)) =
    G.map (punctureMap x y f hf) ≫ pairArrow A ι x G := by
  simp only [pairArrow, ← CategoryTheory.Functor.map_comp]
  exact congrArg G.map (puncture_square x y f hf)

def relativeMap : relative B ι y G ⟶ relative A ι x G :=
  TransverseDerivedBoundary.coneMap _ _ (G.map (punctureMap x y f hf))
    (G.map (Spec.map (CommRingCat.ofHom f))) (pair_square x y f hf G)

theorem relativeMap_boundary : relativeMap x y f hf G ≫ TransverseDerivedBoundary.boundary (pairArrow A ι x G) =
    TransverseDerivedBoundary.boundary (pairArrow B ι y G) ≫
      DerivedCategory.Q.map ((G.map (punctureMap x y f hf))⟦(1 : ℤ)⟧') :=
  TransverseDerivedBoundary.boundary_naturality _ _ _ _ _

#print axioms puncture_preimage
#print axioms punctureMap
#print axioms puncture_square
#print axioms ideal_map
#print axioms closedMap
#print axioms closedMap_mk
#print axioms pair_square
#print axioms relativeMap
#print axioms relativeMap_boundary
end Verification.CoordinatePairMap
