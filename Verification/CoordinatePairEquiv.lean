/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Verification.ConeDerivedComparison

/-!
# Coordinate Pair Equiv

Ring equivalences preserving the actual normal coordinates induce
isomorphisms of the genuine punctured scheme pairs and their derived cones.
This supplies coordinate transport for the geometric Thom terms.
-/
noncomputable section
namespace Verification.CoordinatePairEquiv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinatePurityInput
variable {A B ι : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : ι → B) (e : A ≃+* B) (he : ∀ i,e (x i) = y i)

def schemeIso : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of B) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.symm.op

include he in
theorem puncture_preimage : (schemeIso e).hom ⁻¹ᵁ puncture B ι y = puncture A ι x := by
  ext p
  change (PrimeSpectrum.comap e.symm.toRingHom p) ∈
      (⨆ i,PrimeSpectrum.basicOpen (y i) : TopologicalSpace.Opens (PrimeSpectrum B)) ↔
    p ∈ (⨆ i,PrimeSpectrum.basicOpen (x i) : TopologicalSpace.Opens (PrimeSpectrum A))
  rw [TopologicalSpace.Opens.mem_iSup,TopologicalSpace.Opens.mem_iSup]
  apply exists_congr
  intro i
  change e.symm (y i) ∉ p.asIdeal ↔ x i ∉ p.asIdeal
  rw [← he i,e.symm_apply_apply]

def punctureIso : (puncture A ι x).toScheme ≅ (puncture B ι y).toScheme :=
  (Spec (CommRingCat.of A)).isoOfEq (puncture_preimage x y e he).symm ≪≫
    asIso (morphismRestrict (schemeIso e).hom (puncture B ι y))

theorem puncture_square : (puncture A ι x).ι ≫ (schemeIso e).hom =
    (punctureIso x y e he).hom ≫ (puncture B ι y).ι := by
  simp only [punctureIso,Iso.trans_hom,asIso_hom,Category.assoc,morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc]

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem pair_square : pairArrow A ι x G ≫ G.map (schemeIso e).hom =
    G.map (punctureIso x y e he).hom ≫ pairArrow B ι y G := by
  simp only [pairArrow,← CategoryTheory.Functor.map_comp]
  exact congrArg G.map (puncture_square x y e he)

def relativeIso : relative A ι x G ≅ relative B ι y G :=
  ConeDerivedComparison.coneIso _ _ (G.map (punctureIso x y e he).hom)
    (G.map (schemeIso e).hom) (pair_square x y e he G)

theorem relativeIso_boundary : (relativeIso x y e he G).hom ≫
    TransverseDerivedBoundary.boundary (pairArrow B ι y G) =
      TransverseDerivedBoundary.boundary (pairArrow A ι x G) ≫
        DerivedCategory.Q.map ((G.map (punctureIso x y e he).hom)⟦(1 : ℤ)⟧') :=
  ConeDerivedComparison.coneIso_boundary _ _ _ _ _

#print axioms schemeIso
#print axioms puncture_preimage
#print axioms punctureIso
#print axioms puncture_square
#print axioms pair_square
#print axioms relativeIso
#print axioms relativeIso_boundary
end Verification.CoordinatePairEquiv
