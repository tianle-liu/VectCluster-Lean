/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductAffine
import Verification.ProductOpenPullback
import Verification.ConeDerivedComparison

/-!
# Relative Product Pair

The actual normal relative-product functor on an affine coefficient
scheme is identified with its polynomial coordinate pair, including the
punctured open subscheme and the positive cone boundary.
-/
noncomputable section
namespace Verification.RelativeProductPair
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.RelativeProductAffine Verification.RelativeProductFunctor
open Verification.CoordinatePurityInput
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A]

theorem normal_preimage : normalProjection R A ι ⁻¹ᵁ
    puncture (MvPolynomial ι R) ι MvPolynomial.X =
      puncture (MvPolynomial ι A) ι MvPolynomial.X := by
  ext p
  change (PrimeSpectrum.comap (MvPolynomial.map (algebraMap R A)) p) ∈
      (⨆ i, PrimeSpectrum.basicOpen (MvPolynomial.X i) : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial ι R))) ↔
    p ∈ (⨆ i, PrimeSpectrum.basicOpen (MvPolynomial.X i) : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial ι A)))
  rw [TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_iSup]
  apply exists_congr
  intro i
  change MvPolynomial.map (algebraMap R A) (MvPolynomial.X i) ∉ p.asIdeal ↔ MvPolynomial.X i ∉ p.asIdeal
  rw [MvPolynomial.map_X]

def openArrow : ((punctured R ι) ⨯ affineOver R A).left ⟶ ((normal R ι) ⨯ affineOver R A).left :=
  (prod.map (punctureMap R ι) (𝟙 (affineOver R A))).left

instance openArrow_open : IsOpenImmersion (openArrow R A ι) := by
  unfold openArrow
  letI : IsOpenImmersion (punctureMap R ι).left := inferInstanceAs
    (IsOpenImmersion (puncture (MvPolynomial ι R) ι MvPolynomial.X).ι)
  exact ProductOpenPullback.product_open (punctureMap R ι) (affineOver R A)

theorem open_range : (openArrow R A ι ≫ (ambientIso R A ι).hom).opensRange =
    puncture (MvPolynomial ι A) ι MvPolynomial.X := by
  letI : IsOpenImmersion (punctureMap R ι).left := inferInstanceAs
    (IsOpenImmersion (puncture (MvPolynomial ι R) ι MvPolynomial.X).ι)
  rw [Scheme.Hom.opensRange_comp]
  have h := ProductOpenPullback.open_range (punctureMap R ι) (affineOver R A)
  change (openArrow R A ι).opensRange =
    (prod.fst : normal R ι ⨯ affineOver R A ⟶ normal R ι).left ⁻¹ᵁ
      (puncture (MvPolynomial ι R) ι MvPolynomial.X).ι.opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  rw [h]
  have hp : (prod.fst : normal R ι ⨯ affineOver R A ⟶ normal R ι).left =
      (ambientIso R A ι).hom ≫ normalProjection R A ι := by
    rw [← ambientIso_inv_fst, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hp, Scheme.preimage_comp, normal_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Hom.opensRange_of_isIso, top_inf_eq]

def openIso : ((punctured R ι) ⨯ affineOver R A).left ≅
    (puncture (MvPolynomial ι A) ι MvPolynomial.X).toScheme :=
  IsOpenImmersion.isoOfRangeEq (openArrow R A ι ≫ (ambientIso R A ι).hom)
    (puncture (MvPolynomial ι A) ι MvPolynomial.X).ι (by
      have h : (openArrow R A ι ≫ (ambientIso R A ι).hom).opensRange =
          (puncture (MvPolynomial ι A) ι MvPolynomial.X).ι.opensRange := by
        rw [open_range, Scheme.Opens.opensRange_ι]
      exact congrArg SetLike.coe h)

theorem pair_square : openArrow R A ι ≫ (ambientIso R A ι).hom =
    (openIso R A ι).hom ≫ (puncture (MvPolynomial ι A) ι MvPolynomial.X).ι :=
  (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm

universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def relativeIso : DerivedCategory.Q.obj ((thom R ι G).obj (affineOver R A)) ≅
    CoordinatePurityInput.relative (MvPolynomial ι A) ι MvPolynomial.X G :=
  ConeDerivedComparison.coneIso (G.map (openArrow R A ι))
    (pairArrow (MvPolynomial ι A) ι MvPolynomial.X G)
    (G.map (openIso R A ι).hom) (G.map (ambientIso R A ι).hom) (by
      simp only [pairArrow, ← CategoryTheory.Functor.map_comp]
      exact congrArg G.map (pair_square R A ι))

theorem relativeIso_boundary : (relativeIso R A ι G).hom ≫
    TransverseDerivedBoundary.boundary (pairArrow (MvPolynomial ι A) ι MvPolynomial.X G) =
      TransverseDerivedBoundary.boundary (G.map (openArrow R A ι)) ≫
        DerivedCategory.Q.map ((G.map (openIso R A ι).hom)⟦(1 : ℤ)⟧') :=
  ConeDerivedComparison.coneIso_boundary _ _ _ _ _

#print axioms normal_preimage
#print axioms openArrow
#print axioms openArrow_open
#print axioms open_range
#print axioms openIso
#print axioms pair_square
#print axioms relativeIso
#print axioms relativeIso_boundary
end Verification.RelativeProductPair
