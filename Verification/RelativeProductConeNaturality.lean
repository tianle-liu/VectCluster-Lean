/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductOpenNaturality

/-!
# Relative Product Cone Naturality

The actual affine normal-pair isomorphisms are an arrow isomorphism,
including their open maps. Applying the genuine mapping-cone functor gives
natural strict complex isomorphisms before passing to the derived category.
-/
noncomputable section
namespace Verification.RelativeProductConeNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.RelativeProductFunctor Verification.RelativeProductAffine
open Verification.RelativeProductPair Verification.RelativeProductNaturality
open Verification.RelativeProductOpenNaturality
variable (R A B ι : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def pairIso : (productArrow (Over.forget _ ⋙ G) (punctureMap R ι)).obj (affineOver R A) ≅
    Arrow.mk (CoordinatePurityInput.pairArrow (MvPolynomial ι A) ι MvPolynomial.X G) :=
  Arrow.isoMk (G.mapIso (openIso R A ι)) (G.mapIso (ambientIso R A ι)) (by
    change G.map (openIso R A ι).hom ≫ G.map (CoordinatePurityInput.puncture (MvPolynomial ι A) ι MvPolynomial.X).ι =
      G.map (openArrow R A ι) ≫ G.map (ambientIso R A ι).hom
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
    exact congrArg G.map (RelativeProductPair.pair_square R A ι).symm)

variable (f : A →ₐ[R] B)

def coordinateArrowMap :
    Arrow.mk (CoordinatePurityInput.pairArrow (MvPolynomial ι B) ι MvPolynomial.X G) ⟶
      Arrow.mk (CoordinatePurityInput.pairArrow (MvPolynomial ι A) ι MvPolynomial.X G) :=
  Arrow.homMk (G.map (coordinateOpenMap R A B ι f)) (G.map (polynomialMap R A B ι f))
    (CoordinatePairMap.pair_square MvPolynomial.X MvPolynomial.X
      (MvPolynomial.map f.toRingHom) (fun i : ι => MvPolynomial.map_X _ i) G).symm

omit [HasBinaryBiproducts C] in
theorem pair_naturality : (productArrow (Over.forget _ ⋙ G) (punctureMap R ι)).map (affineMap R A B f) ≫
    (pairIso R A ι G).hom = (pairIso R B ι G).hom ≫ coordinateArrowMap R A B ι G f := by
  apply Arrow.hom_ext
  · change G.map (prod.map (𝟙 (punctured R ι)) (affineMap R A B f)).left ≫ G.map (openIso R A ι).hom =
      G.map (openIso R B ι).hom ≫ G.map (coordinateOpenMap R A B ι f)
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
    exact congrArg G.map (open_naturality R A B ι f)
  · change G.map (prod.map (𝟙 (normal R ι)) (affineMap R A B f)).left ≫ G.map (ambientIso R A ι).hom =
      G.map (ambientIso R B ι).hom ≫ G.map (polynomialMap R A B ι f)
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
    exact congrArg G.map (ambient_naturality R A B ι f)

def complexIso : (thom R ι G).obj (affineOver R A) ≅
    mappingCone (CoordinatePurityInput.pairArrow (MvPolynomial ι A) ι MvPolynomial.X G) :=
  coneFunctor.mapIso (pairIso R A ι G)

theorem complex_naturality : (thom R ι G).map (affineMap R A B f) ≫ (complexIso R A ι G).hom =
    (complexIso R B ι G).hom ≫ coneFunctor.map (coordinateArrowMap R A B ι G f) := by
  have h := congrArg coneFunctor.map (pair_naturality R A B ι G f)
  simpa only [CategoryTheory.Functor.map_comp] using h

universe w
variable [HasDerivedCategory.{w} C]

def derivedIso : DerivedCategory.Q.obj ((thom R ι G).obj (affineOver R A)) ≅
    CoordinatePurityInput.relative (MvPolynomial ι A) ι MvPolynomial.X G :=
  DerivedCategory.Q.mapIso (complexIso R A ι G)

theorem derived_naturality : DerivedCategory.Q.map ((thom R ι G).map (affineMap R A B f)) ≫
    (derivedIso R A ι G).hom = (derivedIso R B ι G).hom ≫
      CoordinatePairMap.relativeMap MvPolynomial.X MvPolynomial.X
        (MvPolynomial.map f.toRingHom) (fun i : ι => MvPolynomial.map_X _ i) G := by
  have h := congrArg DerivedCategory.Q.map (complex_naturality R A B ι G f)
  simpa only [CategoryTheory.Functor.map_comp] using h

theorem derivedIso_hom : (derivedIso R A ι G).hom =
    (RelativeProductPair.relativeIso R A ι G).hom := rfl

theorem derived_boundary : (derivedIso R A ι G).hom ≫
    TransverseDerivedBoundary.boundary (CoordinatePurityInput.pairArrow (MvPolynomial ι A) ι MvPolynomial.X G) =
      TransverseDerivedBoundary.boundary (G.map (openArrow R A ι)) ≫
        DerivedCategory.Q.map ((G.map (openIso R A ι).hom)⟦(1 : ℤ)⟧') := by
  rw [derivedIso_hom]
  exact RelativeProductPair.relativeIso_boundary R A ι G

#print axioms pairIso
#print axioms coordinateArrowMap
#print axioms pair_naturality
#print axioms complexIso
#print axioms complex_naturality
#print axioms derivedIso
#print axioms derived_naturality
#print axioms derivedIso_hom
#print axioms derived_boundary
end Verification.RelativeProductConeNaturality
