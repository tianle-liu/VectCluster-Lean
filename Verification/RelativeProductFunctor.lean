/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityInput
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Comma

/-!
# Relative Product Functor

Actual relative-product chains. Given N°→N, the value at Y is the
literal cone of G(N°×Y)→G(N×Y), with genuine product maps. For the geometric
Thom application products are in schemes over Spec R, so they are the
correct fiber products over the base, not absolute products over Spec Z.
-/
noncomputable section
namespace Verification.RelativeProductFunctor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]

def coneFunctor : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ where
  obj a := mappingCone a.hom
  map f := mappingCone.map _ _ f.left f.right f.w.symm
  map_id a := mappingCone.map_id a.hom
  map_comp _ _ := mappingCone.map_comp _ _ _ _ _ _ _ _ _

variable {D : Type*} [Category D] [HasBinaryProducts D]
variable (G : D ⥤ CochainComplex C ℤ) {N₀ N : D} (j : N₀ ⟶ N)

def productArrow : D ⥤ Arrow (CochainComplex C ℤ) where
  obj Y := Arrow.mk (G.map (prod.map j (𝟙 Y)))
  map f := Arrow.homMk (G.map (prod.map (𝟙 N₀) f)) (G.map (prod.map (𝟙 N) f)) (by
    dsimp only [Arrow.mk_hom]
    rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
    congr 1
    simp only [Limits.prod.map_map,Category.id_comp,Category.comp_id])
  map_id Y := by ext <;> simp
  map_comp f g := by ext <;> simp [Limits.prod.map_map,← CategoryTheory.Functor.map_comp]

def relative : D ⥤ CochainComplex C ℤ := productArrow G j ⋙ coneFunctor

theorem relative_obj (Y : D) : (relative G j).obj Y = mappingCone (G.map (prod.map j (𝟙 Y))) := rfl

section Actual
variable (R ι : Type) [CommRing R]

def normal : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))

def punctured : Over (Spec (CommRingCat.of R)) :=
  Over.mk ((CoordinatePurityInput.puncture (MvPolynomial ι R) ι MvPolynomial.X).ι ≫
    (normal R ι).hom)

def punctureMap : punctured R ι ⟶ normal R ι :=
  Over.homMk (CoordinatePurityInput.puncture (MvPolynomial ι R) ι MvPolynomial.X).ι (by rfl)

variable (F : Scheme ⥤ CochainComplex C ℤ)

def thom : Over (Spec (CommRingCat.of R)) ⥤ CochainComplex C ℤ :=
  relative (Over.forget _ ⋙ F) (punctureMap R ι)

theorem thom_obj (Y : Over (Spec (CommRingCat.of R))) : (thom R ι F).obj Y =
    mappingCone (F.map ((Over.forget _).map (prod.map (punctureMap R ι) (𝟙 Y)))) := rfl
end Actual

#print axioms coneFunctor
#print axioms productArrow
#print axioms relative
#print axioms relative_obj
#print axioms normal
#print axioms punctured
#print axioms punctureMap
#print axioms thom
#print axioms thom_obj
end Verification.RelativeProductFunctor
