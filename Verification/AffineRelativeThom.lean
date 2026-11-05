/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductConeNaturality
import Verification.GeometricCellularSource

/-!
# Affine Relative Thom

The affine restriction of the actual normal-product chains theory.
The source category is precisely the opposite category of R-algebras
used by the transverse-slice calculation, and all products are over R.
-/
noncomputable section
namespace Verification.AffineRelativeThom
open CategoryTheory AlgebraicGeometry Opposite
open Verification.RelativeProductNaturality Verification.RelativeProductAffine
variable (R ι : Type) [CommRing R]

def affineOverFunctor : (Under (CommRingCat.of R))ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  (Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙ Over.post Scheme.Spec

variable {C : Type*} [Category C] [Abelian C] [CategoryTheory.Limits.HasBinaryBiproducts C]
variable (G : Scheme ⥤ CochainComplex C ℤ)

def theory : (Under (CommRingCat.of R))ᵒᵖ ⥤ CochainComplex C ℤ :=
  affineOverFunctor R ⋙ RelativeProductFunctor.thom R ι G

variable (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem object_eq : (theory R ι G).obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) =
    (RelativeProductFunctor.thom R ι G).obj (affineOver R A) := rfl

theorem map_eq (f : A →ₐ[R] B) : (theory R ι G).map f.toUnder.op =
    (RelativeProductFunctor.thom R ι G).map (affineMap R A B f) := rfl

#print axioms affineOverFunctor
#print axioms theory
#print axioms object_eq
#print axioms map_eq
end Verification.AffineRelativeThom
