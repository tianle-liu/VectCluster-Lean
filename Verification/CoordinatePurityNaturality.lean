/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePairMap

/-!
# Coordinate Purity Naturality

The standard purity input is used only on ordinary open maps of actual
smooth framed coordinate pairs. The right-hand arrow is constructed from
the induced quotient ring map; a cellular or residue boundary is not part
of this external naturality input.
-/
noncomputable section
namespace Verification.CoordinatePurityNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R : Type) [CommRing R] (G : Scheme ⥤ CochainComplex C ℤ)

variable {A B ι : Type} [CommRing A] [CommRing B]
variable (x : ι → A) (y : ι → B) (f : A →+* B) (hf : ∀ i,f (x i) = y i)

def normalMap : normalThom B ι y G ⟶ normalThom A ι x G :=
  CoordinatePairMap.relativeMap MvPolynomial.X MvPolynomial.X
    (MvPolynomial.map (CoordinatePairMap.closedMap x y f hf))
    (fun i => MvPolynomial.map_X _ i) G

structure Standard (P : StandardPurity R G) : Prop where
  open_naturality : ∀ (A B ι : Type) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Fintype ι] (x : ι → A) (y : ι → B)
    (f : A →ₐ[R] B) (hf : ∀ i,f (x i) = y i)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (FA : Frame R A ι x) (FB : Frame R B ι y),
    CoordinatePairMap.relativeMap x y f.toRingHom hf G ≫ (P.comparison A ι x FA).hom =
      (P.comparison B ι y FB).hom ≫ normalMap G x y f.toRingHom hf

#print axioms normalMap
#print axioms Standard
end Verification.CoordinatePurityNaturality
