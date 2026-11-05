/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinatePurityNaturality

/-!
# Localized Coordinate Purity

Coordinate purity after the actual ambient localization L. The raw
Nisnevich chains need not satisfy homotopy purity in their ordinary
derived category. All objects and arrows are the images under L of the
literal scheme localization cones constructed earlier.
-/
noncomputable section
namespace Verification.LocalizedCoordinatePurity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D)
variable (R : Type) [CommRing R] (G : Scheme ⥤ CochainComplex C ℤ)

structure Standard where
  comparison : ∀ (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] (x : ι → A),
    Frame R A ι x → (L.obj (relative A ι x G) ≅ L.obj (normalThom A ι x G))

structure Naturality (P : Standard L R G) : Prop where
  open_naturality : ∀ (A B ι : Type) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Fintype ι] (x : ι → A) (y : ι → B)
    (f : A →ₐ[R] B) (hf : ∀ i,f (x i) = y i)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (FA : Frame R A ι x) (FB : Frame R B ι y),
    L.map (CoordinatePairMap.relativeMap x y f.toRingHom hf G) ≫ (P.comparison A ι x FA).hom =
      (P.comparison B ι y FB).hom ≫ L.map (CoordinatePurityNaturality.normalMap G x y f.toRingHom hf)

#print axioms Standard
#print axioms Naturality
end Verification.LocalizedCoordinatePurity
