/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ReindexedCoordinateMap
import Verification.LocalizedCoordinatePurity

/-!
# Localized Indexed Purity

Standard ordinary purity naturality permits a bijection of the framed
normal parameters. Its two morphisms are the actual pair map and the
actual quotient/polynomial normal map; no boundary or cellular matrix is
part of this external input.
-/
noncomputable section
namespace Verification.LocalizedIndexedPurity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D) (R : Type) [CommRing R]
variable (G : Scheme ⥤ CochainComplex C ℤ) (P : LocalizedCoordinatePurity.Standard L R G)

structure Standard : Prop where
  open_naturality : ∀ (A B ι κ : Type) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Fintype ι] [Fintype κ]
    (x : ι → A) (y : κ → B) (e : κ ≃ ι)
    (f : A →ₐ[R] B) (hf : ∀ i,f (x (e i)) = y i)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (FA : Frame R A ι x) (FB : Frame R B κ y),
    L.map (ReindexedCoordinateMap.relativeMap x y e f.toRingHom hf G) ≫
        (P.comparison A ι x FA).hom =
      (P.comparison B κ y FB).hom ≫
        L.map (ReindexedCoordinateMap.normalMap x y e f.toRingHom hf G)

#print axioms Standard
end Verification.LocalizedIndexedPurity
