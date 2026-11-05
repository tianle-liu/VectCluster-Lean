/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeProductFunctor
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Product Open Pullback

Products in the category of schemes over the base preserve the actual
open normal pair by a cartesian square. In particular its open part is the
preimage of the puncture, as an equality of actual scheme opens.
-/
noncomputable section
namespace Verification.ProductOpenPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {D : Type*} [Category D] [HasBinaryProducts D] {U N : D} (j : U ⟶ N) (Y : D)

theorem product_pullback : IsPullback (prod.fst : U ⨯ Y ⟶ U) (prod.map j (𝟙 Y)) j (prod.fst : N ⨯ Y ⟶ N) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk prod.fst (prod.map j (𝟙 Y)) (by simp))
  refine PullbackCone.IsLimit.mk _ (fun s => prod.lift s.fst (s.snd ≫ prod.snd)) ?_ ?_ ?_
  · intro s
    simp
  · intro s
    apply Limits.prod.hom_ext
    · simpa using s.condition
    · simp
  · intro s m hm₁ hm₂
    apply Limits.prod.hom_ext
    · simpa using hm₁
    · have h := congrArg (fun q => q ≫ prod.snd) hm₂
      simpa using h

variable {S : Scheme} {A B : Over S} (f : A ⟶ B) (Z : Over S)

theorem over_square : IsPullback (prod.fst : A ⨯ Z ⟶ A).left (prod.map f (𝟙 Z)).left f.left
    (prod.fst : B ⨯ Z ⟶ B).left := by
  letI : IsConnected WalkingCospan := IsConnected.of_induct (j₀ := WalkingCospan.one) (by
    intro p hp h j
    cases j with
    | none => exact hp
    | some j => exact (h (WidePullbackShape.Hom.term j)).mpr hp)
  letI := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit (cospan f (prod.fst : B ⨯ Z ⟶ B)) (Over.forget S)
  exact (product_pullback f Z).map (Over.forget S)

instance product_open [IsOpenImmersion f.left] : IsOpenImmersion (prod.map f (𝟙 Z)).left :=
  MorphismProperty.of_isPullback (over_square f Z) inferInstance

theorem open_range [IsOpenImmersion f.left] : (prod.map f (𝟙 Z)).left.opensRange =
    (prod.fst : B ⨯ Z ⟶ B).left ⁻¹ᵁ f.left.opensRange := by
  simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (over_square f Z) ⊤

#print axioms product_pullback
#print axioms over_square
#print axioms product_open
#print axioms open_range
end Verification.ProductOpenPullback
