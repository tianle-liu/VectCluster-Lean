/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichInput
import Verification.StrictCoefficientComparison

/-!
# Strict Nisnevich Representability

Ordinary representability of Nisnevich cohomology for the chosen
strictly A¹-invariant heart in the ambient localized derived category.
This interface quantifies over every smooth affine algebra; it contains
no cellular model or exchange-specific comparison.
-/
noncomputable section
namespace Verification.StrictNisnevichRepresentability
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D)
variable (L : DerivedCategory C ⥤ D)
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (T : StrictNisnevichInput.Theory A) (k : Type) [Field k]

structure Standard where
  comparison : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (M : A) (q : ℕ), T.cohomology (Spec (CommRingCat.of R)) M q ≃+
      (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R)))) ⟶
        J.obj (StrictCoefficientComparison.target M q))

variable (H : Standard J L G T k)
variable (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R]

include H in
theorem ambient_zero (M : A) (q : ℕ)
    (hz : IsZero (T.cohomology (Spec (CommRingCat.of R)) M q)) :
    Subsingleton (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R)))) ⟶
      J.obj (StrictCoefficientComparison.target M q)) := by
  let e := H.comparison R M q
  have hzero (x : T.cohomology (Spec (CommRingCat.of R)) M q) : x = 0 := by
    exact congrArg (fun f : T.cohomology (Spec (CommRingCat.of R)) M q ⟶
      T.cohomology (Spec (CommRingCat.of R)) M q => f x) (hz.eq_of_src (𝟙 _) 0)
  refine ⟨fun f g => e.symm.injective ?_⟩
  exact (hzero (e.symm f)).trans (hzero (e.symm g)).symm

include H in
theorem cohomology_zero (M : A) (q : ℕ)
    [Subsingleton (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of R)))) ⟶
      J.obj (StrictCoefficientComparison.target M q))] :
    IsZero (T.cohomology (Spec (CommRingCat.of R)) M q) := by
  let e := H.comparison R M q
  letI : Subsingleton (T.cohomology (Spec (CommRingCat.of R)) M q) :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  exact AddCommGrp.isZero_of_subsingleton _

#print axioms Standard
#print axioms ambient_zero
#print axioms cohomology_zero
end Verification.StrictNisnevichRepresentability
