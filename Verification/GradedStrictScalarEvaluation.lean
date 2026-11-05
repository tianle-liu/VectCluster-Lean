/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittStrictScalars
import Verification.OrderedThomEvaluation
import Verification.StrictCellTests

/-!
# Graded Strict Scalar Evaluation

Ordinary graded strict-sheaf scalar multiplication commutes with the
actual numbered Thom evaluation and its cardinal transport.
-/
noncomputable section
namespace Verification.GradedStrictScalarEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.GradedMilnorWittDegreeSpaces Verification.GradedSectionTotal
open Verification.SheafGradedLaurentResidue
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
local notation "B" => CommRingCat.of R

variable (V : LocalizedThomSections.Standard J L G R site M N)

variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)
variable (S : Type) [CommRing S] [Algebra R S] (ι : Type) [Fintype ι]
variable (r : ℕ) (hr : Fintype.card ι=r) (hs : Algebra.Smooth R S)
include H

omit [J.Additive] [L.Additive] in
theorem degree (k l : ℤ) (c : space site N W B (l-k))
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r:ℤ)) (M k)))) :
    includeDegree (W.grading (CommRingCat.of S)) (l-r)
      (OrderedThomEvaluation.degreeEvaluation J L G R site M N V S r ι hr hs l
        (a ≫ J.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor A (-(r:ℤ))).map (H.scalar k l c)))))=
    includeDegree (W.grading (CommRingCat.of S)) (k-r)
      (OrderedThomEvaluation.degreeEvaluation J L G R site M N V S r ι hr hs k a)*
      GradedMilnorWittSheaf.pullback site N W (S := B) (T := CommRingCat.of S) (algebraMap R S) c.val := by
  cases hr
  exact H.evaluate S ι hs k l c a

omit [J.Additive] [L.Additive] in
theorem ordered [LinearOrder ι] (k l : ℤ) (c : space site N W B (l-k))
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r:ℤ)) (M k)))) :
    includeDegree (W.grading (CommRingCat.of S)) (l-r)
      (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs l
        (a ≫ J.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor A (-(r:ℤ))).map (H.scalar k l c)))))=
    includeDegree (W.grading (CommRingCat.of S)) (k-r)
      (OrderedThomSections.evaluate ι r hr S J L G R site M N V hs k a)*
      GradedMilnorWittSheaf.pullback site N W (S := B) (T := CommRingCat.of S) (algebraMap R S) c.val := by
  simp only [OrderedThomEvaluation.evaluate_apply,OrderedThomEvaluation.finEvaluate,
    OrderedThomEvaluation.rewrite_eq_degree]
  rw [← Category.assoc]
  exact degree J L G R site M N W P V H S (Fin r) r (Fintype.card_fin r) hs k l c _

#print axioms degree
#print axioms ordered
end Verification.GradedStrictScalarEvaluation
