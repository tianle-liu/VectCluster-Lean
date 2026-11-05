/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldExchangeMatrix
import Verification.OriginalKZero
import Verification.StableOrientations
import Verification.ProjectiveIndecomposable

/-!
# Sevenfold Nonfree Indecomposable

Every nonfree actual rank-two bundle on the sevenfold is
indecomposable. The line-bundle hypothesis follows from the internally
computed original K-zero rank map.
-/
noncomputable section
namespace Verification.SevenfoldNonfreeIndecomposable
open CategoryTheory AlgebraicGeometry Verification.ActualProjectiveSplitting
variable (R : Type) [Field R]
variable (Det : DeterminantStandardInput.Standard (SevenfoldExchangeMatrix.Ring R))
variable {KG : Scheme → Type*} [∀ X,AddCommGroup (KG X)]
variable (GT : SchemeGZeroInput.Theory KG) (GK : SchemeGZeroInput.Koszul GT)
variable (GTorus : SchemeGZeroInput.SplitAffineTorus GT) (GLocalization : SchemeGZeroInput.Localization GT)
variable (Cartan : SmoothCartanInput.Standard)

include Det GT GK GTorus GLocalization Cartan in
theorem line_free (Z : Bundle (SevenfoldExchangeMatrix.Ring R)) (hr : HasRank Z 1) : Trivial Z := by
  letI := SevenfoldExchangeMatrix.domain R
  exact StableOrientations.line_free_of_kzero Det (FractionRing (SevenfoldExchangeMatrix.Ring R))
    (OriginalKZero.rank_bijective R (Fin 2) 5 SevenfoldExchangeMatrix.matrix
      SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support
      (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1)
      (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2)
      GT GK GTorus GLocalization Cartan (FractionRing (SevenfoldExchangeMatrix.Ring R))).1 Z hr

include Det GT GK GTorus GLocalization Cartan in
theorem indecomposable (Z : Bundle (SevenfoldExchangeMatrix.Ring R)) (hr : HasRank Z 2)
    (hn : ¬ Trivial Z) :
    letI := SevenfoldExchangeMatrix.domain R
    ProjectiveIndecomposable.Indecomposable Z := by
  letI := SevenfoldExchangeMatrix.domain R
  exact ProjectiveIndecomposable.of_nonfree_rank_two
    (line_free R Det GT GK GTorus GLocalization Cartan) Z hr hn

include Det GT GK GTorus GLocalization Cartan in
theorem representative :
    letI := SevenfoldExchangeMatrix.domain R
    ∀ x : {x : RankedProjectiveClasses.Classes (SevenfoldExchangeMatrix.Ring R) 2 //
      x ≠ RankedProjectiveClasses.trivial (SevenfoldExchangeMatrix.Ring R) 2},
    ∃ (Z : Bundle (SevenfoldExchangeMatrix.Ring R)) (hr : HasRank Z 2),
      RankedProjectiveClasses.classOf (SevenfoldExchangeMatrix.Ring R) Z hr=x.val ∧
      ¬ Trivial Z ∧ ProjectiveIndecomposable.Indecomposable Z := by
  letI := SevenfoldExchangeMatrix.domain R
  intro x
  let Z := x.val.out
  have hZ : RankedProjectiveClasses.classOf (SevenfoldExchangeMatrix.Ring R) Z.val Z.property=x.val :=
    Quotient.out_eq _
  have hn : ¬ Trivial Z.val := by
    intro hf
    exact x.property (hZ.symm.trans ((RankedProjectiveClasses.eq_trivial
      (SevenfoldExchangeMatrix.Ring R) Z.val Z.property).mpr hf))
  exact ⟨Z.val,Z.property,hZ,hn,indecomposable R Det GT GK GTorus GLocalization Cartan Z.val Z.property hn⟩

#print axioms line_free
#print axioms indecomposable
#print axioms representative
end Verification.SevenfoldNonfreeIndecomposable
