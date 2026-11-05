/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPositiveContraction
import Verification.PathPositiveWeightIndex
import Verification.GradedCoefficientRealization

/-!
# Path Graded Sheaf Model

The original path contraction formulas, with their actual K_j indices and
an independent constant Z object, realized in any suitable additive category.
Only the standard positive graded coefficient action remains an input. The
literal path matrices, weighted bases and all homotopies were proved above;
the geometric cellular comparison is a separate theorem.
-/

noncomputable section
namespace Verification.PathGradedSheafModel

open Classical CategoryTheory CategoryTheory.Limits
  Verification.GradedCoefficientRealization

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasZeroObject C] [HasBinaryBiproducts C]
variable (K : ℕ → C) (A : PathGradedCoefficientAction.Action (fun j=>K (j+1))) (Z : C)

def zSource (n : ℕ) : CochainComplex C ℤ := withConstant K A (PathPositiveContraction.zData n) Z
def ySource (a : ℕ) : CochainComplex C ℤ := withConstant K A (PathPositiveContraction.yData a) Z

/-- One summand K_j for each j=1,...,n+1. -/
def zSurvivorIso (n : ℕ) : survivorObject K (fun k : PathCokernel.Weight false (n+1)=>k.val.val) ≅
    ⨁ fun k : Fin (n+1)=>K (k.val+1) := by
  change (⨁ fun k : PathPositiveWeightIndex.ZIndex n=>K k.val.val.val) ≅ _
  exact (biproduct.mapIso (fun k=>eqToIso (congrArg K (PathPositiveWeightIndex.z_value n k).symm))) ≪≫
    biproduct.reindex (PathPositiveWeightIndex.zEquiv n) (fun k=>K (k.val+1))

/-- One summand K_(2j) for each j=1,...,a. -/
def ySurvivorIso (a : ℕ) : survivorObject K (fun k : PathCokernel.Weight true (2*a)=>k.val.val) ≅
    ⨁ fun k : Fin a=>K (2*(k.val+1)) := by
  change (⨁ fun k : PathPositiveWeightIndex.YIndex a=>K k.val.val.val) ≅ _
  exact (biproduct.mapIso (fun k=>eqToIso (congrArg K (PathPositiveWeightIndex.y_value a k).symm))) ≪≫
    biproduct.reindex (PathPositiveWeightIndex.yEquiv a) (fun k=>K (2*(k.val+1)))

/-- The precise all-length Z_n formula, with its actual shifts. -/
def zEquivalence (n : ℕ) : HomotopyEquiv (zSource K A Z n)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
      (Z ⊞ ⨁ fun k : Fin (n+1)=>K (k.val+1))) :=
  (fullEquivalence K A (PathPositiveContraction.zData n) Z).trans
    (HomotopyEquiv.ofIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapIso
      (biprod.mapIso (Iso.refl Z) (zSurvivorIso K n))))

/-- The precise even Y_(2a) formula, including a=0. -/
def yEquivalence (a : ℕ) : HomotopyEquiv (ySource K A Z a)
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
      (Z ⊞ ⨁ fun k : Fin a=>K (2*(k.val+1)))) :=
  (fullEquivalence K A (PathPositiveContraction.yData a) Z).trans
    (HomotopyEquiv.ofIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapIso
      (biprod.mapIso (Iso.refl Z) (ySurvivorIso K a))))

#print axioms zSource
#print axioms ySource
#print axioms zSurvivorIso
#print axioms ySurvivorIso
#print axioms zEquivalence
#print axioms yEquivalence

end Verification.PathGradedSheafModel
