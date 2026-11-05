/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPositiveDifferential
import Verification.StrictCellTests
import Verification.StrictCoefficientCochains

/-!
# Strict Coefficient Boundary

Exact positive-boundary comparison for the literal strict cellular
differential, including its actual cochain degree maps. No differential
identification is an input: it follows from the retained cone triangles.
-/
noncomputable section
namespace Verification.StrictCoefficientBoundary
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel Verification.StrictCellularTower
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A)) (F : ℕ ⥤ CochainComplex C ℤ)

variable (cells : ∀ p : ℕ,Cell J (-(p : ℤ))
  (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))

variable (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))

def liftTest (p : ℕ) (M : A) (f : (cells (p+1)).term ⟶ M) :
    (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧ ⟶ single (-(p : ℤ)) M :=
  HomologicalComplex.mkHomToSingle
    (K := (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧)
    (j := -(p : ℤ)) (A := M)
    ((StrictCellularBoundaryCoefficient.sourceIso J L F cells p).hom ≫ f) (by
      intro i _
      change ((-1 : ℤ).negOnePow •
        (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term).d (i + (-1)) (-(p : ℤ) + (-1))) ≫ _ = 0
      have hd : (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term).d (i + (-1)) (-(p : ℤ) + (-1)) = 0 := rfl
      rw [hd,smul_zero,zero_comp])

omit [HasBinaryBiproducts A] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ,(shiftFunctor D n).Additive]
  [Pretriangulated D] [J.CommShift ℤ] [J.IsTriangulated] [L.CommShift ℤ] [L.IsTriangulated] in
theorem lift_comp (p : ℕ) (M : A) (d : (cells (p+1)).term ⟶ (cells p).term)
    (f : (cells p).term ⟶ M) :
    StrictPositiveDifferential.liftCoefficient J L F cells p d ≫
      (CochainComplex.singleFunctor A (-(p : ℤ))).map f = liftTest J L F cells p M (d ≫ f) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,StrictPositiveDifferential.liftCoefficient,liftTest,
    HomologicalComplex.mkHomToSingle_f,Category.assoc]
  dsimp only [CochainComplex.singleFunctor,CochainComplex.singleFunctors]
  rw [HomologicalComplex.single_map_f_self]
  simp

theorem cochain_coefficient (p : ℕ) (M : A)
    (f : (StrictCoefficientCochains.complex
      (StrictPositiveCellular.cochain J L H F cells hzero) M).X p) :
    (StrictPositiveDifferential.termIso J L H F cells hzero (p+1)).inv ≫
      ((StrictCoefficientCochains.complex
        (StrictPositiveCellular.cochain J L H F cells hzero) M).d p (p+1) f) =
    (StrictPositiveCellular.complex J L H F cells hzero).d (p+1) p ≫
      ((StrictPositiveDifferential.termIso J L H F cells hzero p).inv ≫ f) := by
  rw [StrictCoefficientCochains.differential_apply]
  rw [← StrictPositiveDifferential.cochain_differential J L H F cells hzero p]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

variable [L.Additive]

theorem test_boundary (p : ℕ) (M : A) (f : (cells p).term ⟶ M) :
    (StrictCellularBoundary.positiveBoundary L F p)⟦(-1 : ℤ)⟧' ≫
      (shiftShiftNeg (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))) (1 : ℤ)).hom ≫
        StrictCellTests.testAddEquiv J (cells p) M f =
    StrictTriangleHom.shifted (DerivedCategory.Q ⋙ J) (cells (p+1)).comparison (-1) ≫
      J.map (DerivedCategory.Q.map (liftTest J L F cells p M
        ((StrictPositiveCellular.complex J L H F cells hzero).d (p+1) p ≫ f))) := by
  change _ ≫ _ ≫ ((cells p).comparison ≫ J.map (DerivedCategory.Q.map
    ((CochainComplex.singleFunctor A (-(p : ℤ))).map f))) = _
  have hb := congrArg (fun t => t ≫ J.map (DerivedCategory.Q.map
    ((CochainComplex.singleFunctor A (-(p : ℤ))).map f)))
      (StrictPositiveDifferential.actual_boundary_square J L H F cells hzero p)
  simpa only [Category.assoc,← Functor.map_comp,lift_comp] using hb

theorem actual_coefficient_boundary (p : ℕ) (M : A)
    (f : (StrictCoefficientCochains.complex
      (StrictPositiveCellular.cochain J L H F cells hzero) M).X p) :
    (StrictCellularBoundary.positiveBoundary L F p)⟦(-1 : ℤ)⟧' ≫
      (shiftShiftNeg (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))) (1 : ℤ)).hom ≫
        StrictCellTests.testAddEquiv J (cells p) M
          ((StrictPositiveDifferential.termIso J L H F cells hzero p).inv ≫ f) =
    StrictTriangleHom.shifted (DerivedCategory.Q ⋙ J) (cells (p+1)).comparison (-1) ≫
      J.map (DerivedCategory.Q.map (liftTest J L F cells p M
        ((StrictPositiveDifferential.termIso J L H F cells hzero (p+1)).inv ≫
          (StrictCoefficientCochains.complex
            (StrictPositiveCellular.cochain J L H F cells hzero) M).d p (p+1) f))) := by
  rw [cochain_coefficient]
  exact test_boundary J L H F cells hzero p M _

#print axioms liftTest
#print axioms lift_comp
#print axioms cochain_coefficient
#print axioms test_boundary
#print axioms actual_coefficient_boundary
end Verification.StrictCoefficientBoundary
