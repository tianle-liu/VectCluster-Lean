/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientBoundary

/-!
# Strict Coefficient Boundary Evaluation

The ordinary Hom coefficient differential is conjugate to the actual
positive ambient boundary. The shifts are removed using the canonical
single-complex isomorphism, and not a new boundary-compatibility hypothesis.
-/
noncomputable section
namespace Verification.StrictCoefficientBoundaryEvaluation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A)) (F : ℕ ⥤ CochainComplex C ℤ)
variable (cells : ∀ p : ℕ, Cell J (-(p : ℤ))
  (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))
variable (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))

def singleShift (p : ℕ) (M : A) :
    (single (-((p+1 : ℕ) : ℤ)) M)⟦(-1 : ℤ)⟧ ≅ single (-(p : ℤ)) M :=
  ((CochainComplex.singleFunctors A).shiftIso (-1) (-(p : ℤ))
    (-((p+1 : ℕ) : ℤ)) (by omega)).app M

def coefficientShift (p : ℕ) (M : A) :
    (J.obj (DerivedCategory.Q.obj (single (-((p+1 : ℕ) : ℤ)) M)))⟦(-1 : ℤ)⟧ ≅
      J.obj (DerivedCategory.Q.obj (single (-(p : ℤ)) M)) :=
  ((DerivedCategory.Q ⋙ J).commShiftIso (-1)).symm.app _ ≪≫
    (DerivedCategory.Q ⋙ J).mapIso (singleShift p M)

def shiftTest (p : ℕ) (M : A) (X : D) :
    (X ⟶ J.obj (DerivedCategory.Q.obj (single (-((p+1 : ℕ) : ℤ)) M))) ≃+
      (X⟦(-1 : ℤ)⟧ ⟶ J.obj (DerivedCategory.Q.obj (single (-(p : ℤ)) M))) :=
  (AddEquiv.ofBijective (shiftFunctor D (-1 : ℤ)).mapAddHom
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D (-1 : ℤ))).homEquiv.bijective).trans
      { toFun := fun a => a ≫ (coefficientShift J p M).hom
        invFun := fun a => a ≫ (coefficientShift J p M).inv
        left_inv := by intro a; simp
        right_inv := by intro a; simp
        map_add' := by intro a b; simp only [Preadditive.add_comp] }

omit [HasBinaryBiproducts A] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [J.CommShift ℤ] [J.IsTriangulated] [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] in
theorem singleShift_lift (p : ℕ) (M : A) (f : (cells (p+1)).term ⟶ M) :
    ((CochainComplex.singleFunctor A (-((p+1 : ℕ) : ℤ))).map f)⟦(-1 : ℤ)⟧' ≫
      (singleShift p M).hom = StrictCoefficientBoundary.liftTest J L F cells p M f := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,StrictCoefficientBoundary.liftTest,
    HomologicalComplex.mkHomToSingle_f]
  dsimp only [singleShift,CochainComplex.singleFunctors]
  dsimp only [StrictCellularBoundaryCoefficient.sourceIso,SingleCellConeIndex.headAt]
  have hi : -(p : ℤ) + -1 = -((p+1 : ℕ) : ℤ) := by omega
  simp [single,CochainComplex.singleFunctor,CochainComplex.singleFunctors,
    HomologicalComplex.XIsoOfEq,HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq,HomologicalComplex.single_map_f_self]
  simp only [HomologicalComplex.single,dif_pos hi,Category.assoc,eqToHom_trans]

omit [HasBinaryBiproducts A] [HasZeroObject D] [Pretriangulated D]
  [J.IsTriangulated] [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] in
theorem shiftTest_evaluation (p : ℕ) (M : A) (f : (cells (p+1)).term ⟶ M) :
    shiftTest J p M _ (StrictCellTests.testAddEquiv J (cells (p+1)) M f) =
      StrictTriangleHom.shifted (DerivedCategory.Q ⋙ J) (cells (p+1)).comparison (-1) ≫
        J.map (DerivedCategory.Q.map (StrictCoefficientBoundary.liftTest J L F cells p M f)) := by
  change ((cells (p+1)).comparison ≫ (DerivedCategory.Q ⋙ J).map
    ((CochainComplex.singleFunctor A (-((p+1 : ℕ) : ℤ))).map f))⟦(-1 : ℤ)⟧' ≫
      (coefficientShift J p M).hom = _
  simp only [Functor.map_comp,coefficientShift,Iso.trans_hom,Iso.app_hom,
    Iso.symm_hom,Functor.mapIso_hom,Category.assoc]
  rw [(DerivedCategory.Q ⋙ J).commShiftIso_inv_naturality_assoc]
  simp only [StrictTriangleHom.shifted,Category.assoc,← Functor.map_comp]
  rw [singleShift_lift J L F cells]
  rfl

omit [HasBinaryBiproducts A] [HasZeroObject D] [Pretriangulated D]
  [J.Additive] [J.IsTriangulated] in
theorem shiftTest_precomp (p : ℕ) (M : A) {X Y : D} (f : X ⟶ Y)
    (a : Y ⟶ J.obj (DerivedCategory.Q.obj (single (-((p+1 : ℕ) : ℤ)) M))) :
    shiftTest J p M X (f ≫ a) = f⟦(-1 : ℤ)⟧' ≫ shiftTest J p M Y a := by
  change (f ≫ a)⟦(-1 : ℤ)⟧' ≫ (coefficientShift J p M).hom =
    f⟦(-1 : ℤ)⟧' ≫ a⟦(-1 : ℤ)⟧' ≫ (coefficientShift J p M).hom
  rw [Functor.map_comp,Category.assoc]

def termEvaluation (p : ℕ) (M : A) :
    (StrictCoefficientCochains.complex
      (StrictPositiveCellular.cochain J L H F cells hzero) M).X p ≃+
      (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)) ⟶
        J.obj (DerivedCategory.Q.obj (single (-(p : ℤ)) M))) :=
  (StrictCellTests.homOfIso
    (StrictPositiveDifferential.termIso J L H F cells hzero p) M).trans
      (StrictCellTests.testAddEquiv J (cells p) M)

def boundary (p : ℕ) (M : A) :
    (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)) ⟶
      J.obj (DerivedCategory.Q.obj (single (-(p : ℤ)) M))) →+
    (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F (p+1))) ⟶
      J.obj (DerivedCategory.Q.obj (single (-((p+1 : ℕ) : ℤ)) M))) :=
  (shiftTest J p M _).symm.toAddMonoidHom.comp
    { toFun := fun a => StrictCellularBoundary.ambientBoundary L F p ≫ a
      map_zero' := by simp
      map_add' := by intro a b; simp only [Preadditive.comp_add] }

theorem differential_conjugate (p : ℕ) (M : A)
    (a : (StrictCoefficientCochains.complex
      (StrictPositiveCellular.cochain J L H F cells hzero) M).X p) :
    termEvaluation J L H F cells hzero (p+1) M
        ((StrictCoefficientCochains.complex
          (StrictPositiveCellular.cochain J L H F cells hzero) M).d p (p+1) a) =
      boundary J L F p M (termEvaluation J L H F cells hzero p M a) := by
  apply (shiftTest J p M _).injective
  change shiftTest J p M _ (StrictCellTests.testAddEquiv J (cells (p+1)) M _) =
    shiftTest J p M _ ((shiftTest J p M _).symm _)
  rw [AddEquiv.apply_symm_apply,shiftTest_evaluation]
  simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [StrictCellularBoundary.ambientBoundary_positive]
  simpa only [termEvaluation,AddEquiv.trans_apply,StrictCellTests.homOfIso,
    EquivLike.coe_coe,Category.assoc] using
    (StrictCoefficientBoundary.actual_coefficient_boundary J L H F cells hzero p M a).symm

include H cells hzero in
theorem boundary_square (p : ℕ) (M : A)
    (a : L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)) ⟶
      J.obj (DerivedCategory.Q.obj (single (-(p : ℤ)) M))) :
    boundary J L F (p+1) M (boundary J L F p M a) = 0 := by
  obtain ⟨b,rfl⟩ := (termEvaluation J L H F cells hzero p M).surjective a
  rw [← differential_conjugate,← differential_conjugate]
  have hd := congrArg (fun t => t b) ((StrictCoefficientCochains.complex
    (StrictPositiveCellular.cochain J L H F cells hzero) M).d_comp_d p (p+1) (p+1+1))
  change (StrictCoefficientCochains.complex
    (StrictPositiveCellular.cochain J L H F cells hzero) M).d (p+1) (p+1+1)
      ((StrictCoefficientCochains.complex
        (StrictPositiveCellular.cochain J L H F cells hzero) M).d p (p+1) b) = 0 at hd
  rw [hd,map_zero]

#print axioms singleShift
#print axioms coefficientShift
#print axioms shiftTest
#print axioms singleShift_lift
#print axioms shiftTest_evaluation
#print axioms shiftTest_precomp
#print axioms termEvaluation
#print axioms boundary
#print axioms differential_conjugate
#print axioms boundary_square
end Verification.StrictCoefficientBoundaryEvaluation
