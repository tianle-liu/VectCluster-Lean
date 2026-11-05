/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularTerms
import Verification.StrictAttachmentProjection

/-!
# Strict Cellular Boundary

The actual strict attaching map lifts the positive boundary of the
original filtered raw complexes after localization. All source, quotient
and shift comparison squares are internally proved.
-/
noncomputable section
namespace Verification.StrictCellularBoundary
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel Verification.StrictCellularTower
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A)) (F : ℕ ⥤ CochainComplex C ℤ)

variable (cells : ∀ p : ℕ,Cell J (-(p : ℤ))
  (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))

variable (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))

def quotient (p : ℕ) : (tower J L H F cells hzero (p+1)).model.complex ⟶
    single (-(p : ℤ)) (cells p).term :=
  StrictAttachmentProjection.quotient J (S := StrictFiniteFiltration.stepTriangle L F p) (tower J L H F cells hzero p).model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p)
    (attachment J L H F cells p (tower J L H F cells hzero p))

def attachingBoundary (p : ℕ) :
    (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧ ⟶ single (-(p : ℤ)) (cells p).term :=
  (attachment J L H F cells (p+1) (tower J L H F cells hzero (p+1))).attaching ≫
    quotient J L H F cells hzero p

def ambientBoundary (p : ℕ) :
    (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F (p+1))))⟦(-1 : ℤ)⟧ ⟶
      L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)) :=
  (StrictFiniteFiltration.stepTriangle L F (p+1)).invRotate.mor₁ ≫
    (StrictFiniteFiltration.stepTriangle L F p).mor₂

omit [L.Additive] in
theorem boundary_square (p : ℕ) : ambientBoundary L F p ≫ (cells p).comparison =
    StrictTriangleHom.shifted (DerivedCategory.Q ⋙ J) (cells (p+1)).comparison (-1) ≫
      J.map (DerivedCategory.Q.map (attachingBoundary J L H F cells hzero p)) := by
  have hq := StrictAttachmentProjection.quotient_square J (S := StrictFiniteFiltration.stepTriangle L F p)
    (tower J L H F cells hzero p).model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p)
    (attachment J L H F cells p (tower J L H F cells hzero p))
  have hs := ActualStrictCone.source_square J (S := StrictFiniteFiltration.stepTriangle L F (p+1))
    (tower J L H F cells hzero (p+1)).model.complex
    (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)
    (tower J L H F cells hzero (p+1)).model.comparison
    (cells (p+1)).comparison (cells (p+1)).universal
    (attachment J L H F cells (p+1) (tower J L H F cells hzero (p+1))).attaching
    (attachment J L H F cells (p+1) (tower J L H F cells hzero (p+1))).represents
  dsimp only [ambientBoundary]
  rw [Category.assoc,hq]
  change _ ≫ ((tower J L H F cells hzero (p+1)).model.comparison ≫ _) = _
  rw [← Category.assoc,hs,StrictAttachmentProjection.sourceComparison_eq]
  simp only [attachingBoundary,quotient,Functor.map_comp,Category.assoc]

def positiveBoundary (p : ℕ) :
    L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F (p+1))) ⟶
      (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p)))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q ⋙ L).map (FilteredConeComplex.boundary F p) ≫
    ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app (FilteredConeComplex.relative F p)

omit [HasZeroObject D] [∀ (n : ℤ),(shiftFunctor D n).Additive]
  [Pretriangulated D] [L.IsTriangulated] in
theorem positiveBoundary_eq (p : ℕ) : positiveBoundary L F p =
    -(StrictFiniteFiltration.stepTriangle L F (p+1)).mor₃ ≫
      (StrictFiniteFiltration.stepTriangle L F p).mor₂⟦(1 : ℤ)⟧' := by
  dsimp only [positiveBoundary,FilteredConeComplex.boundary,TransverseConeBoundary.boundary]
  rw [Functor.map_comp,Category.assoc,Functor.commShiftIso_hom_naturality]
  simp only [Functor.map_neg,StrictFiniteFiltration.stepTriangle,Functor.mapTriangle_obj,
    Triangle.mk_mor₂,Triangle.mk_mor₃,Functor.comp_map,Functor.comp_obj,
    Functor.map_comp,Functor.commShiftIso_comp_hom_app,Category.assoc,Preadditive.neg_comp]
  rfl

omit [HasZeroObject D] [Pretriangulated D] [L.IsTriangulated] in
theorem ambientBoundary_positive (p : ℕ) : ambientBoundary L F p =
    (positiveBoundary L F p)⟦(-1 : ℤ)⟧' ≫
      (shiftShiftNeg (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))) (1 : ℤ)).hom := by
  rw [positiveBoundary_eq]
  dsimp only [ambientBoundary,Triangle.invRotate_mor₁,shiftShiftNeg]
  simp only [Functor.map_comp,Functor.map_neg,Preadditive.neg_comp,Category.assoc]
  congr 1
  have hn := (shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).hom.naturality
    (StrictFiniteFiltration.stepTriangle L F p).mor₂
  simpa only [shiftEquiv,shiftEquiv',Iso.symm_hom,Iso.app_hom,Functor.comp_map,Functor.id_map] using
    congrArg (fun a => (shiftFunctor D (-1 : ℤ)).map
      (StrictFiniteFiltration.stepTriangle L F (p+1)).mor₃ ≫ a) hn.symm

#print axioms quotient
#print axioms attachingBoundary
#print axioms ambientBoundary
#print axioms boundary_square
#print axioms positiveBoundary
#print axioms positiveBoundary_eq
#print axioms ambientBoundary_positive
end Verification.StrictCellularBoundary
