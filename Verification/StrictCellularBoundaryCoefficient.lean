/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularBoundary
import Verification.SingleCellConeIndex

/-!
# Strict Cellular Boundary Coefficient

Exact sign of the strict chain coefficient representing the original
positive cone boundary. The minus is proved from the actual quotient
projection, not imposed by a chosen cellular differential.
-/
noncomputable section
namespace Verification.StrictCellularBoundaryCoefficient
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

def sourceIso (p : ℕ) :
    ((single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧).X (-(p : ℤ)) ≅
      (cells (p+1)).term :=
  SingleCellConeIndex.headAt (cells (p+1)).term (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) (by omega)

omit [L.Additive] in
theorem differential_head (p : ℕ) : StrictCellularTerms.d J L H F cells hzero p =
    (sourceIso J L F cells p).inv ≫
      (attachment J L H F cells (p+1) (tower J L H F cells hzero (p+1))).attaching.f (-(p : ℤ)) ≫
        (StrictCellularTerms.termIso J L H F cells hzero (p+1) p (by omega)).hom := by
  let M := tower J L H F cells hzero (p+1)
  letI : M.model.complex.IsStrictlyGE (-((p+1 : ℕ) : ℤ)+1) := by
    simpa only [sub_eq_add_neg,add_comm] using M.lower
  have hh : StrictCellularTerms.termIso J L H F cells hzero (p+2) (p+1) (by omega) =
      StrictCellAttachment.newTermIso J M.model (cells (p+1))
        (StrictFiniteFiltration.step_distinguished L F (p+1)) (attachment J L H F cells (p+1) M) := by
    simp [StrictCellularTerms.termIso,M]
  unfold StrictCellularTerms.d StrictCellularTerms.differential
  rw [hh,StrictCellularTerms.termIso_succ_of_lt J L H F cells hzero (p+1) p (by omega)]
  simp only [Iso.trans_hom,Category.assoc]
  have hd := SingleCellConeIndex.new_differential_at (cells (p+1)).term (-((p+1 : ℕ) : ℤ))
    M.model.complex (attachment J L H F cells (p+1) M).attaching (-(p : ℤ)) (by omega)
  simpa only [Category.assoc] using congrArg
    (fun a => a ≫ (StrictCellularTerms.termIso J L H F cells hzero (p+1) p (by omega)).hom) hd

omit [L.Additive] in
theorem quotient_value (p : ℕ) :
    (StrictCellularBoundary.quotient J L H F cells hzero p).f (-(p : ℤ)) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(p : ℤ)) (cells p).term).hom =
        -(StrictCellularTerms.termIso J L H F cells hzero (p+1) p (by omega)).hom := by
  let M := tower J L H F cells hzero p
  letI : M.model.complex.IsStrictlyGE (-(p : ℤ)+1) := by
    simpa only [sub_eq_add_neg,add_comm] using M.lower
  have hh : StrictCellularTerms.termIso J L H F cells hzero (p+1) p (by omega) =
      StrictCellAttachment.newTermIso J M.model (cells p)
        (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M) := by
    simp [StrictCellularTerms.termIso,M]
  rw [hh]
  have h := StrictAttachmentProjection.quotient_new J M.model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)
  simpa only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,
    Preadditive.comp_neg,Category.comp_id] using congrArg
      (fun a => (StrictCellAttachment.newTermIso J M.model (cells p)
        (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)).hom ≫ a) h

omit [L.Additive] in
theorem coefficient (p : ℕ) : (sourceIso J L F cells p).inv ≫
    (StrictCellularBoundary.attachingBoundary J L H F cells hzero p).f (-(p : ℤ)) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(p : ℤ)) (cells p).term).hom =
        -StrictCellularTerms.d J L H F cells hzero p := by
  simp only [StrictCellularBoundary.attachingBoundary,HomologicalComplex.comp_f,Category.assoc]
  rw [quotient_value]
  simp only [Preadditive.comp_neg]
  rw [differential_head]

#print axioms sourceIso
#print axioms differential_head
#print axioms quotient_value
#print axioms coefficient
end Verification.StrictCellularBoundaryCoefficient
