/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPositiveCellular

/-!
# Strict Positive Differential

Exact positive-boundary comparison for the literal strict cellular
differential, including its actual cochain degree maps. No differential
identification is an input: it follows from the retained cone triangles.
-/
noncomputable section
namespace Verification.StrictPositiveDifferential
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

def termIso (q : ℕ) :
    (StrictPositiveCellular.cochain J L H F cells hzero).X (-(q : ℤ)) ≅ (cells q).term :=
  (StrictPositiveCellular.complex J L H F cells hzero).extendXIso ComplexShape.embeddingDownNat rfl

theorem cochain_differential (p : ℕ) : (termIso J L H F cells hzero (p+1)).inv ≫
    (StrictPositiveCellular.cochain J L H F cells hzero).d (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) ≫
      (termIso J L H F cells hzero p).hom =
    (StrictPositiveCellular.complex J L H F cells hzero).d (p+1) p := by
  change _ ≫ ((StrictPositiveCellular.complex J L H F cells hzero).extend ComplexShape.embeddingDownNat).d _ _ ≫ _ = _
  rw [HomologicalComplex.extend_d_eq (StrictPositiveCellular.complex J L H F cells hzero)
    ComplexShape.embeddingDownNat (i := p+1) (j := p)
    (i' := -((p+1 : ℕ) : ℤ)) (j' := -(p : ℤ)) rfl rfl]
  simp only [termIso,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

def liftCoefficient (p : ℕ) (f : (cells (p+1)).term ⟶ (cells p).term) :
    (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧ ⟶
      single (-(p : ℤ)) (cells p).term :=
  HomologicalComplex.mkHomToSingle
    (K := (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term)⟦(-1 : ℤ)⟧)
    (j := -(p : ℤ)) (A := (cells p).term)
    ((StrictCellularBoundaryCoefficient.sourceIso J L F cells p).hom ≫ f) (by
      intro i _
      change ((-1 : ℤ).negOnePow •
        (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term).d (i + (-1)) (-(p : ℤ) + (-1))) ≫ _ = 0
      have hd : (single (-((p+1 : ℕ) : ℤ)) (cells (p+1)).term).d (i + (-1)) (-(p : ℤ) + (-1)) = 0 := rfl
      rw [hd,smul_zero,zero_comp])

theorem attaching_eq (p : ℕ) : StrictCellularBoundary.attachingBoundary J L H F cells hzero p =
    liftCoefficient J L F cells p ((StrictPositiveCellular.complex J L H F cells hzero).d (p+1) p) := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_epi (StrictCellularBoundaryCoefficient.sourceIso J L F cells p).inv).mp
  apply (cancel_mono (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(p : ℤ)) (cells p).term).hom).mp
  rw [Category.assoc,StrictCellularBoundaryCoefficient.coefficient]
  simp only [liftCoefficient,HomologicalComplex.mkHomToSingle_f,Category.assoc,
    Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
  change -StrictCellularTerms.d J L H F cells hzero p =
    -(StrictCellularTerms.complex J L H F cells hzero).d (p+1) p
  rw [StrictCellularTerms.complex_d]

variable [L.Additive]

theorem actual_boundary_square (p : ℕ) :
    (StrictCellularBoundary.positiveBoundary L F p)⟦(-1 : ℤ)⟧' ≫
      (shiftShiftNeg (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))) (1 : ℤ)).hom ≫
        (cells p).comparison =
    StrictTriangleHom.shifted (DerivedCategory.Q ⋙ J) (cells (p+1)).comparison (-1) ≫
      J.map (DerivedCategory.Q.map (liftCoefficient J L F cells p
        ((StrictPositiveCellular.complex J L H F cells hzero).d (p+1) p))) := by
  rw [← Category.assoc,← StrictCellularBoundary.ambientBoundary_positive,
    StrictCellularBoundary.boundary_square,attaching_eq]

#print axioms termIso
#print axioms cochain_differential
#print axioms liftCoefficient
#print axioms attaching_eq
#print axioms actual_boundary_square
end Verification.StrictPositiveDifferential
