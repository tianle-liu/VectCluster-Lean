/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularRealization
import Verification.StrictCellularBoundaryCoefficient
import Verification.CellularSignConvention

/-!
# Strict Positive Cellular

The positive cellular boundary complex. It is actually chain-isomorphic
to the strict cone realization, and its literal coefficients are those
of the positive ambient boundary under the proved strict comparison.
-/
noncomputable section
namespace Verification.StrictPositiveCellular
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

def complex : ChainComplex A ℕ := CellularSignConvention.negative
  (StrictCellularTerms.complex J L H F cells hzero)

def cochain : CochainComplex A ℤ :=
  (complex J L H F cells hzero).extend ComplexShape.embeddingDownNat

def signIso : StrictCellularRealization.cochain J L H F cells hzero ≅
    cochain J L H F cells hzero :=
  (ComplexShape.embeddingDownNat.extendFunctor A).mapIso
    (CellularSignConvention.negativeIso (StrictCellularTerms.complex J L H F cells hzero))

theorem differential (p : ℕ) : (complex J L H F cells hzero).d (p+1) p =
    (StrictCellularBoundaryCoefficient.sourceIso J L F cells p).inv ≫
      (StrictCellularBoundary.attachingBoundary J L H F cells hzero p).f (-(p : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(p : ℤ)) (cells p).term).hom := by
  rw [StrictCellularBoundaryCoefficient.coefficient]
  change -(StrictCellularTerms.complex J L H F cells hzero).d (p+1) p = _
  rw [StrictCellularTerms.complex_d]

#print axioms complex
#print axioms cochain
#print axioms signIso
#print axioms differential
end Verification.StrictPositiveCellular
