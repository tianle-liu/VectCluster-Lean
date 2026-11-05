/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellAttachment
import Verification.StrictFiniteFiltration

/-!
# Strict Cellular Tower

A genuine strict cellular tower. Each step is the actual cone of its
retained attaching chain map, not an arbitrary existential model. The
strict degrees at stage p lie in [1-p,0], and the construction preserves
the original filtration maps under the strict universal comparisons.
-/
noncomputable section
namespace Verification.StrictCellularTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable (H : ChainRepresentability (A := A)) (F : ℕ ⥤ CochainComplex C ℤ)

structure Stage (p : ℕ) (X : D) where
  model : Model J X
  lower : model.complex.IsStrictlyGE (1-(p : ℤ))
  upper : model.complex.IsStrictlyLE 0

def zeroStage (X : D) (hz : IsZero X) : Stage J 0 X where
  model := ofIsZero J X hz
  lower := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i _
    exact isZero_zero A
  upper := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i _
    exact isZero_zero A

variable (cells : ∀ p : ℕ,Cell J (-(p : ℤ))
  (L.obj (DerivedCategory.Q.obj (FilteredConeComplex.relative F p))))

def attachment (p : ℕ) (M : Stage J p (L.obj (DerivedCategory.Q.obj (F.obj p)))) :=
  StrictCellAttachment.attach J M.model (cells p) (StrictFiniteFiltration.step_distinguished L F p) H

def successor (p : ℕ) (M : Stage J p (L.obj (DerivedCategory.Q.obj (F.obj p)))) :
    Stage J (p+1) (L.obj (DerivedCategory.Q.obj (F.obj (p+1)))) where
  model := StrictCellAttachment.model J M.model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)
  lower := by
    letI : M.model.complex.IsStrictlyGE (-(p : ℤ)+1) := by
      convert M.lower using 1; omega
    simpa only [Nat.cast_add,Nat.cast_one,show 1-((p : ℤ)+1)=-(p : ℤ) by omega] using
      StrictCellAttachment.support_lower J M.model (cells p)
        (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M)
  upper := by
    letI := M.upper
    exact StrictCellAttachment.support_upper J M.model (cells p)
      (StrictFiniteFiltration.step_distinguished L F p) (attachment J L H F cells p M) (by omega)

variable (hzero : IsZero (L.obj (DerivedCategory.Q.obj (F.obj 0))))

def tower : (p : ℕ) → Stage J p (L.obj (DerivedCategory.Q.obj (F.obj p)))
  | 0 => zeroStage J _ hzero
  | p+1 => successor J L H F cells p (tower p)

def inclusion (p : ℕ) : (tower J L H F cells hzero p).model.complex ⟶
    (tower J L H F cells hzero (p+1)).model.complex :=
  CochainComplex.mappingCone.inr (attachment J L H F cells p (tower J L H F cells hzero p)).attaching

theorem inclusion_square (p : ℕ) : L.map (DerivedCategory.Q.map (FilteredConeComplex.inclusion F p)) ≫
    (tower J L H F cells hzero (p+1)).model.comparison =
      (tower J L H F cells hzero p).model.comparison ≫ J.map (DerivedCategory.Q.map (inclusion J L H F cells hzero p)) := by
  simpa only [tower,successor,inclusion] using
    (StrictCellAttachment.inclusion_square J (tower J L H F cells hzero p).model (cells p)
    (StrictFiniteFiltration.step_distinguished L F p)
    (attachment J L H F cells p (tower J L H F cells hzero p)))

#print axioms Stage
#print axioms zeroStage
#print axioms attachment
#print axioms successor
#print axioms tower
#print axioms inclusion
#print axioms inclusion_square
end Verification.StrictCellularTower
