/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellularTerms
import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# Strict Cellular Realization

The strict cell complex really realizes the retained finite cone tower.
Its terms are the cell projectives and its differential is the stable
literal attaching differential. No ambient homology objects occur.
-/
noncomputable section
namespace Verification.StrictCellularRealization
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictProjectiveModel Verification.StrictSingleModel Verification.StrictCellularTower
open Verification.StrictCellularTerms
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
variable (N : ℕ) (hstop : ∀ q, N ≤ q → IsZero (cells q).term)

def degreeIso (q : ℕ) : ((tower J L H F cells hzero N).model.complex).X (-(q : ℤ)) ≅ (cells q).term := by
  by_cases hq : q<N
  · exact termIso J L H F cells hzero N q hq
  · letI := (tower J L H F cells hzero N).lower
    exact (((tower J L H F cells hzero N).model.complex).isZero_of_isStrictlyGE (1-(N : ℤ)) (-(q : ℤ)) (by omega)).iso (hstop q (by omega))

def restrictionIso : ((tower J L H F cells hzero N).model.complex).restriction ComplexShape.embeddingDownNat ≅
    complex J L H F cells hzero :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso J L H F cells hzero N hstop) (by
    intro i q hiq
    change q+1=i at hiq
    subst i
    by_cases hq : q+1<N
    · change (degreeIso J L H F cells hzero N hstop (q+1)).hom ≫ _ =
        ((tower J L H F cells hzero N).model.complex).d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫ (degreeIso J L H F cells hzero N hstop q).hom
      rw [complex_d]
      simp only [degreeIso,dif_pos hq,dif_pos (show q<N by omega)]
      unfold d
      rw [← differential_stable J L H F cells hzero N q hq]
      simp only [differential,Category.assoc,Iso.hom_inv_id_assoc]
    · letI := (tower J L H F cells hzero N).lower
      exact (((tower J L H F cells hzero N).model.complex).isZero_of_isStrictlyGE (1-(N : ℤ)) (-((q+1 : ℕ) : ℤ)) (by omega)).eq_of_src _ _)

def cochain : CochainComplex A ℤ :=
  (complex J L H F cells hzero).extend ComplexShape.embeddingDownNat

def comparison : (tower J L H F cells hzero N).model.complex ⟶ cochain J L H F cells hzero :=
  ComplexShape.embeddingDownNat.liftExtend
    (restrictionIso J L H F cells hzero N hstop).hom
    (fun _ h _ _ => h.false_of_isTruncLE.elim)

theorem comparison_isIso : IsIso (comparison J L H F cells hzero N hstop) := by
  classical
  letI : ∀ i, IsIso ((comparison J L H F cells hzero N hstop).f i) := by
    intro i
    by_cases hi : ∃ q : ℕ, -(q : ℤ)=i
    · obtain ⟨q,hq⟩ := hi
      apply (ComplexShape.embeddingDownNat.isIso_liftExtend_f_iff
        (restrictionIso J L H F cells hzero N hstop).hom
        (fun _ h _ _ => h.false_of_isTruncLE.elim) hq).mpr
      change IsIso ((degreeIso J L H F cells hzero N hstop q).hom)
      infer_instance
    · letI := (tower J L H F cells hzero N).upper
      have hpositive : 0 < i := by
        by_contra h
        apply hi
        exact ⟨(-i).toNat,by omega⟩
      exact isIso_of_source_target_iso_zero _
        (((tower J L H F cells hzero N).model.complex).isZero_of_isStrictlyLE 0 i hpositive).isoZero
        ((complex J L H F cells hzero).isZero_extend_X ComplexShape.embeddingDownNat i
          (by simpa only [ComplexShape.embeddingDownNat_f,not_exists] using hi)).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

def realizationIso : (tower J L H F cells hzero N).model.complex ≅ cochain J L H F cells hzero := by
  letI := comparison_isIso J L H F cells hzero N hstop
  exact asIso (comparison J L H F cells hzero N hstop)

#print axioms degreeIso
#print axioms restrictionIso
#print axioms cochain
#print axioms comparison
#print axioms comparison_isIso
#print axioms realizationIso
end Verification.StrictCellularRealization
