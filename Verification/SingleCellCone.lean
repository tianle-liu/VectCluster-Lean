/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictSingleModel

/-!
# Single Cell Cone

Attaching one strict cell has literal old terms plus one new term.
The coefficient of its genuine cone differential is the actual attaching
chain map with positive sign. All concentration is inside the strict heart.
-/
noncomputable section
namespace Verification.SingleCellCone
open CategoryTheory CategoryTheory.Limits CochainComplex
open Verification.StrictSingleModel
variable {A : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable (P : A) (d : ℤ) (K : CochainComplex A ℤ)
variable (u : (single d P)⟦(-1 : ℤ)⟧ ⟶ K)

def headIso : ((single d P)⟦(-1 : ℤ)⟧).X (d+1) ≅ P :=
  (single d P).shiftFunctorObjXIso (-1) (d+1) d (by omega) ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) d P

omit [HasBinaryBiproducts A] in
theorem source_zero (i : ℤ) (hi : i ≠ d+1) : IsZero (((single d P)⟦(-1 : ℤ)⟧).X i) :=
  IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) d P (i-1) (by omega))
    ((single d P).shiftFunctorObjXIso (-1) i (i-1) (by omega))

def oldIso (i : ℤ) (hi : i ≠ d) : (mappingCone u).X i ≅ K.X i where
  hom := (mappingCone.snd u).v i i (add_zero i)
  inv := (mappingCone.inr u).f i
  hom_inv_id := by
    have h := mappingCone.id_X u i (i+1) rfl
    rw [(source_zero P d (i+1) (by omega)).eq_of_tgt ((mappingCone.fst u).1.v i (i+1) rfl) 0,
      zero_comp,zero_add] at h
    exact h
  inv_hom_id := mappingCone.inr_f_snd_v u i

variable [K.IsStrictlyGE (d+1)]

def newIso : (mappingCone u).X d ≅ P where
  hom := (mappingCone.fst u).1.v d (d+1) rfl ≫ (headIso P d).hom
  inv := (headIso P d).inv ≫ (mappingCone.inl u).v (d+1) d (by omega)
  hom_inv_id := by
    rw [Category.assoc,Iso.hom_inv_id_assoc]
    have h := mappingCone.id_X u d (d+1) rfl
    rw [(K.isZero_of_isStrictlyGE (d+1) d (by omega)).eq_of_tgt ((mappingCone.snd u).v d d (add_zero d)) 0,
      zero_comp,add_zero] at h
    exact h
  inv_hom_id := by
    rw [Category.assoc,mappingCone.inl_v_fst_v_assoc,Iso.inv_hom_id]

theorem new_differential : (newIso P d K u).inv ≫ (mappingCone u).d d (d+1) ≫
    (oldIso P d K u (d+1) (by omega)).hom = (headIso P d).inv ≫ u.f (d+1) := by
  have hd : ((single d P)⟦(-1 : ℤ)⟧).d (d+1) (d+2) = 0 :=
    (source_zero P d (d+2) (by omega)).eq_of_tgt _ _
  dsimp only [newIso,oldIso]
  rw [Category.assoc,reassoc_of% (mappingCone.inl_v_d u (d+1) d (d+2) (by omega) (by omega))]
  simp only [hd,zero_comp,sub_zero,Category.assoc,mappingCone.inr_f_snd_v,Category.comp_id]

omit [K.IsStrictlyGE (d+1)] in
theorem old_differential (i j : ℤ) (hi : i ≠ d) (hj : j ≠ d) :
    (oldIso P d K u i hi).inv ≫ (mappingCone u).d i j ≫ (oldIso P d K u j hj).hom = K.d i j := by
  dsimp only [oldIso]
  rw [mappingCone.inr_f_d_assoc,mappingCone.inr_f_snd_v,Category.comp_id]

theorem support_lower : CochainComplex.IsStrictlyGE (mappingCone u) d := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE (d+1) i (by omega)) (oldIso P d K u i (by omega))

variable [K.IsStrictlyLE 0]
omit [K.IsStrictlyGE (d+1)] in
theorem support_upper (hd : d ≤ 0) : CochainComplex.IsStrictlyLE (mappingCone u) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE 0 i hi) (oldIso P d K u i (by omega))

#print axioms headIso
#print axioms source_zero
#print axioms oldIso
#print axioms newIso
#print axioms new_differential
#print axioms old_differential
#print axioms support_lower
#print axioms support_upper
end Verification.SingleCellCone
