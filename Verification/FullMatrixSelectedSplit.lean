/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalSelectedColumns

/-!
# Full Matrix Selected Split

A full integer matrix splitting restricts to a primitive selected-column
splitting after rows proved zero are removed.
-/
noncomputable section
namespace Verification.FullMatrixSelectedSplit
open Verification.AnticliqueSubcolumns
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V]
variable (B : Matrix (V ⊕ C) V ℤ) (I : Finset V)

def restore : (Rows (C:=C) I →₀ ℤ) →ₗ[ℤ] ((V ⊕ C) → ℤ) := by
  classical
  exact {
    toFun := fun x a => if h : ∀ v∈I,a≠Sum.inl v then x ⟨a,h⟩ else 0
    map_add' := by intro x y;funext a;simp only [Pi.add_apply];split_ifs <;> rfl
    map_smul' := by intro r x;funext a;simp only [Pi.smul_apply];split_ifs <;> simp only [Finsupp.smul_apply,smul_zero,RingHom.id_apply] }


theorem restore_column (hzero : ∀ i∈I,∀ j∈I,B (Sum.inl i) j=0) (i : I) :
    restore I (column B I i)=fun a=>B a i.val := by
  classical
  funext a
  change (if h : ∀ v∈I,a≠Sum.inl v then column B I i ⟨a,h⟩ else 0)=B a i.val
  split
  · rfl
  · rename_i h
    push_neg at h
    obtain ⟨v,hv,rfl⟩ := h
    exact (hzero v hv i.val i.property).symm

def restrict : (V → ℤ) →ₗ[ℤ] (I →₀ ℤ) where
  toFun x := Finsupp.equivFunOnFinite.symm (fun i=>x i.val)
  map_add' _ _ := by ext;rfl
  map_smul' _ _ := by ext;rfl

def retraction (r : ((V ⊕ C) → ℤ) →ₗ[ℤ] (V → ℤ)) :
    (Rows (C:=C) I →₀ ℤ) →ₗ[ℤ] (I →₀ ℤ) :=
  (restrict I).comp (r.comp (restore I))

theorem left (r : ((V ⊕ C) → ℤ) →ₗ[ℤ] (V → ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id)
    (hzero : ∀ i∈I,∀ j∈I,B (Sum.inl i) j=0) :
    (retraction I r).comp (selectedMap B I)=LinearMap.id := by
  classical
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,selectedMap,
    Finsupp.linearCombination_single,one_smul]
  change restrict I (r (restore I (column B I i)))=Finsupp.single i 1
  rw [restore_column B I hzero]
  have hm : B.mulVec (Pi.single i.val 1)=fun a=>B a i.val := by
    ext a
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [← hm]
  have hh := LinearMap.congr_fun hr (Pi.single i.val 1)
  change r (B.mulVec (Pi.single i.val 1))=Pi.single i.val 1 at hh
  rw [hh]
  ext j
  simp [restrict,Pi.single_apply,Finsupp.single_apply,Subtype.ext_iff,eq_comm]

theorem AS (r : ((V ⊕ C) → ℤ) →ₗ[ℤ] (V → ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id)
    (hzero : ∀ i∈I,∀ j∈I,B (Sum.inl i) j=0) : AnticliqueSubcolumns.AS B I := by
  have hl : Function.LeftInverse (retraction I r) (selectedMap B I) :=
    fun x=>LinearMap.congr_fun (left B I r hr hzero) x
  exact ⟨hl.injective,CliqueSaturation.split_range_saturated _ _ hl⟩

#print axioms restore
#print axioms restore_column
#print axioms restrict
#print axioms retraction
#print axioms left
#print axioms AS
end Verification.FullMatrixSelectedSplit
