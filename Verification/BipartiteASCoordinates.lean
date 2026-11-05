/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AnticliqueSubcolumns
import Verification.PrimitiveBipartiteExtension
import Mathlib.LinearAlgebra.Pi

/-!
# Bipartite AS Coordinates

Exact finite coordinates for AS on the larger side of a bipartition.
The selected columns and deleted rows are the manuscript's literal
AnticliqueSubcolumns.selectedMap, not a new primitivity hypothesis.
-/

noncomputable section
namespace Verification.BipartiteASCoordinates
open Classical Verification.AnticliqueSubcolumns
variable (P Q F : Type) [Fintype P] [Fintype Q] [Fintype F]

def selected : Finset (P ⊕ Q) := Finset.univ.filter (fun v : P ⊕ Q=>v.isLeft=true)

def sourceIndex : selected P Q ≃ P where
  toFun i := by
    rcases i with ⟨i,hi⟩
    cases i with
    | inl p => exact p
    | inr q => simp [selected] at hi
  invFun p := ⟨Sum.inl p,by simp [selected]⟩
  left_inv i := by
    rcases i with ⟨i,hi⟩
    cases i with
    | inl p => rfl
    | inr q => simp [selected] at hi
  right_inv _ := rfl

def targetIndex : Rows (C:=F) (selected P Q) ≃ (Q ⊕ F) where
  toFun i := by
    rcases i with ⟨i,hi⟩
    cases i with
    | inl v =>
      cases v with
      | inl p => exact (hi (Sum.inl p) (by simp [selected]) rfl).elim
      | inr q => exact Sum.inl q
    | inr f => exact Sum.inr f
  invFun i := match i with
    | Sum.inl q => ⟨Sum.inl (Sum.inr q),by intro v hv;cases v <;> simp_all [selected]⟩
    | Sum.inr f => ⟨Sum.inr f,by simp⟩
  left_inv i := by
    rcases i with ⟨i,hi⟩
    cases i with
    | inl v =>
      cases v with
      | inl p => exact (hi (Sum.inl p) (by simp [selected]) rfl).elim
      | inr q => rfl
    | inr f => rfl
  right_inv i := by cases i <;> rfl

def sourceCoordinates : (selected P Q →₀ ℤ) ≃ₗ[ℤ] (P → ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (selected P Q)).trans
    (LinearEquiv.funCongrLeft ℤ ℤ (sourceIndex P Q).symm)

def targetCoordinates : (Rows (C:=F) (selected P Q) →₀ ℤ) ≃ₗ[ℤ] ((Q → ℤ) × (F → ℤ)) :=
  ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Rows (C:=F) (selected P Q))).trans
    (LinearEquiv.funCongrLeft ℤ ℤ (targetIndex P Q F).symm)).trans
      (LinearEquiv.sumArrowLequivProdArrow Q F ℤ ℤ)

variable {P Q F}
def matrix (D : Matrix P Q ℤ) (E : Matrix Q P ℤ) (C : Matrix F P ℤ) (G : Matrix F Q ℤ) :
    Matrix ((P ⊕ Q) ⊕ F) (P ⊕ Q) ℤ
  | Sum.inl (Sum.inl _),Sum.inl _ => 0
  | Sum.inl (Sum.inl p),Sum.inr q => D p q
  | Sum.inl (Sum.inr q),Sum.inl p => E q p
  | Sum.inl (Sum.inr _),Sum.inr _ => 0
  | Sum.inr f,Sum.inl p => C f p
  | Sum.inr f,Sum.inr q => G f q

variable (D : Matrix P Q ℤ) (E : Matrix Q P ℤ) (C : Matrix F P ℤ) (G : Matrix F Q ℤ)

theorem source_single (p : P) :
    (sourceCoordinates P Q).symm (Pi.single p (1:ℤ)) =
      Finsupp.single ((sourceIndex P Q).symm p) 1 := by
  apply (sourceCoordinates P Q).injective
  funext q
  change Pi.single p 1 q=Finsupp.single ((sourceIndex P Q).symm p) 1 ((sourceIndex P Q).symm q)
  simp [Pi.single_apply,Finsupp.single_apply,eq_comm]

theorem selected_coordinate :
    (targetCoordinates P Q F).toLinearMap.comp
      ((selectedMap (matrix D E C G) (selected P Q)).comp (sourceCoordinates P Q).symm.toLinearMap)=
    E.mulVecLin.prod C.mulVecLin := by
  apply (Pi.basisFun ℤ P).ext
  intro p
  simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,source_single,
    selectedMap,Finsupp.linearCombination_single,one_smul]
  apply Prod.ext
  · funext q
    change (column (matrix D E C G) (selected P Q) ((sourceIndex P Q).symm p))
      ((targetIndex P Q F).symm (Sum.inl q))=E.mulVec (Pi.single p 1) q
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one,one_smul]
    rfl
  · funext f
    change (column (matrix D E C G) (selected P Q) ((sourceIndex P Q).symm p))
      ((targetIndex P Q F).symm (Sum.inr f))=C.mulVec (Pi.single p 1) f
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one,one_smul]
    rfl

/-- AS on the actual independent side supplies a retraction of the literal
E/C block after only explicit finite coordinate changes. -/
def selectedRetraction (h : AS (matrix D E C G) (selected P Q)) :
    ((Q → ℤ) × (F → ℤ)) →ₗ[ℤ] (P → ℤ) :=
  (sourceCoordinates P Q).toLinearMap.comp
    (((LinearMap.fst ℤ _ _).comp
      (PrimitiveLattice.primitive_columns_split_compatible
        (selectedMap (matrix D E C G) (selected P Q)) h.1 h.2).choose.toLinearMap).comp
          (targetCoordinates P Q F).symm.toLinearMap)

theorem selectedRetraction_left (h : AS (matrix D E C G) (selected P Q)) :
    (selectedRetraction D E C G h).comp (E.mulVecLin.prod C.mulVecLin)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hx:=LinearMap.congr_fun (selected_coordinate D E C G) x
  change targetCoordinates P Q F (selectedMap (matrix D E C G) (selected P Q)
    ((sourceCoordinates P Q).symm x))=(E.mulVecLin.prod C.mulVecLin) x at hx
  change sourceCoordinates P Q
    (((PrimitiveLattice.primitive_columns_split_compatible
      (selectedMap (matrix D E C G) (selected P Q)) h.1 h.2).choose
        ((targetCoordinates P Q F).symm ((E.mulVecLin.prod C.mulVecLin) x))).1)=x
  rw [← hx,LinearEquiv.symm_apply_apply,
    (PrimitiveLattice.primitive_columns_split_compatible
      (selectedMap (matrix D E C G) (selected P Q)) h.1 h.2).choose_spec,
    LinearEquiv.apply_symm_apply]

#print axioms selected
#print axioms sourceIndex
#print axioms targetIndex
#print axioms sourceCoordinates
#print axioms targetCoordinates
#print axioms matrix
#print axioms source_single
#print axioms selected_coordinate
#print axioms selectedRetraction
#print axioms selectedRetraction_left

end Verification.BipartiteASCoordinates
