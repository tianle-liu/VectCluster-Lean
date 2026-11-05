/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFullRank
import Verification.AnticliqueReindex

/-!
# Path Forest Original RFR

AS implies full extended RFR for an arbitrarily labelled signed path
forest. The forest hypothesis is the literal principal-matrix coordinate
identity; neither full rank, saturation nor any frozen basis is assumed.
-/

noncomputable section
namespace Verification.PathForestOriginalRFR
open Classical Verification.PathForestMatching Verification.PathForestFullRank
variable {S V F : Type} [Fintype S] [Fintype V] [Fintype F]
variable (m : S → ℕ) (o : S → Bool)
variable (u : (s : S) → largeIndex (m s) (o s) → ℤˣ) (v : (s : S) → Fin (m s) → ℤˣ)
variable (e : (PIndex m o ⊕ QIndex m) ≃ V) (B : Matrix (V ⊕ F) V ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (e j)=principal m o u v i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent B I → AnticliqueSubcolumns.AS B I)

def frozenP : Matrix F (PIndex m o) ℤ := fun f p=>B (Sum.inr f) (e (Sum.inl p))
def frozenQ : Matrix F (QIndex m) ℤ := fun f q=>B (Sum.inr f) (e (Sum.inr q))

include hprincipal in
omit [Fintype V] [Fintype F] in
theorem reindexed_matrix : B.submatrix (ExchangeReindex.rows e) e=
    extended m o u v (frozenP m o e B) (frozenQ m o e B) := by
  ext i j
  cases i with
  | inl i =>
    change B (Sum.inl (e i)) (e j)=_
    rw [hprincipal]
    cases i <;> cases j <;> rfl
  | inr f => cases j <;> rfl

omit [Fintype V] [Fintype F] in
theorem selected_independent : ExchangeReindex.PrincipalIndependent
    (extended m o u v (frozenP m o e B) (frozenQ m o e B))
      (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)) := by
  intro i hi j hj _
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => simp [BipartiteASCoordinates.selected] at hj
  | inr i => simp [BipartiteASCoordinates.selected] at hi

include hprincipal hAS in
theorem selected_AS : AnticliqueSubcolumns.AS
    (extended m o u v (frozenP m o e B) (frozenQ m o e B))
      (BipartiteASCoordinates.selected (PIndex m o) (QIndex m)) := by
  rw [← reindexed_matrix m o u v e B hprincipal]
  change AnticliqueSubcolumns.AS (ExchangeReindex.matrix e B) _
  apply (AnticliqueReindex.AS_iff e B _).mp
  apply hAS
  apply (ExchangeReindex.independent_iff e B _).mpr
  change ExchangeReindex.PrincipalIndependent (B.submatrix (ExchangeReindex.rows e) e) _
  rw [reindexed_matrix m o u v e B hprincipal]
  exact selected_independent m o u v e B


def columnCoordinates : (V → ℤ) ≃ₗ[ℤ] ((PIndex m o ⊕ QIndex m) → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ e
def rowCoordinates : ((V ⊕ F) → ℤ) ≃ₗ[ℤ] (((PIndex m o ⊕ QIndex m) ⊕ F) → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ (ExchangeReindex.rows e)

include hprincipal in
omit [Fintype F] in
theorem column_conjugacy (x : V → ℤ) : rowCoordinates m o e (B.mulVec x)=
    (extended m o u v (frozenP m o e B) (frozenQ m o e B)).mulVec (columnCoordinates m o e x) := by
  have h:=Matrix.submatrix_mulVec_equiv B (x ∘ e) (ExchangeReindex.rows e) e
  have he : (x ∘ e) ∘ e.symm=x := by funext i;simp
  rw [he,reindexed_matrix m o u v e B hprincipal] at h
  exact h.symm

def retraction : ((V ⊕ F) → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (columnCoordinates m o e).symm.toLinearMap.comp
    ((PathForestFullRank.retraction m o u v (frozenP m o e B) (frozenQ m o e B)
      (selected_AS m o u v e B hprincipal hAS)).comp (rowCoordinates m o e).toLinearMap)

theorem left : (retraction m o u v e B hprincipal hAS).comp B.mulVecLin=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (columnCoordinates m o e).symm
    (PathForestFullRank.retraction m o u v (frozenP m o e B) (frozenQ m o e B)
      (selected_AS m o u v e B hprincipal hAS) (rowCoordinates m o e (B.mulVec x)))=x
  rw [column_conjugacy m o u v e B hprincipal]
  have h:=LinearMap.congr_fun (PathForestFullRank.left m o u v (frozenP m o e B) (frozenQ m o e B)
    (selected_AS m o u v e B hprincipal hAS)) (columnCoordinates m o e x)
  change PathForestFullRank.retraction m o u v (frozenP m o e B) (frozenQ m o e B)
    (selected_AS m o u v e B hprincipal hAS)
      ((extended m o u v (frozenP m o e B) (frozenQ m o e B)).mulVec (columnCoordinates m o e x))=
        columnCoordinates m o e x at h
  rw [h,LinearEquiv.symm_apply_apply]

include hprincipal hAS in
theorem full_rank_saturated : Function.Injective B.mulVecLin ∧ FreezingLattice.Saturated (LinearMap.range B.mulVecLin) := by
  have h : Function.LeftInverse (retraction m o u v e B hprincipal hAS) B.mulVecLin :=
    fun x=>LinearMap.congr_fun (left m o u v e B hprincipal hAS) x
  exact ⟨h.injective,CliqueSaturation.split_range_saturated _ _ h⟩

#print axioms frozenP
#print axioms frozenQ
#print axioms reindexed_matrix
#print axioms selected_independent
#print axioms selected_AS
#print axioms columnCoordinates
#print axioms rowCoordinates
#print axioms column_conjugacy
#print axioms retraction
#print axioms left
#print axioms full_rank_saturated
end Verification.PathForestOriginalRFR
