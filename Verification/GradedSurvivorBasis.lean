/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SurvivorBaseChange
import Verification.GradedHomologyTF

/-!
# Graded Survivor Basis

Each actual degree of the residual complex is finite free after extension of
coefficients.  We construct its basis using the integral idempotent restricted
to that degree, not by inferring graded freeness from ungraded freeness.
-/

namespace Verification.GradedSurvivorBasis

open Verification.GradedPerturbation Verification.GradedHomologyTF

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal degree-p row restriction of a finite matrix. -/
def cut (deg : ι → ℤ) (p : ℤ) (P : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => if deg i=p then P i j else 0

/-- Row restriction acts by the actual homogeneous projection. -/
theorem cut_apply (deg : ι → ℤ) (p : ℤ) (P : Matrix ι ι R) (x : ι → R) :
    Matrix.toLin' (cut deg p P) x=degreePart deg p (Matrix.toLin' P x) := by
  funext i
  by_cases hi : deg i=p
  · simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, cut, degreePart, hi]
  · simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, cut, degreePart, hi]

/-- A homogeneous degree-zero matrix preserves the literal degree submodule. -/
theorem preserves_degree (deg : ι → ℤ) (P : Matrix ι ι R)
    (hP : Homogeneous deg 0 P) (p : ℤ) (x : degreeModule (R := R) deg p) :
    Matrix.toLin' P x.val ∈ degreeModule deg p :=
  (matrixDegreeMap deg P 0 hP p p (by omega) x).property

omit [DecidableEq ι] in
/-- Restricting a degree-zero idempotent to one degree is again an idempotent. -/
theorem cut_square (deg : ι → ℤ) (P : Matrix ι ι R)
    (hP : Homogeneous deg 0 P) (hPP : P*P=P) (p : ℤ) :
    cut deg p P*cut deg p P=cut deg p P := by
  ext i j
  by_cases hi : deg i=p
  · change (∑ k, (if deg i=p then P i k else 0)*(if deg k=p then P k j else 0)) = _
    simp only [if_pos hi, cut]
    change (∑ k, P i k*(if deg k=p then P k j else 0))=P i j
    calc
      _ = ∑ k, P i k*P k j := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : deg k=p
        · rw [if_pos hk]
        · rw [if_neg hk, mul_zero, hP i k (by omega), zero_mul]
      _ = P i j := congrFun (congrFun hPP i) j
  · simp [Matrix.mul_apply, cut, hi]

/-- The degreewise survivor used in the residual complex is the cut idempotent's fixed module. -/
theorem fixedModule_cut (deg : ι → ℤ) (P : Matrix ι ι R)
    (hP : Homogeneous deg 0 P) (p : ℤ) :
    Verification.SurvivorBaseChange.fixedModule (cut deg p P) =
      Verification.PerturbedHomologyModel.fixedModule deg P p := by
  apply Submodule.ext
  intro x
  change (Matrix.toLin' (cut deg p P) x-x=0) ↔
    (x ∈ degreeModule deg p ∧ Matrix.toLin' P x=x)
  rw [sub_eq_zero, cut_apply]
  constructor
  · intro hx
    have hd : x ∈ degreeModule deg p := by
      rw [← hx]
      exact degreePart_mem deg p _
    refine ⟨hd, ?_⟩
    have hm := degreePart_fixed deg p
      (⟨Matrix.toLin' P x,preserves_degree deg P hP p ⟨x,hd⟩⟩ : degreeModule deg p)
    exact hm.symm.trans hx
  · rintro ⟨hd,hx⟩
    rw [hx]
    exact degreePart_fixed deg p ⟨x,hd⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Restriction commutes with actual extension of integral coefficients. -/
theorem cut_cast (deg : ι → ℤ) (P : Matrix ι ι ℤ) (p : ℤ) :
    (cut deg p P).map (Int.castRingHom R)=cut deg p (P.map (Int.castRingHom R)) := by
  ext i j
  by_cases hi : deg i=p <;> simp [cut, Matrix.map_apply, hi]

omit [Fintype ι] [DecidableEq ι] in
/-- Degree-zero support survives coefficient extension. -/
theorem cast_degree (deg : ι → ℤ) (P : Matrix ι ι ℤ)
    (hP : Homogeneous deg 0 P) : Homogeneous deg 0 (P.map (Int.castRingHom R)) := by
  intro i j hij
  simp [Matrix.map_apply, hP i j hij]

/-- The integral cut fixed module has an actual finite basis. -/
noncomputable def integralDegreeBasis (deg : ι → ℤ) (P : Matrix ι ι ℤ) (p : ℤ) :
    Basis (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule (cut deg p P))))
      ℤ (Verification.SurvivorBaseChange.fixedModule (cut deg p P)) :=
  Module.finBasis ℤ _

/-- Constructed finite free basis of the actual degree-p survivor over any coefficient ring. -/
noncomputable def scalarDegreeBasis (deg : ι → ℤ) (P : Matrix ι ι ℤ)
    (hP : Homogeneous deg 0 P) (hPP : P*P=P) (p : ℤ) :
    Basis (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule (cut deg p P))))
      R (Verification.PerturbedHomologyModel.fixedModule deg (P.map (Int.castRingHom R)) p) :=
  (Verification.SurvivorBaseChange.scalarBasis (cut deg p P) (cut_square deg P hP hPP p)
    (integralDegreeBasis deg P p)).map
    (LinearEquiv.ofEq _ _ (by rw [cut_cast]; exact fixedModule_cut deg _ (cast_degree deg P hP) p))

#print axioms cut
#print axioms cut_apply
#print axioms preserves_degree
#print axioms cut_square
#print axioms fixedModule_cut
#print axioms cut_cast
#print axioms cast_degree
#print axioms integralDegreeBasis
#print axioms scalarDegreeBasis

end Verification.GradedSurvivorBasis
