/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenGraphBridge
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Exterior Total Basis

The full exterior algebra, not just a fixed exterior power, is free on all
finite subsets. This assembles the already proved ordered homogeneous bases
through the actual exterior grading and identifies their values with words.
-/

namespace Verification.ExteriorTotalBasis

open Verification.EvenBasis Verification.EvenGraphBridge

variable {R α : Type*} [CommRing R] [Fintype α] [LinearOrder α]

noncomputable def totalIndexEquiv : (Σ n : ℕ, WedgeIndex α n) ≃ Finset α :=
  (Equiv.sigmaCongrRight (fun n => wedgeFinsetEquiv n)).trans
    (Equiv.sigmaFiberEquiv Finset.card)

noncomputable def homogeneousBasis :
    Basis (Σ n : ℕ, WedgeIndex α n) R (ExteriorAlgebra R (α → R)) :=
  (DirectSum.Decomposition.isInternal
    (fun n : ℕ => ExteriorAlgebra.exteriorPower R n (α → R))).collectedBasis
      (fun n => orderedExteriorBasis n)

noncomputable def subsetBasis : Basis (Finset α) R (ExteriorAlgebra R (α → R)) :=
  homogeneousBasis.reindex totalIndexEquiv

omit [Fintype α] in
theorem ofFn_orderEmb (A : Finset α) :
    List.ofFn (A.orderEmbOfFin rfl) = A.sort (· ≤ ·) := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    A.listMap_orderEmbOfFin_finRange rfl

theorem subsetBasis_apply (A : Finset α) :
    subsetBasis (R := R) A = word (A.sort (· ≤ ·)) := by
  rw [subsetBasis, Basis.reindex_apply]
  change homogeneousBasis (totalIndexEquiv.symm A) = _
  rw [homogeneousBasis, DirectSum.IsInternal.collectedBasis_coe]
  change (orderedExteriorBasis (R := R) A.card (A.orderEmbOfFin rfl) :
    ExteriorAlgebra R (α → R)) = _
  rw [orderedExteriorBasis_apply]
  simp only [orderedWedge, exteriorPower.ιMulti_apply_coe]
  rw [← word_ofFn, ofFn_orderEmb]

noncomputable def coefficientEquiv : ExteriorAlgebra R (α → R) ≃ₗ[R] (Finset α →₀ R) :=
  subsetBasis.repr

theorem coefficientEquiv_word (A : Finset α) :
    coefficientEquiv (word (A.sort (· ≤ ·)) : ExteriorAlgebra R (α → R)) = Finsupp.single A 1 := by
  rw [← subsetBasis_apply]
  exact Basis.repr_self _ _

theorem coefficientEquiv_symm_single (A : Finset α) (r : R) :
    coefficientEquiv.symm (Finsupp.single A r) = r • word (A.sort (· ≤ ·)) := by
  rw [← subsetBasis_apply]
  exact Basis.repr_symm_single _ _ _

theorem word_independent : LinearIndependent R (fun A : Finset α => word (R := R) (A.sort (· ≤ ·))) := by
  simpa only [← subsetBasis_apply] using (subsetBasis (R := R) (α := α)).linearIndependent

theorem word_spans :
    Submodule.span R (Set.range (fun A : Finset α => word (R := R) (A.sort (· ≤ ·)))) = ⊤ := by
  simpa only [← subsetBasis_apply] using (subsetBasis (R := R) (α := α)).span_eq

theorem subsetBasis_totalIndex (n : ℕ) (a : WedgeIndex α n) :
    subsetBasis (R := R) (totalIndexEquiv ⟨n,a⟩) =
      (orderedExteriorBasis (R := R) n a : ExteriorAlgebra R (α → R)) := by
  rw [subsetBasis, Basis.reindex_apply, Equiv.symm_apply_apply,
    homogeneousBasis, DirectSum.IsInternal.collectedBasis_coe]

omit [Fintype α] in
theorem totalIndex_card (n : ℕ) (a : WedgeIndex α n) :
    (totalIndexEquiv ⟨n,a⟩).card = n := by
  change (Finset.univ.image a).card = n
  rw [Finset.card_image_of_injective _ a.injective]
  simp

theorem coefficientEquiv_homogeneous (n : ℕ)
    (x : ExteriorAlgebra.exteriorPower R n (α → R)) (A : Finset α) (hA : A.card ≠ n) :
    coefficientEquiv (x : ExteriorAlgebra R (α → R)) A = 0 := by
  classical
  have hx := (orderedExteriorBasis (R := R) (α := α) n).sum_repr x
  apply_fun (fun y : ExteriorAlgebra.exteriorPower R n (α → R) =>
    coefficientEquiv (y : ExteriorAlgebra R (α → R)) A) at hx
  rw [← hx]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [← subsetBasis_totalIndex, show coefficientEquiv (subsetBasis (R := R) (totalIndexEquiv ⟨n,a⟩)) =
    Finsupp.single (totalIndexEquiv ⟨n,a⟩) 1 from Basis.repr_self _ _]
  have hn : totalIndexEquiv ⟨n,a⟩ ≠ A := by
    intro h
    exact hA (h ▸ totalIndex_card n a)
  simp [hn]

#print axioms totalIndexEquiv
#print axioms homogeneousBasis
#print axioms subsetBasis
#print axioms ofFn_orderEmb
#print axioms subsetBasis_apply
#print axioms coefficientEquiv
#print axioms coefficientEquiv_word
#print axioms coefficientEquiv_symm_single
#print axioms word_independent
#print axioms word_spans
#print axioms subsetBasis_totalIndex
#print axioms totalIndex_card
#print axioms coefficientEquiv_homogeneous

end Verification.ExteriorTotalBasis
