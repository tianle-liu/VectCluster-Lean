/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SurvivorBaseChange

/-!
# Weighted Fixed Basis

Weight support of a constructed fixed-module basis forces its inverse
coordinates to preserve the same weights. This is a consequence of linear
independence and spanning, not an extra condition on the chosen coordinates.
-/

namespace Verification.WeightedFixedBasis

open Verification.SurvivorBaseChange

variable {R ι κ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

variable (w : ι → ℕ) (v : κ → ℕ) (S : Submodule R (ι → R)) (b : Basis κ R S)
variable (hb : ∀ k i,w i≠v k → (b k).val i=0)

omit [DecidableEq κ] in
include hb in
theorem coordinate_support (x : S) (q : ℕ) (hx : ∀i,w i≠q → x.val i=0)
    (k : κ) (hk : v k≠q) : b.equivFun x k=0 := by
  classical
  let c : κ → R := fun j=>if v j=q then b.equivFun x j else 0
  have he : b.equivFun.symm c=x := by
    apply Subtype.ext
    funext i
    rw [Basis.equivFun_symm_apply]
    simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    by_cases hi : w i=q
    · have hh := congrArg (fun y : S=>y.val i) (b.sum_equivFun x)
      simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
      rw [←hh]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : v j=q
      · simp only [c,if_pos hj]
      · rw [hb j i (by omega)]
        simp
    · rw [hx i hi]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : v j=q
      · rw [hb j i (by omega),mul_zero]
      · simp only [c,if_neg hj,zero_mul]
  have hh := congrArg (fun x=>b.equivFun x k) he
  dsimp only at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  simpa only [c,if_neg hk] using hh.symm

variable [Fintype ι] [DecidableEq ι]

theorem inclusion_entry (P : Matrix ι ι R) (b : Basis κ R (fixedModule P)) (i : ι) (k : κ) :
    inclusionMatrix P b i k=(b k).val i := by
  simp [inclusionMatrix,LinearMap.toMatrix'_apply,Basis.equivFun_symm_apply]

omit [DecidableEq κ] in
theorem retraction_support (P : Matrix ι ι R) (hP : P*P=P)
    (b : Basis κ R (fixedModule P)) (hwP : ∀i j,w i≠w j → P i j=0)
    (hb : ∀ k i,w i≠v k → (b k).val i=0) (k : κ) (i : ι) (hi : v k≠w i) :
    retractionMatrix P hP b k i=0 := by
  simp only [retractionMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap]
  change b.equivFun (projection P hP (fun j=>if j=i then 1 else 0)) k=0
  apply coordinate_support w v (fixedModule P) b hb _ (w i) _ k hi
  intro j hj
  change ∑l,P j l*(if l=i then 1 else 0)=0
  simpa using hwP j i hj

#print axioms coordinate_support
#print axioms inclusion_entry
#print axioms retraction_support

end Verification.WeightedFixedBasis
