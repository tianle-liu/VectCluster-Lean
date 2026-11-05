/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithCharacters

/-!
# Smith Scaled Retraction

A tame Smith presentation gives an integral retraction up to a
scalar invertible in the ground ring. Conversely such a retraction
forces every Smith coefficient to be invertible.
-/
noncomputable section
namespace Verification.SmithScaledRetraction
variable {M ι : Type*} [AddCommGroup M] {N : Submodule ℤ M} {n : ℕ}
variable (s : Basis.SmithNormalForm N ι n)

def denominator : ℤ := ∏ i,s.a i
def cofactor (i : Fin n) : ℤ := ∏ j∈Finset.univ.erase i,s.a j

theorem cofactor_mul (i : Fin n) : cofactor s i*s.a i=denominator s := by
  classical
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

def coordinate (i : Fin n) : M →ₗ[ℤ] ℤ :=
  (Finsupp.lapply (s.f i)).comp s.bM.repr.toLinearMap

def retraction : M →ₗ[ℤ] N :=
  ∑ i,cofactor s i • ((LinearMap.toSpanSingleton ℤ N (s.bN i)).comp (coordinate s i))

theorem coordinate_basis (i j : Fin n) : coordinate s i (s.bN j : M) =
    if j=i then s.a j else 0 := by
  classical
  change s.bM.repr (s.bN j : M) (s.f i) = _
  rw [s.snf,map_smul,Basis.repr_self,Finsupp.smul_apply]
  by_cases h : j=i
  · subst j
    simp
  · simp [Finsupp.single_eq_of_ne (fun hh=>h (s.f.injective hh)),h]

theorem retraction_basis (i : Fin n) : retraction s (s.bN i : M)=denominator s • s.bN i := by
  classical
  simp only [retraction,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply,coordinate_basis]
  simp only [ite_smul,zero_smul,smul_ite,smul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,if_true,smul_smul,cofactor_mul]

theorem retraction_subtype : (retraction s).comp N.subtype=denominator s • LinearMap.id := by
  apply s.bN.ext
  intro i
  exact retraction_basis s i

variable (R : Type*) [CommRing R]

theorem intCast_unit_of_natAbs (a : ℤ) (h : IsUnit (a.natAbs:R)) : IsUnit (a:R) := by
  cases a with
  | ofNat a => simpa using h
  | negSucc a => simpa only [Int.cast_negSucc,Int.natAbs_negSucc] using h.neg

theorem natAbs_unit_of_intCast (a : ℤ) (h : IsUnit (a:R)) : IsUnit (a.natAbs:R) := by
  cases a with
  | ofNat a => simpa using h
  | negSucc a =>
    simpa only [Int.cast_negSucc,Int.natAbs_negSucc,neg_neg] using h.neg

theorem denominator_unit (h : ∀ i,IsUnit ((s.a i).natAbs:R)) : IsUnit (denominator s:R) := by
  classical
  rw [denominator,Int.cast_prod]
  have hprod (t : Finset (Fin n)) : IsUnit (∏ i ∈ t,(s.a i:R)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi]
      exact (intCast_unit_of_natAbs R (s.a i) (h i)).mul ih
  exact hprod Finset.univ

theorem coefficients_unit_of_retraction (r : M →ₗ[ℤ] N) (d : ℤ)
    (hr : r.comp N.subtype=d • LinearMap.id) (hd : IsUnit (d:R)) :
    ∀ i,IsUnit ((s.a i).natAbs:R) := by
  intro i
  have hi := LinearMap.congr_fun hr (s.bN i)
  change r (s.bN i : M)=d • s.bN i at hi
  rw [s.snf,map_smul] at hi
  have h := congrArg (fun z : N=>s.bN.repr z i) hi
  simp only [map_smul,Finsupp.smul_apply,Basis.repr_self,Finsupp.single_eq_same,
    smul_eq_mul,mul_one] at h
  apply natAbs_unit_of_intCast
  have hh : IsUnit ((s.a i:R)*(s.bN.repr (r (s.bM (s.f i))) i:R)) := by
    rw [← Int.cast_mul,h]
    exact hd
  exact isUnit_of_mul_isUnit_left hh

#print axioms denominator
#print axioms cofactor
#print axioms cofactor_mul
#print axioms coordinate
#print axioms retraction
#print axioms coordinate_basis
#print axioms retraction_basis
#print axioms retraction_subtype
#print axioms intCast_unit_of_natAbs
#print axioms natAbs_unit_of_intCast
#print axioms denominator_unit
#print axioms coefficients_unit_of_retraction
end Verification.SmithScaledRetraction
