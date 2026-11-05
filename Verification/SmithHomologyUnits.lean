/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralSmithScalarIso

/-!
# Smith Homology Units

Torsion-free actual cohomology forces the constructed boundary Smith
entries to be units. Saturation is proved inside the actual cycle module
via its actual categorical homology quotient.
-/
noncomputable section
namespace Verification.SmithHomologyUnits
open CategoryTheory
open Verification.SmithComplexCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

omit [IsDomain R] [IsPrincipalIdealRing R]
  [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)] in
theorem boundary_eq (n : ℤ) : boundaries C n =
    LinearMap.range (C.sc' (n-1) n (n+1)).moduleCatToCycles := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y,Subtype.ext hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨y,congrArg Subtype.val hy⟩

/-- The constructed Smith boundary quotient is the genuine cohomology. -/
def homologyEquiv (n : ℤ) : ((cycles C n) ⧸ (boundaries C n)) ≃ₗ[R] C.homology n :=
  (Submodule.quotEquivOfEq _ _ (boundary_eq C n)).trans
    (((C.homologyIsoSc' (n-1) n (n+1) (by simp) (by simp)).trans
      ((C.sc' (n-1) n (n+1)).moduleCatHomologyIso)).toLinearEquiv.symm)

omit [IsDomain R] [IsPrincipalIdealRing R]
  [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)] in
theorem saturated (n : ℤ) (htf : NoZeroSMulDivisors R (C.homology n)) :
    ∀ (a : R), a ≠ 0 → ∀ x : cycles C n, a • x ∈ boundaries C n → x ∈ boundaries C n := by
  letI := htf
  intro a ha x hx
  let q : (cycles C n) ⧸ boundaries C n := Submodule.Quotient.mk x
  have hq : a • q = 0 := by
    change (Submodule.Quotient.mk (a • x) : (cycles C n) ⧸ boundaries C n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have heq : a • (homologyEquiv C n q) = 0 := by
    rw [← map_smul, hq, map_zero]
  have hezero : homologyEquiv C n q = 0 :=
    (smul_eq_zero.mp heq).resolve_left ha
  exact (Submodule.Quotient.mk_eq_zero _).mp
    ((homologyEquiv C n).injective (hezero.trans (map_zero (homologyEquiv C n)).symm))

theorem scalar_isUnit (n : ℤ) (htf : NoZeroSMulDivisors R (C.homology n))
    (i : Fin (boundaryRank C n)) : IsUnit (IntegralSmithScalarIso.scalar C n i) := by
  let s := smith C n
  have sne : s.a i ≠ 0 := by
    intro h
    have hh := s.snf i
    rw [h,zero_smul] at hh
    exact s.bN.ne_zero i (Subtype.ext hh)
  have hm : s.bM (s.f i) ∈ boundaries C n :=
    saturated C n htf (s.a i) sne _ (by rw [← s.snf]; exact (s.bN i).property)
  have h := s.repr_apply_embedding_eq_repr_smul (⟨s.bM (s.f i),hm⟩ : boundaries C n) (i := i)
  have heq : 1 = s.a i * s.bN.repr (⟨s.bM (s.f i),hm⟩ : boundaries C n) i := by
    simpa only [s.bM.repr_self,Finsupp.single_eq_same,map_smul,Finsupp.smul_apply,smul_eq_mul] using h
  exact isUnit_iff_dvd_one.mpr ⟨_,heq⟩

#print axioms boundary_eq
#print axioms homologyEquiv
#print axioms saturated
#print axioms scalar_isUnit
end Verification.SmithHomologyUnits
