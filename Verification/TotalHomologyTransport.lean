/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedHomologyTF

/-!
# Total Homology Transport

Explicit boundary-preimage transport along a split map of actual differential
modules. The result is TF of the literal kernel/image quotient.
-/

namespace Verification.TotalHomologyTransport

open Verification.GradedHomologyTF

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A differential-module retract inherits TF homology by transporting actual boundaries. -/
theorem total_tf_of_retract (D : Module.End R M) (E : Module.End R N)
    (i : M →ₗ[R] N) (r : N →ₗ[R] M)
    (hi : i.comp D=E.comp i) (hr : r.comp E=D.comp r) (hri : r.comp i=LinearMap.id)
    (htf : NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology E)) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology D) := by
  apply (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles D)).mpr
  intro a ha x hx
  obtain ⟨y,hy⟩ := hx
  have hy' : D y=a • x.val := hy
  have hiD (z : M) : i (D z)=E (i z) := LinearMap.congr_fun hi z
  have hrE (z : N) : r (E z)=D (r z) := LinearMap.congr_fun hr z
  have hri' (z : M) : r (i z)=z := LinearMap.congr_fun hri z
  have hz : E (i x.val)=0 := by rw [←hiD,x.property,map_zero]
  let z : LinearMap.ker E := ⟨i x.val,hz⟩
  have haz : a • z ∈ Verification.IntegralSplitting.boundaryCycles E := by
    refine ⟨i y,?_⟩
    change E (i y)=a • i x.val
    rw [←hiD,hy',map_smul]
  obtain ⟨w,hw⟩ := (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles E)).mp
    htf a ha z haz
  have hw' : E w=i x.val := hw
  refine ⟨r w,?_⟩
  change D (r w)=x.val
  rw [←hrE,hw',hri']

#print axioms total_tf_of_retract

end Verification.TotalHomologyTransport
