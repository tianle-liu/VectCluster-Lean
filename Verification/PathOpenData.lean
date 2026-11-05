/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointClosedData

/-!
# Path Open Data

A surjective restriction with its literal closed-support kernel packages
an actual open quotient and the differential induced on it.
-/

namespace Verification.PathOpenData

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure OpenData (D : M →ₗ[R] M) (E : N →ₗ[R] N) (C : Submodule R M) where
  map : M →ₗ[R] N
  surjective : Function.Surjective map
  kernel_iff : ∀ x, map x=0 ↔ x ∈ C
  intertwining : map.comp D=E.comp map

namespace OpenData
variable {D : M →ₗ[R] M} {E : N →ₗ[R] N} {C : Submodule R M}

theorem ker_eq (h : OpenData D E C) : LinearMap.ker h.map=C := by
  ext x
  exact h.kernel_iff x

noncomputable def quotientEquiv (h : OpenData D E C) : (M ⧸ C) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ h.ker_eq.symm).trans
    (LinearMap.quotKerEquivOfSurjective h.map h.surjective)

theorem preserved (h : OpenData D E C) : C ≤ C.comap D := by
  intro x hx
  apply (h.kernel_iff (D x)).mp
  have hh := LinearMap.congr_fun h.intertwining x
  simp only [LinearMap.comp_apply] at hh
  rw [hh,(h.kernel_iff x).mpr hx,map_zero]

noncomputable def quotientDifferential (h : OpenData D E C) : (M ⧸ C) →ₗ[R] (M ⧸ C) :=
  C.mapQ C D h.preserved

theorem quotient_intertwining (h : OpenData D E C) :
    h.quotientEquiv.toLinearMap.comp h.quotientDifferential=
      E.comp h.quotientEquiv.toLinearMap := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun h.intertwining x

end OpenData

#print axioms OpenData
#print axioms OpenData.ker_eq
#print axioms OpenData.quotientEquiv
#print axioms OpenData.preserved
#print axioms OpenData.quotientDifferential
#print axioms OpenData.quotient_intertwining

end Verification.PathOpenData
