/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Boundary Cokernel Transport

Literal cokernel transport under independently specified source and target
coordinate equivalences, with the differential equality checked explicitly.
-/

namespace Verification.BoundaryCokernelTransport

variable {R C M A B : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

theorem range_coordinates (D : C →ₗ[R] M) (d : A →ₗ[R] B)
    (F : C ≃ₗ[R] A) (E : M ≃ₗ[R] B)
    (h : E.toLinearMap.comp (D.comp F.symm.toLinearMap)=d) :
    (LinearMap.range D).map E.toLinearMap=LinearMap.range d := by
  ext b
  constructor
  · rintro ⟨m,⟨c,rfl⟩,hm⟩
    refine ⟨F c,?_⟩
    have hh := LinearMap.congr_fun h (F c)
    simp only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
    exact hh.symm.trans hm
  · rintro ⟨a,rfl⟩
    refine ⟨D (F.symm a),⟨F.symm a,rfl⟩,?_⟩
    exact LinearMap.congr_fun h a

noncomputable def cokernelEquiv (D : C →ₗ[R] M) (d : A →ₗ[R] B)
    (F : C ≃ₗ[R] A) (E : M ≃ₗ[R] B)
    (h : E.toLinearMap.comp (D.comp F.symm.toLinearMap)=d) :
    (M ⧸ LinearMap.range D) ≃ₗ[R] (B ⧸ LinearMap.range d) :=
  Submodule.Quotient.equiv _ _ E (range_coordinates D d F E h)

#print axioms range_coordinates
#print axioms cokernelEquiv

end Verification.BoundaryCokernelTransport
