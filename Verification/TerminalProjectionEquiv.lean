/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Terminal Projection Equiv

An explicit first-boundary cokernel-to-survivor isomorphism. Its value
on a quotient representative is the literal normalized projection, enabling
weight calculations on the actual survivor basis.
-/

namespace Verification.TerminalProjectionEquiv

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable (D : N →ₗ[R] M) (H : M →ₗ[R] N)
variable (h : D.comp (H.comp D)=D)

def projector : Module.End R M := LinearMap.id-D.comp H

include h in
theorem projector_boundary : (projector D H).comp D=0 := by
  ext x
  have hh := LinearMap.congr_fun h x
  change D (H (D x))=D x at hh
  change D x-D (H (D x))=0
  rw [hh,sub_self]

include h in
theorem projector_square : (projector D H).comp (projector D H)=projector D H := by
  ext x
  change projector D H (x-D (H x))=projector D H x
  rw [map_sub]
  have hh := LinearMap.congr_fun (projector_boundary D H h) (H x)
  change projector D H (D (H x))=0 at hh
  rw [hh,sub_zero]

def fixed : Submodule R M := LinearMap.ker (projector D H-LinearMap.id)

theorem fixed_property (x : fixed D H) : projector D H x.val=x.val := sub_eq_zero.mp x.property

def project : M →ₗ[R] fixed D H where
  toFun x := ⟨projector D H x,by
    change projector D H (projector D H x)-projector D H x=0
    exact sub_eq_zero.mpr (LinearMap.congr_fun (projector_square D H h) x)⟩
  map_add' x y := by apply Subtype.ext;exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext;exact map_smul _ _ _

theorem project_surjective : Function.Surjective (project D H h) := by
  intro x
  exact ⟨x.val,Subtype.ext (fixed_property D H x)⟩

theorem project_kernel : LinearMap.ker (project D H h)=LinearMap.range D := by
  ext x
  constructor
  · intro hx
    have hh : projector D H x=0 := congrArg Subtype.val hx
    change x-D (H x)=0 at hh
    exact ⟨H x,(sub_eq_zero.mp hh).symm⟩
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun (projector_boundary D H h) y

noncomputable def quotientEquiv : (M ⧸ LinearMap.range D) ≃ₗ[R] fixed D H :=
  (Submodule.quotEquivOfEq _ _ (project_kernel D H h).symm).trans
    ((project D H h).quotKerEquivOfSurjective (project_surjective D H h))

theorem quotientEquiv_mk (x : M) :
    (quotientEquiv D H h ((LinearMap.range D).mkQ x)).val=projector D H x := rfl

#print axioms projector
#print axioms projector_boundary
#print axioms projector_square
#print axioms fixed
#print axioms fixed_property
#print axioms project
#print axioms project_surjective
#print axioms project_kernel
#print axioms quotientEquiv
#print axioms quotientEquiv_mk

end Verification.TerminalProjectionEquiv
