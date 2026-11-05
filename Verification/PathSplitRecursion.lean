/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

/-!
# Path Split Recursion

Explicit block coordinates for a split actual open/closed recursion.
The connecting operator is computed from the original differential and section.
-/

namespace Verification.PathSplitRecursion

variable {R C M O : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
variable [AddCommGroup O] [Module R O]

variable (E : C →ₗ[R] M) (Q : M →ₗ[R] O) (S : O →ₗ[R] M)
variable (hE : Function.Injective E) (hEQ : LinearMap.range E=LinearMap.ker Q)
variable (hQS : Q.comp S=LinearMap.id)

include hEQ in
theorem open_closed (x : C) : Q (E x)=0 := by
  change E x ∈ LinearMap.ker Q
  rw [← hEQ]
  exact ⟨x,rfl⟩

noncomputable def closedRetraction : M →ₗ[R] C :=
  (LinearEquiv.ofInjective E hE).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range E) (LinearMap.id-S.comp Q) (fun x => by
      rw [hEQ]
      change Q (x-S (Q x))=0
      have hh := LinearMap.congr_fun hQS (Q x)
      simp only [LinearMap.comp_apply,LinearMap.id_apply] at hh
      rw [map_sub,hh,sub_self]))

theorem closedRetraction_image (x : M) :
    E (closedRetraction E Q S hE hEQ hQS x)=x-S (Q x) := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective E hE).apply_symm_apply
    (⟨x-S (Q x),by
      rw [hEQ]
      change Q (x-S (Q x))=0
      have hh := LinearMap.congr_fun hQS (Q x)
      simp only [LinearMap.comp_apply,LinearMap.id_apply] at hh
      rw [map_sub,hh,sub_self]⟩ : LinearMap.range E))

theorem closedRetraction_closed (x : C) : closedRetraction E Q S hE hEQ hQS (E x)=x := by
  apply hE
  rw [closedRetraction_image,open_closed E Q hEQ,map_zero,sub_zero]

theorem closedRetraction_section (x : O) : closedRetraction E Q S hE hEQ hQS (S x)=0 := by
  apply hE
  have hh := LinearMap.congr_fun hQS x
  simp only [LinearMap.comp_apply,LinearMap.id_apply] at hh
  rw [closedRetraction_image,hh,sub_self,map_zero]

noncomputable def coordinates : M ≃ₗ[R] C × O where
  toFun x := (closedRetraction E Q S hE hEQ hQS x,Q x)
  invFun x := E x.1+S x.2
  left_inv x := by
    change E (closedRetraction E Q S hE hEQ hQS x)+S (Q x)=x
    rw [closedRetraction_image,sub_add_cancel]
  right_inv x := by
    apply Prod.ext
    · change closedRetraction E Q S hE hEQ hQS (E x.1+S x.2)=x.1
      rw [map_add,closedRetraction_closed,closedRetraction_section,add_zero]
    · change Q (E x.1+S x.2)=x.2
      rw [map_add,open_closed E Q hEQ,zero_add]
      exact LinearMap.congr_fun hQS x.2
  map_add' x y := by simp only [map_add,Prod.mk_add_mk]
  map_smul' r x := by simp only [map_smul,Prod.smul_mk,RingHom.id_apply]

variable (D : M →ₗ[R] M) (DC : C →ₗ[R] C) (DO : O →ₗ[R] O)
variable (hDE : D.comp E=E.comp DC) (hQD : Q.comp D=DO.comp Q)

noncomputable def connecting : O →ₗ[R] C :=
  (closedRetraction E Q S hE hEQ hQS).comp (D.comp S)

noncomputable def blockDifferential : (C × O) →ₗ[R] (C × O) :=
  ((DC.comp (LinearMap.fst R C O))+
    (connecting E Q S hE hEQ hQS D).comp (LinearMap.snd R C O)).prod
      (DO.comp (LinearMap.snd R C O))

include hDE hQD in
theorem coordinates_differential :
    (coordinates E Q S hE hEQ hQS).toLinearMap.comp D=
      (blockDifferential E Q S hE hEQ hQS D DC DO).comp (coordinates E Q S hE hEQ hQS).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change closedRetraction E Q S hE hEQ hQS (D x)=
      DC (closedRetraction E Q S hE hEQ hQS x)+closedRetraction E Q S hE hEQ hQS (D (S (Q x)))
    have hd := LinearMap.congr_fun hDE (closedRetraction E Q S hE hEQ hQS x)
    simp only [LinearMap.comp_apply] at hd
    have he : x=E (closedRetraction E Q S hE hEQ hQS x)+S (Q x) := by
      rw [closedRetraction_image,sub_add_cancel]
    conv_lhs => rw [he]
    rw [map_add,map_add,hd,closedRetraction_closed]
  · exact LinearMap.congr_fun hQD x

#print axioms open_closed
#print axioms closedRetraction
#print axioms closedRetraction_image
#print axioms closedRetraction_closed
#print axioms closedRetraction_section
#print axioms coordinates
#print axioms connecting
#print axioms blockDifferential
#print axioms coordinates_differential

end Verification.PathSplitRecursion
