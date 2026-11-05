/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestComponentMatrix

/-!
# Path Forest Quotient

The actual integral mutable-row quotient of a linearly oriented path
forest is one copy of Z for each odd component. The quotient coordinates
and the endpoint section are explicit, including empty/even components.
-/

noncomputable section
namespace Verification.PathForestQuotient
open Classical Verification.PathForestMatching Verification.PathForestFullRank
  Verification.PathForestComponentMatrix

def localPairing (m : ℕ) (o : Bool) :
    ((largeIndex m o → ℤ) × (Fin m → ℤ)) →ₗ[ℤ] ℤ :=
  match o with
  | false => 0
  | true => PathLattice.oddPairing m

theorem local_image (m : ℕ) (o : Bool) (x : (largeIndex m o → ℤ) × (Fin m → ℤ)) :
    x ∈ LinearMap.range (localPrincipal m o) ↔ (o=true → localPairing m o x=0) := by
  cases o with
  | false =>
    constructor
    · intro _ h;cases h
    · intro _;exact PathLattice.evenOperator_surjective m x
  | true => simpa [localPairing,localPrincipal] using PathLattice.odd_image_iff m x

def localEndpoint (m : ℕ) (o : Bool) :
    ℤ →ₗ[ℤ] ((largeIndex m o → ℤ) × (Fin m → ℤ)) :=
  match o with
  | false => 0
  | true => (LinearMap.single ℤ (fun _ : Fin (m+1)=>ℤ) ⟨0,by omega⟩).prod 0

theorem endpoint_pairing (m : ℕ) (o : Bool) (z : ℤ) :
    localPairing m o (localEndpoint m o z)=if o then z else 0 := by
  cases o with
  | false => rfl
  | true =>
    change (∑ i : Fin (m+1),(Pi.single (⟨0,by omega⟩ : Fin (m+1)) z : Fin (m+1) → ℤ) i)=z
    simp

variable {S : Type} [Fintype S] (m : S → ℕ) (o : S → Bool)
abbrev Odd := {s : S // o s=true}

def quotientMap : (Vertices m o → ℤ) →ₗ[ℤ] (Odd o → ℤ) where
  toFun x s := localPairing (m s.val) (o s.val) (components m o x s.val)
  map_add' x y := by funext s;simp only [map_add,Pi.add_apply]
  map_smul' a x := by funext s;simp only [map_smul,Pi.smul_apply,RingHom.id_apply]

def oddValue : (Odd o → ℤ) →ₗ[ℤ] (S → ℤ) where
  toFun x s := if h : o s=true then x ⟨s,h⟩ else 0
  map_add' x y := by funext s;by_cases h : o s=true <;> simp [h]
  map_smul' a x := by funext s;by_cases h : o s=true <;> simp [h]

def endpoint : (Odd o → ℤ) →ₗ[ℤ] (Vertices m o → ℤ) :=
  (components m o).symm.toLinearMap.comp (LinearMap.pi (fun s=>
    (localEndpoint (m s) (o s)).comp ((LinearMap.proj s).comp (oddValue o))))

omit [Fintype S] in
theorem endpoint_right : (quotientMap m o).comp (endpoint m o)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext s
  change localPairing (m s.val) (o s.val)
    (components m o ((components m o).symm (fun t=>localEndpoint (m t) (o t) (oddValue o x t))) s.val)=x s
  rw [LinearEquiv.apply_symm_apply,endpoint_pairing]
  simp [oddValue,s.property]

omit [Fintype S] in
theorem quotient_surjective : Function.Surjective (quotientMap m o) := by
  intro x
  exact ⟨endpoint m o x,LinearMap.congr_fun (endpoint_right m o) x⟩

theorem image_eq_kernel : LinearMap.range (ordinaryMatrix m o).mulVecLin=LinearMap.ker (quotientMap m o) := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y,rfl⟩
    change quotientMap m o ((ordinaryMatrix m o).mulVec y)=0
    funext s
    change localPairing (m s.val) (o s.val) (components m o ((ordinaryMatrix m o).mulVec y) s.val)=0
    rw [principal_component]
    exact (local_image _ _ _).mp ⟨components m o y s.val,rfl⟩ s.property
  · intro hx
    have hx' : quotientMap m o x=0 := hx
    have hl (s : S) : components m o x s ∈ LinearMap.range (localPrincipal (m s) (o s)) := by
      apply (local_image _ _ _).mpr
      intro hs
      exact congrFun hx' ⟨s,hs⟩
    refine ⟨(components m o).symm (fun s=>(hl s).choose),?_⟩
    apply (components m o).injective
    funext s
    change components m o ((ordinaryMatrix m o).mulVec ((components m o).symm (fun s=>(hl s).choose))) s=_
    rw [principal_component,LinearEquiv.apply_symm_apply]
    exact (hl s).choose_spec

theorem transpose_eq_neg : (ordinaryMatrix m o).transpose= -ordinaryMatrix m o := by
  ext i j
  cases i <;> cases j <;> simp [ordinaryMatrix,principal,Matrix.fromBlocks,Matrix.transpose_apply]

theorem rows_eq_kernel : LinearMap.range (ordinaryMatrix m o).transpose.mulVecLin=LinearMap.ker (quotientMap m o) := by
  have he : (ordinaryMatrix m o).transpose.mulVecLin= -(ordinaryMatrix m o).mulVecLin := by
    apply LinearMap.ext
    intro x
    change (ordinaryMatrix m o).transpose.mulVec x= -((ordinaryMatrix m o).mulVec x)
    rw [transpose_eq_neg,Matrix.neg_mulVec]
  rw [he,LinearMap.range_neg,image_eq_kernel]

theorem quotient_rows_zero : (quotientMap m o).comp (ordinaryMatrix m o).transpose.mulVecLin=0 := by
  apply LinearMap.ext
  intro x
  have h : (ordinaryMatrix m o).transpose.mulVecLin x ∈ LinearMap.ker (quotientMap m o) := by
    rw [← rows_eq_kernel]
    exact ⟨x,rfl⟩
  exact h

def rowQuotientEquiv : ((Vertices m o → ℤ) ⧸ LinearMap.range (ordinaryMatrix m o).transpose.mulVecLin) ≃ₗ[ℤ]
    (Odd o → ℤ) :=
  (Submodule.quotEquivOfEq _ _ (rows_eq_kernel m o)).trans
    (LinearMap.quotKerEquivOfSurjective (quotientMap m o) (quotient_surjective m o))

#print axioms localPairing
#print axioms local_image
#print axioms localEndpoint
#print axioms endpoint_pairing
#print axioms Odd
#print axioms quotientMap
#print axioms oddValue
#print axioms endpoint
#print axioms endpoint_right
#print axioms quotient_surjective
#print axioms image_eq_kernel
#print axioms transpose_eq_neg
#print axioms rows_eq_kernel
#print axioms quotient_rows_zero
#print axioms rowQuotientEquiv
end Verification.PathForestQuotient
