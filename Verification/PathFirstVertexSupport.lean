/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFullComplex

/-!
# Path First Vertex Support

Exact first-vertex block support of the actual full-rho path differential.
-/

namespace Verification.PathFirstVertexSupport

open Classical Verification.PathCochains Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathStratumGrading

variable {R : Type*} [CommRing R]

theorem zMatrix_incidence (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : ∀ j ∈ y.1.val, eraseConfig y.1 j ≠ x.1) : zMatrix g ρ n y x=0 := by
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply,zDifferential_stratum_zero g ρ n _ y.1]
  · rfl
  · intro j hj
    exact zCoefficients_inverse_stratum ρ n x _ (h j hj)

theorem yMatrix_incidence (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : ∀ j ∈ y.1.val, eraseConfig y.1 j ≠ x.1) : yMatrix g ρ a y x=0 := by
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply,yDifferential_stratum_zero g ρ a _ y.1]
  · rfl
  · intro j hj
    exact yCoefficients_inverse_stratum ρ a x _ (h j hj)

theorem erase_ne_of_first {n : ℕ} (J I : Config n) (hJ : 1 ∉ J.val) (hI : 1 ∈ I.val)
    (j : ℕ) : eraseConfig J j ≠ I := by
  intro h
  have he : J.val.erase j=I.val := congrArg Subtype.val h
  apply hJ
  exact Finset.mem_of_mem_erase (he.symm ▸ hI)

/-- The closed subcomplex has no cochain differential into the open part. -/
theorem zMatrix_first (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (hy : 1 ∉ y.1.val) (hx : 1 ∈ x.1.val) : zMatrix g ρ n y x=0 :=
  zMatrix_incidence g ρ n y x (fun j _ => erase_ne_of_first y.1 x.1 hy hx j)

theorem yMatrix_first (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (hy : 1 ∉ y.1.val) (hx : 1 ∈ x.1.val) : yMatrix g ρ a y x=0 :=
  yMatrix_incidence g ρ a y x (fun j _ => erase_ne_of_first y.1 x.1 hy hx j)

abbrev OpenIndex (B : List Bool → Prop) (n : ℕ) := {x : NormalIndex B n // 1 ∉ x.1.val}
abbrev ClosedIndex (B : List Bool → Prop) (n : ℕ) := {x : NormalIndex B n // 1 ∈ x.1.val}

/-- This partition uses the actual first zero vertex, retaining every word. -/
noncomputable def indexEquiv (B : List Bool → Prop) (n : ℕ) :
    OpenIndex B n ⊕ ClosedIndex B n ≃ NormalIndex B n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if h : 1 ∈ x.1.val then Sum.inr ⟨x,h⟩ else Sum.inl ⟨x,h⟩
  left_inv x := by cases x with
    | inl x => simp only [Sum.elim_inl,x.property,↓reduceDIte]
    | inr x => simp only [Sum.elim_inr,x.property,↓reduceDIte]
  right_inv x := by dsimp; split <;> rfl

noncomputable instance openFintype (B : List Bool → Prop) (n : ℕ) : Fintype (OpenIndex B n) :=
  Fintype.ofFinite _

noncomputable instance closedFintype (B : List Bool → Prop) (n : ℕ) : Fintype (ClosedIndex B n) :=
  Fintype.ofFinite _

#print axioms zMatrix_incidence
#print axioms yMatrix_incidence
#print axioms erase_ne_of_first
#print axioms zMatrix_first
#print axioms yMatrix_first
#print axioms OpenIndex
#print axioms ClosedIndex
#print axioms indexEquiv
#print axioms openFintype
#print axioms closedFintype

end Verification.PathFirstVertexSupport
