/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Integral Splitting

Integral splitting of an actual finite free differential module.  Torsion-free
homology is the input; sections and contractions are constructed using the PID
and projective-module theorems, rather than assumed as cancellation data.
-/

namespace Verification.IntegralSplitting

section SplitSurjection

variable {R M N : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjection with a chosen section splits into its literal kernel and target. -/
def splitEquiv (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) :
    M ≃ₗ[R] (LinearMap.ker f) × N where
  toFun x := (⟨x-s (f x), by
    change f (x-s (f x)) = 0
    have hx : f (s (f x)) = f x := LinearMap.congr_fun hs (f x)
    rw [map_sub, hx, sub_self]⟩, f x)
  invFun z := z.1.val+s z.2
  left_inv x := by simp
  right_inv z := by
    rcases z with ⟨x,y⟩
    have hx : f x.val = 0 := x.property
    have hsy : f (s y) = y := LinearMap.congr_fun hs y
    apply Prod.ext
    · apply Subtype.ext
      simp [hx,hsy]
    · simp [hx,hsy]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp [map_add]
      abel
    · exact map_add f x y
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      simp [map_smul, smul_sub]
    · exact map_smul f a x

end SplitSurjection

section Integral

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]
variable (U : M →ₗ[R] M)

/-- Boundaries regarded as a submodule of actual cycles. -/
def boundaryCycles : Submodule R (LinearMap.ker U) :=
  (LinearMap.range U).comap (LinearMap.ker U).subtype

/-- The literal integral homology quotient. -/
abbrev Homology := (LinearMap.ker U) ⧸ boundaryCycles U

variable (hU : U.comp U = 0)

omit [Module.Free R M] [Module.Finite R M] [IsDomain R] [IsPrincipalIdealRing R] in
include hU in
theorem boundaries_are_cycles : LinearMap.range U ≤ LinearMap.ker U :=
  LinearMap.range_le_ker_iff.mpr hU

/-- Under d²=0 the boundary submodule inside cycles is the actual image module. -/
def boundaryEquiv : boundaryCycles U ≃ₗ[R] LinearMap.range U :=
  Submodule.comapSubtypeEquivOfLe (boundaries_are_cycles U hU)

/-- The first section exists because a submodule of a finite free Z-module is free. -/
noncomputable def boundarySection : LinearMap.range U →ₗ[R] M :=
  Classical.choose (U.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict U))

theorem boundarySection_rightInverse : U.rangeRestrict.comp (boundarySection U) = LinearMap.id :=
  Classical.choose_spec (U.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict U))

variable [NoZeroSMulDivisors R (Homology U)]

omit [Module.Free R M] in
/-- TF homology is actually free of finite rank over Z. -/
theorem homology_free : Module.Free R (Homology U) := inferInstance

/-- The second section is constructed from the actual TF homology quotient. -/
noncomputable def homologySection : Homology U →ₗ[R] LinearMap.ker U :=
  Classical.choose ((boundaryCycles U).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _))

omit [Module.Free R M] in
theorem homologySection_rightInverse : (boundaryCycles U).mkQ.comp (homologySection U) = LinearMap.id :=
  Classical.choose_spec ((boundaryCycles U).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _))

/-- Cycles are split into actual boundaries and actual homology. -/
noncomputable def cycleEquiv : LinearMap.ker U ≃ₗ[R] (LinearMap.range U) × Homology U :=
  (splitEquiv (boundaryCycles U).mkQ (homologySection U) (homologySection_rightInverse U)).trans
    (LinearEquiv.prodCongr
      ((LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _)).trans (boundaryEquiv U hU))
      (LinearEquiv.refl R (Homology U)))

/-- The complete decomposition is constructed from the two split exact sequences. -/
noncomputable def decomposition : M ≃ₗ[R] ((LinearMap.range U) × Homology U) × LinearMap.range U :=
  (splitEquiv U.rangeRestrict (boundarySection U) (boundarySection_rightInverse U)).trans
    (LinearEquiv.prodCongr
      ((LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict U)).trans (cycleEquiv U hU))
      (LinearEquiv.refl R (LinearMap.range U)))

omit [Module.Free R M] in
/-- Boundaries have their literal boundary coordinate and zero homology coordinate. -/
theorem cycleEquiv_boundary (x : LinearMap.range U) :
    cycleEquiv U hU ⟨x.val, boundaries_are_cycles U hU x.property⟩ = (x,0) := by
  have hx : (⟨x.val, boundaries_are_cycles U hU x.property⟩ : LinearMap.ker U) ∈ boundaryCycles U := x.property
  have hq : (boundaryCycles U).mkQ ⟨x.val, boundaries_are_cycles U hU x.property⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  apply Prod.ext
  · apply Subtype.ext
    change x.val - (homologySection U ((boundaryCycles U).mkQ
      ⟨x.val, boundaries_are_cycles U hU x.property⟩)).val = x.val
    rw [hq, map_zero]
    simp
  · simpa [cycleEquiv, splitEquiv] using hq

/-- In these constructed coordinates the differential consists of unit pairs only. -/
theorem decomposition_differential (x : M) :
    decomposition U hU (U x) = ((U.rangeRestrict x, 0), 0) := by
  have huu : U (U x) = 0 := LinearMap.congr_fun hU x
  have hr : U.rangeRestrict (U x) = 0 := by apply Subtype.ext; exact huu
  change (cycleEquiv U hU
    ((LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict U))
      ⟨U x-boundarySection U (U.rangeRestrict (U x)), _⟩), U.rangeRestrict (U x)) = _
  simp only [hr, map_zero, sub_zero]
  apply Prod.ext
  · exact cycleEquiv_boundary U hU (U.rangeRestrict x)
  · rfl


/-- The last coordinate is the actual outgoing boundary. -/
theorem decomposition_last (x : M) : (decomposition U hU x).2 = U.rangeRestrict x := rfl

/-- Literal normal form of the differential under the constructed decomposition. -/
theorem decomposition_differential_normal (x : M) :
    decomposition U hU (U x) = (((decomposition U hU x).2,0),0) := by
  rw [decomposition_differential, decomposition_last]

/-- The reverse of the unit-pair differential in the constructed coordinates. -/
def standardHomotopy : ((LinearMap.range U × Homology U) × LinearMap.range U) →ₗ[R]
    ((LinearMap.range U × Homology U) × LinearMap.range U) where
  toFun x := ((0,0),x.1.1)
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The integral contraction is constructed, not supplied as an assumption. -/
noncomputable def contraction : M →ₗ[R] M :=
  (decomposition U hU).symm.toLinearMap.comp
    ((standardHomotopy U).comp (decomposition U hU).toLinearMap)

theorem decomposition_contraction (x : M) :
    decomposition U hU (contraction U hU x) = ((0,0),(decomposition U hU x).1.1) := by
  change (decomposition U hU) ((decomposition U hU).symm ((0,0),(decomposition U hU x).1.1)) = _
  exact (decomposition U hU).apply_symm_apply _

/-- The derived contraction is square-zero. -/
theorem contraction_square : (contraction U hU).comp (contraction U hU) = 0 := by
  apply LinearMap.ext
  intro x
  apply (decomposition U hU).injective
  change decomposition U hU (contraction U hU (contraction U hU x)) = decomposition U hU 0
  rw [decomposition_contraction, decomposition_contraction, map_zero]
  rfl

/-- All of the pure differential is covered by the derived unit pairs. -/
theorem differential_contraction_differential : U.comp ((contraction U hU).comp U) = U := by
  apply LinearMap.ext
  intro x
  apply (decomposition U hU).injective
  change decomposition U hU (U (contraction U hU (U x))) = decomposition U hU (U x)
  simp only [decomposition_differential_normal, decomposition_contraction]

/-- The derived contraction is normalized on those pairs. -/
theorem contraction_differential_contraction :
    (contraction U hU).comp (U.comp (contraction U hU)) = contraction U hU := by
  apply LinearMap.ext
  intro x
  apply (decomposition U hU).injective
  change decomposition U hU (contraction U hU (U (contraction U hU x))) =
    decomposition U hU (contraction U hU x)
  simp only [decomposition_differential_normal, decomposition_contraction]

/-- Actual projection onto the literal homology quotient. -/
noncomputable def homologyProjection : M →ₗ[R] Homology U :=
  ((LinearMap.snd R (LinearMap.range U) (Homology U)).comp
    (LinearMap.fst R ((LinearMap.range U) × Homology U) (LinearMap.range U))).comp
    (decomposition U hU).toLinearMap

/-- Representatives of homology are constructed by the same two sections. -/
noncomputable def homologyInclusion : Homology U →ₗ[R] M :=
  (decomposition U hU).symm.toLinearMap.comp
    ((LinearMap.inr R (LinearMap.range U) (Homology U)).prod 0)

theorem homologyProjection_inclusion :
    (homologyProjection U hU).comp (homologyInclusion U hU) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change ((decomposition U hU) ((decomposition U hU).symm ((0,x),0))).1.2 = x
  rw [LinearEquiv.apply_symm_apply]

theorem homologyInclusion_projection :
    (homologyInclusion U hU).comp (homologyProjection U hU) =
      LinearMap.id-U.comp (contraction U hU)-(contraction U hU).comp U := by
  apply LinearMap.ext
  intro x
  apply (decomposition U hU).injective
  change (decomposition U hU) ((decomposition U hU).symm ((0,(decomposition U hU x).1.2),0)) =
    decomposition U hU (x-U (contraction U hU x)-contraction U hU (U x))
  rw [LinearEquiv.apply_symm_apply, map_sub, map_sub]
  simp only [decomposition_differential_normal, decomposition_contraction]
  apply Prod.ext
  · apply Prod.ext <;> simp
  · simp

/-- The pure-homology survivor projection is the actual `1-UH-HU`. -/
noncomputable def survivorProjection : M →ₗ[R] M :=
  LinearMap.id-U.comp (contraction U hU)-(contraction U hU).comp U

/-- Its image as an actual fixed-point module. -/
noncomputable def survivorModule : Submodule R M :=
  LinearMap.ker (survivorProjection U hU-LinearMap.id)

/-- The actual fixed-point module is linearly equivalent to the actual homology quotient. -/
noncomputable def survivorEquiv : Homology U ≃ₗ[R] survivorModule U hU where
  toFun x := ⟨homologyInclusion U hU x, by
    change survivorProjection U hU (homologyInclusion U hU x)-homologyInclusion U hU x = 0
    change (LinearMap.id-U.comp (contraction U hU)-(contraction U hU).comp U : M →ₗ[R] M)
      (homologyInclusion U hU x)-homologyInclusion U hU x = 0
    rw [← homologyInclusion_projection]
    change homologyInclusion U hU (homologyProjection U hU (homologyInclusion U hU x))-
      homologyInclusion U hU x = 0
    have hx := LinearMap.congr_fun (homologyProjection_inclusion U hU) x
    change homologyProjection U hU (homologyInclusion U hU x) = x at hx
    rw [hx, sub_self]⟩
  invFun x := homologyProjection U hU x.val
  left_inv x := LinearMap.congr_fun (homologyProjection_inclusion U hU) x
  right_inv x := by
    apply Subtype.ext
    have hx : survivorProjection U hU x.val-x.val = 0 := x.property
    rw [← sub_eq_zero]
    change ((homologyInclusion U hU).comp (homologyProjection U hU)) x.val-x.val = 0
    rw [homologyInclusion_projection]
    exact hx
  map_add' x y := by apply Subtype.ext; exact map_add (homologyInclusion U hU) x y
  map_smul' a x := by apply Subtype.ext; exact map_smul (homologyInclusion U hU) a x

/-- An actual finite basis of pure homology, obtained from TF over the PID. -/
noncomputable def homologyBasis : Basis (Fin (Module.finrank R (Homology U))) R (Homology U) :=
  Module.finBasis R (Homology U)

/-- Transporting that basis gives a finite basis of the actual surviving module. -/
noncomputable def survivorBasis : Basis (Fin (Module.finrank R (Homology U))) R (survivorModule U hU) :=
  (homologyBasis U).map (survivorEquiv U hU)

end Integral

#print axioms splitEquiv
#print axioms boundaryCycles
#print axioms boundaries_are_cycles
#print axioms boundaryEquiv
#print axioms boundarySection
#print axioms boundarySection_rightInverse
#print axioms homology_free
#print axioms homologySection
#print axioms homologySection_rightInverse
#print axioms cycleEquiv
#print axioms decomposition
#print axioms cycleEquiv_boundary
#print axioms decomposition_differential

#print axioms decomposition_last
#print axioms decomposition_differential_normal
#print axioms standardHomotopy
#print axioms contraction
#print axioms decomposition_contraction
#print axioms contraction_square
#print axioms differential_contraction_differential
#print axioms contraction_differential_contraction
#print axioms homologyProjection
#print axioms homologyInclusion
#print axioms homologyProjection_inclusion
#print axioms homologyInclusion_projection
#print axioms survivorProjection
#print axioms survivorModule
#print axioms survivorEquiv
#print axioms homologyBasis
#print axioms survivorBasis

end Verification.IntegralSplitting

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.IntegralSplitting.Homology
