/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralSplitting
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Smith Chain Block

A Smith normal form for an actual map of finite free PID modules, together
with separation of every nonzero Smith pair from both adjacent differentials.
All bases and sections are constructed from the map. No chain decomposition
or diagonalization of the whole complex is an input.
-/

noncomputable section
namespace Verification.SmithChainBlock

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
variable (d : M →ₗ[R] N)

/-- The image is projective because it is a submodule of a finite free PID module. -/
def imageSection : LinearMap.range d →ₗ[R] M :=
  Classical.choose (d.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict d))

omit [Module.Free R M] [Module.Finite R N] in
theorem imageSection_rightInverse :
    d.rangeRestrict.comp (imageSection d) = LinearMap.id :=
  Classical.choose_spec (d.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict d))

/-- Literal kernel/image coordinates in the source, constructed using a section. -/
def sourceSplit : M ≃ₗ[R] LinearMap.ker d × LinearMap.range d :=
  (IntegralSplitting.splitEquiv d.rangeRestrict (imageSection d)
    (imageSection_rightInverse d)).trans
    (LinearEquiv.prodCongr
      (LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict d))
      (LinearEquiv.refl R _))

omit [Module.Free R M] [Module.Finite R N] in
theorem sourceSplit_last (x : M) : (sourceSplit d x).2 = d.rangeRestrict x := rfl

omit [Module.Free R M] [Module.Finite R N] in
theorem sourceSplit_symm_d (z : LinearMap.ker d × LinearMap.range d) :
    d ((sourceSplit d).symm z) = z.2.val := by
  have h := congrArg (fun w : LinearMap.ker d × LinearMap.range d => w.2.val)
    ((sourceSplit d).apply_symm_apply z)
  exact h

/-- Only the standard single-submodule Smith theorem is invoked. -/
def smithData := (LinearMap.range d).smithNormalForm (Module.finBasis R N)

def smithRank : ℕ := (smithData d).1

def smith : Basis.SmithNormalForm (LinearMap.range d)
    (Fin (Module.finrank R N)) (smithRank d) := (smithData d).2

/-- Source basis: a kernel basis followed by lifts of the actual image Smith basis. -/
def sourceBasis : Basis (Fin (Module.finrank R (LinearMap.ker d)) ⊕ Fin (smithRank d)) R M :=
  ((Module.finBasis R (LinearMap.ker d)).prod (smith d).bN).map (sourceSplit d).symm

def targetBasis : Basis (Fin (Module.finrank R N)) R N := (smith d).bM

theorem sourceBasis_kernel (i : Fin (Module.finrank R (LinearMap.ker d))) :
    d (sourceBasis d (Sum.inl i)) = 0 := by
  simp only [sourceBasis, Basis.map_apply, sourceSplit_symm_d,
    Basis.prod_apply_inl_snd, Submodule.coe_zero]

theorem sourceBasis_pair (i : Fin (smithRank d)) :
    d (sourceBasis d (Sum.inr i)) = (smith d).a i • targetBasis d ((smith d).f i) := by
  simp only [sourceBasis, Basis.map_apply, sourceSplit_symm_d, Basis.prod_apply_inr_snd]
  exact (smith d).snf i

omit [Module.Free R M] [Module.Finite R M] in
theorem smith_coefficient_ne_zero (i : Fin (smithRank d)) : (smith d).a i ≠ 0 := by
  intro h
  apply (smith d).bN.ne_zero i
  apply Subtype.ext
  simpa [h] using (smith d).snf i

/-- Every incoming differential has zero coordinate on every lifted image vector. -/
theorem incoming_pair_coordinate {P : Type*} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] M) (hdf : d.comp f = 0) (x : P) (i : Fin (smithRank d)) :
    (sourceBasis d).repr (f x) (Sum.inr i) = 0 := by
  change (smith d).bN.repr ((sourceSplit d (f x)).2) i = 0
  have hx : d.rangeRestrict (f x) = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun hdf x
  rw [sourceSplit_last, hx, map_zero]
  rfl

/-- A nonzero Smith target vector has no outgoing differential in a torsion-free target. -/
theorem outgoing_pair_zero {P : Type*} [AddCommGroup P] [Module R P]
    [NoZeroSMulDivisors R P] (f : N →ₗ[R] P) (hfd : f.comp d = 0)
    (i : Fin (smithRank d)) : f (targetBasis d ((smith d).f i)) = 0 := by
  have h : (smith d).a i • f (targetBasis d ((smith d).f i)) = 0 := by
    rw [← map_smul, ← sourceBasis_pair]
    exact LinearMap.congr_fun hfd _
  exact (smul_eq_zero.mp h).resolve_left (smith_coefficient_ne_zero d i)

omit [Module.Free R M] [Module.Finite R M] in
/-- Every Smith coefficient of a scalar multiple is divisible by that scalar. -/
theorem scalar_dvd_smith_coefficient (a : R) (i : Fin (smithRank (a • d))) :
    a ∣ (smith (a • d)).a i := by
  obtain ⟨x, hx⟩ := ((smith (a • d)).bN i).property
  refine ⟨((smith (a • d)).bM.repr (d x)) ((smith (a • d)).f i), ?_⟩
  have h := congrArg
    (fun y : N => ((smith (a • d)).bM.repr y) ((smith (a • d)).f i))
    ((smith (a • d)).snf i)
  rw [← hx] at h
  simpa using h.symm

/-- The same constructed bases diagonalize a scalar multiple of the original map. -/
theorem scaled_pair (a : R) (i : Fin (smithRank d)) :
    (a • d) (sourceBasis d (Sum.inr i)) =
      (a * (smith d).a i) • targetBasis d ((smith d).f i) := by
  simp only [LinearMap.smul_apply, sourceBasis_pair, smul_smul]

/-- The kernel columns stay zero after scalar multiplication. -/
theorem scaled_kernel (a : R) (i : Fin (Module.finrank R (LinearMap.ker d))) :
    (a • d) (sourceBasis d (Sum.inl i)) = 0 := by
  simp only [LinearMap.smul_apply, sourceBasis_kernel, smul_zero]

#print axioms imageSection
#print axioms imageSection_rightInverse
#print axioms sourceSplit
#print axioms sourceSplit_last
#print axioms sourceSplit_symm_d
#print axioms smithData
#print axioms smithRank
#print axioms smith
#print axioms sourceBasis
#print axioms targetBasis
#print axioms sourceBasis_kernel
#print axioms sourceBasis_pair
#print axioms smith_coefficient_ne_zero
#print axioms incoming_pair_coordinate
#print axioms outgoing_pair_zero
#print axioms scalar_dvd_smith_coefficient
#print axioms scaled_pair
#print axioms scaled_kernel

end Verification.SmithChainBlock
