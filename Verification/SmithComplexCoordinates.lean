/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithChainBlock
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Smith Complex Coordinates

Coherent Smith coordinates in every degree of an actual complex.
Smith bases are chosen for boundaries inside cycles, then lifted using the
constructed projective sections. This coordinates all differentials at once.
-/

noncomputable section
namespace Verification.SmithComplexCoordinates
open CategoryTheory

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

def outgoing (n : ℤ) : C.X n →ₗ[R] C.X (n+1) := (C.d n (n+1)).hom

def incoming (n : ℤ) : C.X (n-1) →ₗ[R] C.X n := (C.d (n-1) n).hom

def cycles (n : ℤ) : Submodule R (C.X n) := LinearMap.ker (outgoing C n)

def boundaries (n : ℤ) : Submodule R (cycles C n) :=
  (LinearMap.range (incoming C n)).comap (cycles C n).subtype

omit [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]
    [IsDomain R] [IsPrincipalIdealRing R] in
theorem incoming_le_cycles (n : ℤ) : LinearMap.range (incoming C n) ≤ cycles C n := by
  apply LinearMap.range_le_ker_iff.mpr
  exact congrArg ModuleCat.Hom.hom (C.d_comp_d (n-1) n (n+1))

def boundaryEquiv (n : ℤ) : boundaries C n ≃ₗ[R] LinearMap.range (incoming C n) :=
  Submodule.comapSubtypeEquivOfLe (incoming_le_cycles C n)

def nextBoundaryEquiv (n : ℤ) : LinearMap.range (outgoing C n) ≃ₗ[R] boundaries C (n+1) := by
  have h : LinearMap.range (outgoing C n) = LinearMap.range (incoming C (n+1)) := by
    exact congrArg (fun k : ℤ => LinearMap.range (C.d k (n+1)).hom)
      (show n = n+1-1 by omega)
  exact (LinearEquiv.ofEq _ _ h).trans (boundaryEquiv C (n+1)).symm

omit [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]
    [IsDomain R] [IsPrincipalIdealRing R] in
theorem nextBoundaryEquiv_val (n : ℤ) (x : LinearMap.range (outgoing C n)) :
    (nextBoundaryEquiv C n x).val.val = x.val := by
  have h : LinearMap.range (outgoing C n) = LinearMap.range (incoming C (n+1)) :=
    congrArg (fun k : ℤ => LinearMap.range (C.d k (n+1)).hom)
      (show n = n+1-1 by omega)
  change (((LinearEquiv.ofEq _ _ h) x) : C.X (n+1)) = x.val
  exact LinearEquiv.coe_ofEq_apply h x

def smithData (n : ℤ) :=
  (boundaries C n).smithNormalForm (Module.finBasis R (cycles C n))

def boundaryRank (n : ℤ) : ℕ := (smithData C n).1

def smith (n : ℤ) : Basis.SmithNormalForm (boundaries C n)
    (Fin (Module.finrank R (cycles C n))) (boundaryRank C n) := (smithData C n).2

abbrev NormalModule (n : ℤ) :=
  (Fin (Module.finrank R (cycles C n)) →₀ R) × (Fin (boundaryRank C (n+1)) →₀ R)

/-- Both sets of coordinates use the same boundary Smith basis at the next degree. -/
def coordinates (n : ℤ) : C.X n ≃ₗ[R] NormalModule C n :=
  (SmithChainBlock.sourceSplit (outgoing C n)).trans
    (LinearEquiv.prodCongr (smith C n).bM.repr
      ((nextBoundaryEquiv C n).trans (smith C (n+1)).bN.repr))

/-- Independent diagonal boundary insertion, written in the constructed Smith bases. -/
def diagonal (n : ℤ) : (Fin (boundaryRank C n) →₀ R) →ₗ[R]
    (Fin (Module.finrank R (cycles C n)) →₀ R) :=
  Finsupp.linearCombination R (fun i => Finsupp.single ((smith C n).f i) ((smith C n).a i))

theorem diagonal_boundary (n : ℤ) (x : boundaries C n) :
    diagonal C n ((smith C n).bN.repr x) = (smith C n).bM.repr x.val := by
  have h : (diagonal C n).comp (smith C n).bN.repr.toLinearMap =
      (smith C n).bM.repr.toLinearMap.comp (boundaries C n).subtype := by
    apply (smith C n).bN.ext
    intro i
    simp [diagonal, (smith C n).snf i]
  exact LinearMap.congr_fun h x

/-- The normal differential only joins a lifted boundary to its cycle pivot. -/
def normalDifferential (n : ℤ) : NormalModule C n →ₗ[R] NormalModule C (n+1) :=
  ((diagonal C (n+1)).comp (LinearMap.snd R _ _)).prod 0

theorem normalDifferential_apply (n : ℤ) (z : NormalModule C n) :
    normalDifferential C n z = (diagonal C (n+1) z.2, 0) := rfl

theorem normalDifferential_square (n : ℤ) :
    (normalDifferential C (n+1)).comp (normalDifferential C n) = 0 := by
  ext z i <;> simp [normalDifferential_apply]

theorem coordinates_cycle (n : ℤ) (x : cycles C n) :
    coordinates C n x.val = ((smith C n).bM.repr x, 0) := by
  have hx : (outgoing C n).rangeRestrict x.val = 0 := by
    apply Subtype.ext
    exact x.property
  change ((smith C n).bM.repr
    ⟨x.val - SmithChainBlock.imageSection (outgoing C n)
      ((outgoing C n).rangeRestrict x.val), _⟩,
    ((nextBoundaryEquiv C n).trans (smith C (n+1)).bN.repr)
      ((outgoing C n).rangeRestrict x.val)) = _
  simp only [hx, map_zero, sub_zero]

/-- Actual simultaneous conjugacy, with no diagonal-complex hypothesis. -/
theorem coordinates_differential (n : ℤ) (x : C.X n) :
    coordinates C (n+1) (outgoing C n x) =
      normalDifferential C n (coordinates C n x) := by
  let b := nextBoundaryEquiv C n ((outgoing C n).rangeRestrict x)
  have hb : b.val.val = outgoing C n x := nextBoundaryEquiv_val C n _
  rw [← hb, coordinates_cycle, normalDifferential_apply]
  change ((smith C (n+1)).bM.repr b.val, 0) =
    (diagonal C (n+1) ((smith C (n+1)).bN.repr b), 0)
  rw [diagonal_boundary]

/-- Every displayed pair coefficient is nonzero over the original PID. -/
theorem coefficient_ne_zero (n : ℤ) (i : Fin (boundaryRank C n)) :
    (smith C n).a i ≠ 0 := by
  intro h
  apply (smith C n).bN.ne_zero i
  apply Subtype.ext
  simpa [h] using (smith C n).snf i

theorem normalDifferential_cycle (n : ℤ)
    (z : Fin (Module.finrank R (cycles C n)) →₀ R) :
    normalDifferential C n (z,0) = 0 := by
  simp [normalDifferential_apply]

/-- The independent nonzero two-term blocks are explicit in these coordinates. -/
theorem normalDifferential_pair (n : ℤ) (i : Fin (boundaryRank C (n+1))) (r : R) :
    normalDifferential C n (0,Finsupp.single i r) =
      (Finsupp.single ((smith C (n+1)).f i) (r * (smith C (n+1)).a i),0) := by
  simp [normalDifferential_apply, diagonal]

#print axioms outgoing
#print axioms incoming
#print axioms cycles
#print axioms boundaries
#print axioms incoming_le_cycles
#print axioms boundaryEquiv
#print axioms nextBoundaryEquiv
#print axioms nextBoundaryEquiv_val
#print axioms smithData
#print axioms boundaryRank
#print axioms smith
#print axioms NormalModule
#print axioms coordinates
#print axioms diagonal
#print axioms diagonal_boundary
#print axioms normalDifferential
#print axioms normalDifferential_apply
#print axioms normalDifferential_square
#print axioms coordinates_cycle
#print axioms coordinates_differential
#print axioms coefficient_ne_zero
#print axioms normalDifferential_cycle
#print axioms normalDifferential_pair

end Verification.SmithComplexCoordinates
