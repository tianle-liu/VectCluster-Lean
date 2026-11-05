/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCover
import Verification.AugmentedSimplexContraction

/-!
# Graph Cover Fibers

The fiberwise pure complex in the vertex-cover filtration, with its actual
boundary, contraction, and projection onto the empty fibers. The orientation
puts the cover vertices before the outside vertices, hence the factor (-1)^|I|.
-/

namespace Verification.GraphCoverFibers

open Verification.GraphCover

variable {R V : Type*} [CommRing R] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V)

abbrev RemainingVertex (I : CoverSimplex G C T) := {v : V // v ∈ remaining G C T I.val}

abbrev FiberExterior (I : CoverSimplex G C T) :=
  ExteriorAlgebra R (RemainingVertex G C T I → R)

noncomputable def pivot (I : CoverSimplex G C T) (h : (remaining G C T I.val).Nonempty) :
    RemainingVertex G C T I :=
  ⟨(remaining G C T I.val).min' h, Finset.min'_mem _ _⟩

def phase (I : CoverSimplex G C T) : R := (-1 : R) ^ I.val.card

theorem phase_square (I : CoverSimplex G C T) : phase (R := R) G C T I * phase G C T I = 1 := by
  rw [phase, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

noncomputable def boundaryAt (I : CoverSimplex G C T) :
    FiberExterior (R := R) G C T I →ₗ[R] FiberExterior (R := R) G C T I :=
  phase (R := R) G C T I •
    Verification.AugmentedSimplexContraction.boundary (R := R) (α := RemainingVertex G C T I)

noncomputable def homotopyAt (I : CoverSimplex G C T) :
    FiberExterior (R := R) G C T I →ₗ[R] FiberExterior (R := R) G C T I := by
  classical
  exact if h : (remaining G C T I.val).Nonempty then
    phase (R := R) G C T I • Verification.AugmentedSimplexContraction.homotopy (R := R) (pivot G C T I h) else 0

noncomputable def projectionAt (I : CoverSimplex G C T) :
    FiberExterior (R := R) G C T I →ₗ[R] FiberExterior (R := R) G C T I := by
  classical
  exact if (remaining G C T I.val).Nonempty then 0 else LinearMap.id

theorem boundaryAt_squared (I : CoverSimplex G C T) :
    (boundaryAt (R := R) G C T I).comp (boundaryAt G C T I) = 0 := by
  simp only [boundaryAt, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    phase_square, one_smul, Verification.AugmentedSimplexContraction.boundary_squared]

theorem homotopyAt_squared (I : CoverSimplex G C T) :
    (homotopyAt (R := R) G C T I).comp (homotopyAt G C T I) = 0 := by
  classical
  by_cases h : (remaining G C T I.val).Nonempty
  · simp only [homotopyAt, dif_pos h, LinearMap.smul_comp, LinearMap.comp_smul,
      smul_smul, phase_square, one_smul, Verification.AugmentedSimplexContraction.homotopy_squared]
  · simp [homotopyAt, h]

theorem fiber_homotopy_identity (I : CoverSimplex G C T) :
    (boundaryAt (R := R) G C T I).comp (homotopyAt G C T I) +
      (homotopyAt G C T I).comp (boundaryAt G C T I) =
      LinearMap.id - projectionAt G C T I := by
  classical
  by_cases h : (remaining G C T I.val).Nonempty
  · simp only [homotopyAt, dif_pos h, boundaryAt, projectionAt, if_pos h,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, phase_square, one_smul, sub_zero]
    exact Verification.AugmentedSimplexContraction.boundary_homotopy (R := R) (pivot G C T I h)
  · have he : remaining G C T I.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    letI : IsEmpty (RemainingVertex G C T I) := ⟨by intro v; simpa [he] using v.property⟩
    simp [homotopyAt, projectionAt, boundaryAt, h,
      Verification.AugmentedSimplexContraction.empty_boundary]

/-- Every empty fiber is one copy of the coefficient ring on its dominating cover subset. -/
noncomputable def dominatingFiberEquiv (I : CoverSimplex G C T) (hI : Dominates G C T I.val) :
    FiberExterior (R := R) G C T I ≃ₐ[R] R := by
  have he := (remaining_empty_iff G C T I.val).mpr hI
  letI : IsEmpty (RemainingVertex G C T I) := ⟨by intro v; simpa [he] using v.property⟩
  exact Verification.AugmentedSimplexContraction.emptyEquiv

abbrev FiberProduct := (I : CoverSimplex G C T) → FiberExterior (R := R) G C T I

noncomputable def pureBoundary : FiberProduct (R := R) G C T →ₗ[R] FiberProduct (R := R) G C T :=
  LinearMap.pi (fun I => (boundaryAt G C T I).comp (LinearMap.proj I))

noncomputable def pureHomotopy : FiberProduct (R := R) G C T →ₗ[R] FiberProduct (R := R) G C T :=
  LinearMap.pi (fun I => (homotopyAt G C T I).comp (LinearMap.proj I))

noncomputable def pureProjection : FiberProduct (R := R) G C T →ₗ[R] FiberProduct (R := R) G C T :=
  LinearMap.pi (fun I => (projectionAt G C T I).comp (LinearMap.proj I))

theorem pureBoundary_squared :
    (pureBoundary (R := R) G C T).comp (pureBoundary G C T) = 0 := by
  apply LinearMap.ext
  intro x
  funext I
  exact LinearMap.congr_fun (boundaryAt_squared (R := R) G C T I) (x I)

theorem pureHomotopy_squared :
    (pureHomotopy (R := R) G C T).comp (pureHomotopy G C T) = 0 := by
  apply LinearMap.ext
  intro x
  funext I
  exact LinearMap.congr_fun (homotopyAt_squared (R := R) G C T I) (x I)

/-- Simultaneous explicit contraction of every nonempty simplex fiber. -/
theorem pure_homotopy_identity :
    (pureBoundary (R := R) G C T).comp (pureHomotopy G C T) +
      (pureHomotopy G C T).comp (pureBoundary G C T) =
      LinearMap.id - pureProjection G C T := by
  apply LinearMap.ext
  intro x
  funext I
  exact LinearMap.congr_fun (fiber_homotopy_identity (R := R) G C T I) (x I)

theorem projectionAt_boundary (I : CoverSimplex G C T) :
    (projectionAt (R := R) G C T I).comp (boundaryAt G C T I) = 0 := by
  classical
  by_cases h : (remaining G C T I.val).Nonempty
  · simp [projectionAt, h]
  · have he : remaining G C T I.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    letI : IsEmpty (RemainingVertex G C T I) := ⟨by intro v; simpa [he] using v.property⟩
    simp [projectionAt, boundaryAt, h, Verification.AugmentedSimplexContraction.empty_boundary]

theorem projectionAt_homotopy (I : CoverSimplex G C T) :
    (projectionAt (R := R) G C T I).comp (homotopyAt G C T I) = 0 := by
  classical
  by_cases h : (remaining G C T I.val).Nonempty <;> simp [projectionAt, homotopyAt, h]

theorem pureProjection_boundary :
    (pureProjection (R := R) G C T).comp (pureBoundary G C T) = 0 := by
  apply LinearMap.ext
  intro x
  funext I
  exact LinearMap.congr_fun (projectionAt_boundary (R := R) G C T I) (x I)

theorem pureProjection_homotopy :
    (pureProjection (R := R) G C T).comp (pureHomotopy G C T) = 0 := by
  apply LinearMap.ext
  intro x
  funext I
  exact LinearMap.congr_fun (projectionAt_homotopy (R := R) G C T I) (x I)

/-- The normalized contraction identity required by finite perturbation. -/
theorem pureHomotopy_regular :
    ((pureHomotopy (R := R) G C T).comp (pureBoundary G C T)).comp (pureHomotopy G C T) =
      pureHomotopy G C T := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (pure_homotopy_identity (R := R) G C T) (pureHomotopy G C T x)
  have hh := LinearMap.congr_fun (pureHomotopy_squared (R := R) G C T) x
  have hp := LinearMap.congr_fun (pureProjection_homotopy (R := R) G C T) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh hp
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, hh, hp, map_zero, zero_add, sub_zero] using h

theorem pureBoundary_regular :
    ((pureBoundary (R := R) G C T).comp (pureHomotopy G C T)).comp (pureBoundary G C T) =
      pureBoundary G C T := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (pure_homotopy_identity (R := R) G C T) (pureBoundary G C T x)
  have hh := LinearMap.congr_fun (pureBoundary_squared (R := R) G C T) x
  have hp := LinearMap.congr_fun (pureProjection_boundary (R := R) G C T) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh hp
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, hh, hp, map_zero, add_zero, sub_zero] using h

#print axioms pivot
#print axioms phase
#print axioms phase_square
#print axioms boundaryAt
#print axioms homotopyAt
#print axioms projectionAt
#print axioms boundaryAt_squared
#print axioms homotopyAt_squared
#print axioms fiber_homotopy_identity
#print axioms dominatingFiberEquiv
#print axioms pureBoundary
#print axioms pureHomotopy
#print axioms pureProjection
#print axioms pureBoundary_squared
#print axioms pureHomotopy_squared
#print axioms pure_homotopy_identity
#print axioms projectionAt_boundary
#print axioms projectionAt_homotopy
#print axioms pureProjection_boundary
#print axioms pureProjection_homotopy
#print axioms pureHomotopy_regular
#print axioms pureBoundary_regular

end Verification.GraphCoverFibers

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.GraphCoverFibers.FiberExterior
#print axioms Verification.GraphCoverFibers.FiberProduct
#print axioms Verification.GraphCoverFibers.RemainingVertex
