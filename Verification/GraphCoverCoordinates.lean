/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverFibers
import Verification.ExteriorTotalBasis

/-!
# Graph Cover Coordinates

The exterior fiber product has precisely the original independent-simplex
basis. The following equivalence is constructed from the actual full exterior
bases and the exact cover/outside simplex decomposition.
-/

namespace Verification.GraphCoverCoordinates

open Verification.GraphCover Verification.GraphCoverFibers
  Verification.EvenGraphBridge

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V)

/-- Finite subsets of a finite subtype are exactly subsets of its ambient finite set. -/
def subtypeFinsetEquiv (S : Finset V) : Finset {v : V // v ∈ S} ≃ {K : Finset V // K ⊆ S} where
  toFun K := ⟨K.map (Function.Embedding.subtype _), by
    intro v hv
    exact Finset.property_of_mem_map_subtype _ hv⟩
  invFun K := K.val.subtype (fun v => v ∈ S)
  left_inv K := by
    ext v
    simp
  right_inv K := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun v hv => K.property hv)

noncomputable def fiberIndexEquiv (hC : Covers G C) :
    (Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) ≃ Simplex G T :=
  let e : (Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) ≃
      (Σ I : CoverSimplex G C T, Fiber G C T I) :=
    Equiv.sigmaCongrRight (fun I : CoverSimplex G C T =>
      subtypeFinsetEquiv (remaining G C T I.val))
  e.trans (simplexFiberEquiv G C T hC).symm

/-- Actual finite coefficient equivalence between the graph basis and exterior fibers. -/
noncomputable def coefficientEquiv (hC : Covers G C) :
    FiberProduct (R := R) G C T ≃ₗ[R] (Simplex G T →₀ R) := by
  classical
  exact (LinearEquiv.piCongrRight fun I =>
    Verification.ExteriorTotalBasis.coefficientEquiv (R := R) (α := RemainingVertex G C T I)).trans
      ((Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm.trans
        (Finsupp.domLCongr (fiberIndexEquiv G C T hC)))

open Classical in
theorem sigma_single {ι : Type*} [Fintype ι] {α : ι → Type*}
    (x : Σ i, α i) (r : R) :
    Finsupp.sigmaFinsuppLEquivPiFinsupp R (Finsupp.single x r) =
      Pi.single x.1 (Finsupp.single x.2 r) := by
  rcases x with ⟨j,b⟩
  funext i
  apply Finsupp.ext
  intro a
  by_cases hi : i = j
  · subst i
    simp [Finsupp.sigmaFinsuppLEquivPiFinsupp_apply, Finsupp.single_apply]
  · have hn : (⟨j,b⟩ : Σ i, α i) ≠ ⟨i,a⟩ := fun h => hi (congrArg Sigma.fst h).symm
    simp [Finsupp.sigmaFinsuppLEquivPiFinsupp_apply, Finsupp.single_apply, hn, hi]


open Classical in
/-- Explicit inverse on every graph basis element, retaining its actual cover stratum. -/
theorem coefficientEquiv_symm_single (hC : Covers G C)
    (x : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) (r : R) :
    (coefficientEquiv (R := R) G C T hC).symm
      (Finsupp.single (fiberIndexEquiv G C T hC x) r) =
    Pi.single x.1 (r • word (x.2.sort (· ≤ ·))) := by
  classical
  simp only [coefficientEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Finsupp.domLCongr_symm, Finsupp.domLCongr_single, Equiv.symm_apply_apply,
    LinearEquiv.symm_symm, sigma_single, LinearEquiv.piCongrRight_symm]
  funext I
  by_cases hi : I = x.1
  · subst I
    simp [LinearEquiv.piCongrRight_apply,
      Verification.ExteriorTotalBasis.coefficientEquiv_symm_single]
  · simp [LinearEquiv.piCongrRight_apply, hi]

noncomputable def graphFiberBasis (hC : Covers G C) :
    Basis (Simplex G T) R (FiberProduct (R := R) G C T) :=
  Basis.ofRepr (coefficientEquiv G C T hC)

open Classical in
theorem graphFiberBasis_apply (hC : Covers G C)
    (x : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) :
    graphFiberBasis (R := R) G C T hC (fiberIndexEquiv G C T hC x) =
      Pi.single x.1 (word (x.2.sort (· ≤ ·))) := by
  change (coefficientEquiv (R := R) G C T hC).symm (Finsupp.single _ 1) = _
  rw [coefficientEquiv_symm_single, one_smul]

theorem coefficientEquiv_apply (hC : Covers G C)
    (f : FiberProduct (R := R) G C T)
    (x : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) :
    coefficientEquiv G C T hC f (fiberIndexEquiv G C T hC x) =
      Verification.ExteriorTotalBasis.coefficientEquiv (f x.1) x.2 := by
  change Verification.ExteriorTotalBasis.coefficientEquiv
    (f ((fiberIndexEquiv G C T hC).symm (fiberIndexEquiv G C T hC x)).1)
    (((fiberIndexEquiv G C T hC).symm (fiberIndexEquiv G C T hC x)).2) = _
  rw [Equiv.symm_apply_apply]

open Classical in
theorem coefficientEquiv_single_word (hC : Covers G C)
    (x : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) (r : R) :
    coefficientEquiv (R := R) G C T hC (Pi.single x.1 (r • word (x.2.sort (· ≤ ·)))) =
      Finsupp.single (fiberIndexEquiv G C T hC x) r := by
  apply (coefficientEquiv G C T hC).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (coefficientEquiv_symm_single G C T hC x r).symm

#print axioms subtypeFinsetEquiv
#print axioms fiberIndexEquiv
#print axioms coefficientEquiv
#print axioms sigma_single
#print axioms coefficientEquiv_symm_single
#print axioms graphFiberBasis
#print axioms graphFiberBasis_apply
#print axioms coefficientEquiv_apply
#print axioms coefficientEquiv_single_word

end Verification.GraphCoverCoordinates
