/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainMatrix
import Verification.GraphCohomologyTF
import Verification.TransposeHomologyTF
import Verification.NatFinsuppHomologyReverse
import Verification.TotalHomologyTransport

/-!
# Graph Chain TF

The paper's integral chain-homology freeness condition implies TF of the
actual independence cochains through a proved finite-matrix transposition.
-/

namespace Verification.GraphChainTF

open Classical

open Verification.GraphCoverGrading Verification.GraphChainMatrix
  Verification.GraphBlockComplex Verification.GraphCohomologyTF
  Verification.GradedHomologyTF Verification.TransposeHomologyTF
  Verification.TotalHomologyTransport

variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
  (G : SimpleGraph V) (c : V → C)

/-- Literal form of the manuscript's all-induced integral chain-homology freeness. -/
def ChainGraphFree : Prop := ∀ (T : Finset V) (p : ℤ),
  Module.Free ℤ ((chainComplex (R := ℤ) G T).homology p)

/-- The weaker TF property is kept distinct from the paper's freeness hypothesis. -/
def ChainGraphTF : Prop := ∀ (T : Finset V) (p : ℤ),
  NoZeroSMulDivisors ℤ ((chainComplex (R := ℤ) G T).homology p)

theorem chain_tf_of_free (h : ChainGraphFree G) : ChainGraphTF G := by
  intro T p
  letI := h T p
  infer_instance

theorem chain_total_tf (h : ChainGraphTF G) (T : Finset V) :
    NoZeroSMulDivisors ℤ (Verification.IntegralSplitting.Homology
      (Matrix.toLin' (chainMatrix (R := ℤ) G T))) := by
  apply Verification.GradedHomologyTF.total_tf (degree G T) (chainMatrix G T)
    (chainMatrix_degree G T) (chainMatrix_square G T)
  intro p
  letI : SMul ℤ ((Verification.GradedPerturbation.matrixComplex (degree G T)
      (chainMatrix (R := ℤ) G T) (chainMatrix_degree G T) (chainMatrix_square G T)).homology p) :=
    (ModuleCat.isModule ((Verification.GradedPerturbation.matrixComplex (degree G T)
      (chainMatrix (R := ℤ) G T) (chainMatrix_degree G T) (chainMatrix_square G T)).homology p)).toSMul
  constructor
  intro a x hx
  exact (h T p).eq_zero_or_eq_zero_of_smul_eq_zero
    ((int_smul_eq_zsmul (ModuleCat.isModule
      ((chainComplex (R := ℤ) G T).homology p)) a x).symm.trans hx)

omit [Fintype C] in
set_option maxHeartbeats 800000 in
/-- Actual graph cochains inherit integral TF from the original chain complex. -/
theorem cochain_total_tf (h : ChainGraphTF G) (T : Finset V) :
    NoZeroSMulDivisors ℤ (Verification.IntegralSplitting.Homology
      (simplexDifferential ℤ G c (T,∅))) := by
  let e := cochainCoordinates (R := ℤ) G c T
  let E := Matrix.toLin' (chainMatrix (R := ℤ) G T).transpose
  let D := simplexDifferential ℤ G c (T,∅)
  have hc (x) : E (e x)=e (D x) :=
    LinearMap.congr_fun (cochainCoordinates_differential (R := ℤ) G c T) x
  apply total_tf_of_retract D E e.toLinearMap e.symm.toLinearMap
  · exact (cochainCoordinates_differential (R := ℤ) G c T).symm
  · apply LinearMap.ext
    intro f
    apply e.injective
    change e (e.symm (E f))=e (D (e.symm f))
    rw [e.apply_symm_apply,←hc,e.apply_symm_apply]
  · apply LinearMap.ext
    exact e.symm_apply_apply
  · exact transpose_total_tf (chainMatrix G T) (chainMatrix_square G T) (chain_total_tf G h T)

omit [Fintype C] in
/-- Integral chain TF implies the actual natural-indexed cohomology TF condition. -/
theorem cochainGraphTF_of_chainTF (h : ChainGraphTF G) : CochainGraphTF (R := ℤ) G c := by
  intro T p
  exact Verification.NatFinsuppHomologyReverse.degreewise_tf
    (simplexDegree G c (T,∅)) (simplexDifferential ℤ G c (T,∅))
    (simplexDifferential_degree ℤ G c (T,∅)) (simplexDifferential_square ℤ G c (T,∅))
    (cochain_total_tf G c h T) p

omit [Fintype C] in
/-- This direction uses exactly the paper's chain-freeness input, not an added cochain assumption. -/
theorem cochainGraphTF_of_chainFree (h : ChainGraphFree G) : CochainGraphTF (R := ℤ) G c :=
  cochainGraphTF_of_chainTF G c (chain_tf_of_free G h)

#print axioms ChainGraphFree
#print axioms ChainGraphTF
#print axioms chain_tf_of_free
#print axioms chain_total_tf
#print axioms cochain_total_tf
#print axioms cochainGraphTF_of_chainTF
#print axioms cochainGraphTF_of_chainFree

end Verification.GraphChainTF
