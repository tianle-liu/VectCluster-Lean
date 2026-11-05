/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldChainIndex

/-!
# Sevenfold Chain Matrix

The actual augmented sevenfold boundary has the explicitly computed
four-edge incidence matrix, on every induced subset of its vertices.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldChainMatrix
open Verification.SevenfoldGraphFreeness Verification.SevenfoldChainIndex
open Verification.GraphCover Verification.GraphChainMatrix Verification.GraphSimplexChains

def matrix (i j : Fin 10) : ℤ :=
  if j = 0 then 0 else if j ≤ 5 then (if i=0 then 1 else 0)
  else if j=6 then (if i=3 then 1 else if i=1 then -1 else 0)
  else if j=7 then (if i=3 then 1 else if i=2 then -1 else 0)
  else if j=8 then (if i=4 then 1 else if i=2 then -1 else 0)
  else (if i=4 then 1 else if i=1 then -1 else 0)


theorem numeric : ∀ i j : Fin 10,
    (∑ v ∈ face j, if (face j).erase v = face i then
      (-1 : ℤ) ^ Verification.EvenDifferential.rankBelow (face j) v else 0) = matrix i j := by
  decide


theorem entry (T : Finset (Fin 5)) (i j : {i : Fin 10 // face i ⊆ T}) :
    chainMatrix (R := ℤ) graph T (index T i) (index T j) = matrix i.val j.val := by
  rw [chainMatrix_entry]
  simp only [basisBoundary,Finsupp.finset_sum_apply,Finsupp.single_apply]
  have he (v : Fin 5) : eraseSimplex graph T (index T j) v = index T i ↔
      (face j.val).erase v = face i.val := by
    rw [Subtype.ext_iff]
    have hdec : (fun a b : Fin 5 => LinearOrder.toDecidableEq a b) = instDecidableEqFin 5 :=
      Subsingleton.elim _ _
    simp only [eraseSimplex,index_face,hdec]

  simp_rw [he]
  change (∑ v ∈ face j.val, if (face j.val).erase v = face i.val then
    (-1 : ℤ) ^ Verification.EvenDifferential.rankBelow (face j.val) v else 0) = _
  exact numeric i.val j.val

#print axioms numeric

#print axioms matrix
#print axioms entry
end Verification.SevenfoldChainMatrix
