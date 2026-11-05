/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstDegreeCoordinates
import Mathlib.Data.Fintype.BigOperators

/-!
# Path One Pure Basis

Exact dimensions of both actual degrees of the length-one Z chain complex.
The bases are transported from the already exhaustive word index bijections.
-/

namespace Verification.PathOnePureBasis

open Classical Verification.PathFirstBasis Verification.PathEndpointWords
  Verification.PathNormalizedBasis Verification.PathEndpointWordRemoval Verification.PathStratumGrading
  Verification.PathFirstDegreeCoordinates Verification.GradedPerturbation

variable {R : Type} [CommRing R]

theorem word_card (n : ℕ) : Fintype.card (Verification.PathWords.Word n)=2^n := by
  change Fintype.card (List.Vector Bool n)=2^n
  simpa only [Fintype.card_bool] using card_vector (α := Bool) n

theorem source_card : Fintype.card (OneSource RightNormal 1)=1 := by
  have hn : Fintype.card (NormalWord RightNormal 1)=1 :=
    (Fintype.card_congr (rightWordEquiv 0)).trans (word_card 0)
  have hv : Fintype.card (Vertex 1)=1 := by simp [Vertex]
  rw [Fintype.card_prod,hn,hv,mul_one]

noncomputable def firstBasis :
    Basis (Fin 1) R (degreeModule (R := R) (fun x : NormalIndex RightNormal 1 => -degree x) (-1)) :=
  ((Finsupp.basisSingleOne : Basis (OneSource RightNormal 1) R (OneSource RightNormal 1 →₀ R)).reindex
    (Fintype.equivFinOfCardEq source_card)).map (firstCoordinates RightNormal 1).symm

noncomputable def zeroBasis :
    Basis (Fin 4) R (degreeModule (R := R) (fun x : NormalIndex RightNormal 1 => -degree x) 0) :=
  ((Finsupp.basisSingleOne : Basis (Verification.PathWords.Word 2) R (Verification.PathWords.Word 2 →₀ R)).reindex
    (Fintype.equivFinOfCardEq (word_card 2))).map (zZeroCoordinates 1).symm

theorem degree_range (x : NormalIndex RightNormal 1) : -degree x = -1 ∨ -degree x=0 := by
  have hc : x.1.val.card≤1 := by simpa using Finset.card_le_card x.1.property.1
  change -(x.1.val.card:ℤ) = -1 ∨ -(x.1.val.card:ℤ)=0
  omega

#print axioms word_card
#print axioms source_card
#print axioms firstBasis
#print axioms zeroBasis
#print axioms degree_range

end Verification.PathOnePureBasis
