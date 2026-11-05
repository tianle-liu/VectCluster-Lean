/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerComplex
import Verification.IndependentChartIndex

/-!
# Original Witt Integer Model

Instantiate the integral Witt complex with the manuscript's original
acyclic exchange matrix and its actual independent-set family.
-/
noncomputable section
namespace Verification.OriginalWittIntegerModel
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.OriginalWittIntegerComplex
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)

def hereditary : ∀ I J, J⊆I → Independent (laterWeights κ n B) I →
    Independent (laterWeights κ n B) J := by
  intro I J h hI i hi j hj
  exact hI i (h hi) j (h hj)

include hpos hneg hsupport in
omit [Fintype κ] in
theorem zero_block (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    ∀ i j : I, B (Sum.inl j.val) (Sum.inl i.val)=0 := by
  intro i j
  exact IndependentChartIndex.independent_principal_zero κ n I B hpos hneg hsupport hI
    j.val i.val j.property i.property

def independent_entries : ∀ I, Independent (laterWeights κ n B) I →
    ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) (Sum.inl i)=0 := by
  intro I hI i hi j hj _
  exact zero_block κ n B hpos hneg hsupport I hI ⟨i,hi⟩ ⟨j,hj⟩

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  OriginalWittIntegerComplex.complex (fun a i => B a (Sum.inl i))
    (Independent (laterWeights κ n B)) (hereditary κ n B)
    (independent_entries κ n B hpos hneg hsupport)

variable (hall : ∀ I, Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hall in
theorem finite_free (p : ℕ) :
    Module.Finite ℤ ((complex κ n B hpos hneg hsupport).X p) ∧
    Module.Free ℤ ((complex κ n B hpos hneg hsupport).X p) := by
  constructor
  · exact degree_finite _ _ (zero_block κ n B hpos hneg hsupport) hall p
  · exact degree_free _ _ (zero_block κ n B hpos hneg hsupport) hall p

omit [Fintype κ] in
theorem bounded (p : ℕ) (hp : n < p) :
    Subsingleton ((complex κ n B hpos hneg hsupport).X p) :=
  degree_above _ _ p (by simpa using hp)

include hpos hneg hsupport hall in
theorem stratum_rank (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I) :
    Module.finrank ℤ (OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i)) I) =
      2^(n+Fintype.card κ-2*I.card) := by
  simpa using OriginalWittStratumFree.rank (fun a i => B a (Sum.inl i)) I
    (zero_block κ n B hpos hneg hsupport I hI) (hall I hI)

#print axioms hereditary
#print axioms zero_block
#print axioms independent_entries
#print axioms complex
#print axioms finite_free
#print axioms bounded
#print axioms stratum_rank
end Verification.OriginalWittIntegerModel
