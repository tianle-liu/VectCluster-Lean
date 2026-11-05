/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RectangularSourceSinkMutation
import Verification.ExchangeReindex

/-!
# Rectangular Mutation Sequence

Finite source/sink sequences preserve the actual rectangular full
splitting, so every independent selected-column family remains AS.
-/
noncomputable section
namespace Verification.RectangularMutationSequence
open Classical Verification.RectangularMutationSplitting Verification.RectangularSourceSinkMutation
variable {V F : Type} [Fintype V] [Fintype F] [DecidableEq V]

def result (B : Matrix (V⊕F) V ℤ) : List V→Matrix (V⊕F) V ℤ
  | []=>B
  | k::l=>result (matrix B k) l

def Admissible (B : Matrix (V⊕F) V ℤ) : List V→Prop
  | []=>True
  | k::l=>SourceSink B k ∧ Admissible (matrix B k) l

def retraction (B : Matrix (V⊕F) V ℤ) (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ)) :
    List V→(((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ))
  | []=>r
  | k::l=>retraction (matrix B k) (RectangularMutationSplitting.retraction B k r) l

omit [Fintype F] in
theorem left (B : Matrix (V⊕F) V ℤ) (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ))
    (hr : r.comp B.mulVecLin=LinearMap.id) (l : List V) :
    (retraction B r l).comp (result B l).mulVecLin=LinearMap.id := by
  induction l generalizing B r with
  | nil=>exact hr
  | cons k l ih=>exact ih _ _ (RectangularMutationSplitting.left B k r hr)

omit [Fintype F] in
theorem skew (B : Matrix (V⊕F) V ℤ) (hB : Skew B) (l : List V) (hl : Admissible B l) :
    Skew (result B l) := by
  induction l generalizing B with
  | nil=>exact hB
  | cons k l ih=>exact ih _ (RectangularSourceSinkMutation.skew B hB k hl.1) hl.2

omit [Fintype F] in
theorem absolute (B : Matrix (V⊕F) V ℤ) (hB : Skew B) (l : List V) (hl : Admissible B l) (i j : V) :
    |result B l (Sum.inl i) j|=|B (Sum.inl i) j| := by
  induction l generalizing B with
  | nil=>rfl
  | cons k l ih=>
    exact (ih _ (RectangularSourceSinkMutation.skew B hB k hl.1) hl.2).trans
      (RectangularSourceSinkMutation.absolute B hB k hl.1 i j)

theorem selected_AS (B : Matrix (V⊕F) V ℤ) (hB : Skew B)
    (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id)
    (l : List V) (hl : Admissible B l) (I : Finset V)
    (hI : ExchangeReindex.PrincipalIndependent (result B l) I) :
    AnticliqueSubcolumns.AS (result B l) I := by
  apply FullMatrixSelectedSplit.AS (result B l) I (retraction B r l) (left B r hr l)
  intro i hi j hj
  by_cases hij : i=j
  · subst j
    exact diagonal _ (skew B hB l hl) i
  · exact hI i hi j hj hij

#print axioms result
#print axioms Admissible
#print axioms retraction
#print axioms left
#print axioms skew
#print axioms absolute
#print axioms selected_AS
end Verification.RectangularMutationSequence
