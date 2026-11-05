/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittParityChange

/-!
# Even Witt Columns

For the article's even mutable matrix with clique-color coefficients,
the actual binary column is precisely the frozen color basis vector.
-/
noncomputable section
open scoped Classical
namespace Verification.EvenWittColumns
open Verification.OriginalWittQuotient
variable {V C : Type*}

def matrix (b : V → V → ℤ) (c : V → C) : (V ⊕ C) → V → ℤ :=
  fun a i => Sum.elim (fun j => 2 * b j i) (fun k => if c i = k then 1 else 0) a

def frozenMatrix (c : V → C) : (V ⊕ C) → V → ℤ :=
  fun a i => Sum.elim (fun _ => 0) (fun k => if c i = k then 1 else 0) a

theorem parity (b : V → V → ℤ) (c : V → C) (a : V ⊕ C) (i : V) :
    (matrix b c a i : ZMod 2) = (frozenMatrix c a i : ZMod 2) := by
  cases a with
  | inl j => simp [matrix,frozenMatrix,show (2 : ZMod 2) = 0 from by decide]
  | inr k => rfl

theorem column (b : V → V → ℤ) (c : V → C) (i : V) :
    columnVector (matrix b c) i =
      Multiplicative.ofAdd (Pi.single (Sum.inr (c i)) (1 : ZMod 2)) := by
  classical
  apply Multiplicative.toAdd.injective
  funext a
  cases a with
  | inl j => simp [columnVector,matrix,Pi.single_apply,show (2 : ZMod 2) = 0 from by decide]
  | inr k => simp [columnVector,matrix,Pi.single_apply,apply_ite,eq_comm]

def stratumEquiv (b : V → V → ℤ) (c : V → C) (I : Finset V) :
    Stratum (matrix b c) I ≃ₐ[ℤ] Stratum (frozenMatrix c) I :=
  OriginalWittParityChange.equiv (matrix b c) (frozenMatrix c) (parity b c) I

#print axioms matrix
#print axioms frozenMatrix
#print axioms parity
#print axioms column
#print axioms stratumEquiv
end Verification.EvenWittColumns
