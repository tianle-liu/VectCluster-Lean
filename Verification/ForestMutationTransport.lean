/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BFZForestMutationInput

/-!
# Forest Mutation Transport

Iterating the ordinary single-step acyclic presentation theorem along
the literal source/sink mutation sequence. Forest support at every step is
proved from the actual principal-entry calculation.
-/
noncomputable section
namespace Verification.ForestMutationTransport
open Verification.RootedForestCertificate Verification.RectangularSourceSinkMutation
open Verification.RectangularMutationSequence Verification.BFZForestMutationInput
variable (R : Type) [Field R] (H : Standard R)
variable {V F : Type} [Fintype V] [Fintype F] [DecidableEq V]
variable (P : Forest V) (B : Matrix (V⊕F) V ℤ)
variable (hB : Skew B) (hp : ∀i j,B (Sum.inl i) j≠0 ↔ P.Adj i j)

include hB hp in
omit H [Field R] [Fintype F] in
theorem support_step (k : V) (hk : SourceSink B k) :
    ∀i j,RectangularMutationSplitting.matrix B k (Sum.inl i) j≠0 ↔ P.Adj i j := by
  intro i j
  exact (not_congr (zero_iff B hB k hk i j)).trans (hp i j)

def equiv (l : List V) (hl : Admissible B l) :
    FrozenExchangeReindex.Global R (extended B) ≃ₐ[R]
      FrozenExchangeReindex.Global R (extended (result B l)) := by
  induction l generalizing B with
  | nil=>exact AlgEquiv.refl
  | cons k l ih=>
    exact (H.equiv V F P B hB hp k hl.1).trans
      (ih _ (RectangularSourceSinkMutation.skew B hB k hl.1)
        (support_step P B hB hp k hl.1) hl.2)

#print axioms support_step
#print axioms equiv
end Verification.ForestMutationTransport
