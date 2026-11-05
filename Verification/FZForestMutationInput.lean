/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RootedForestCertificate
import Verification.RectangularMutationSequence

/-!
# FZ Forest Mutation Input

Uniform cited input: Fomin–Zelevinsky II, Proposition 9.2,
https://arxiv.org/pdf/math/0208229, p.31. Any two orientations of a finite
weighted tree are connected by source/sink mutations; disjoint forests are
handled componentwise. The reference input ranges over all rooted forests,
not manuscript paths. Its output is the literal rectangular FZ mutation.
-/
noncomputable section
namespace Verification.FZForestMutationInput
open Verification.RootedForestCertificate Verification.RectangularSourceSinkMutation
open Verification.RectangularMutationSequence
structure Standard where
  reorient : ∀ (V F : Type) [Fintype V] [Fintype F] [DecidableEq V]
    (P : Forest V) (B : Matrix (V⊕F) V ℤ) (D : Matrix V V ℤ),
    Skew B → (∀i j,D i j= -D j i) →
    (∀i j,B (Sum.inl i) j≠0 ↔ P.Adj i j) →
    (∀i j,|D i j|=|B (Sum.inl i) j|) →
    ∃l : List V,Admissible B l ∧ ∀i j,result B l (Sum.inl i) j=D i j
#print axioms Standard
end Verification.FZForestMutationInput
