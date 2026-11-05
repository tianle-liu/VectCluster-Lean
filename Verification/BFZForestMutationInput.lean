/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RootedForestCertificate
import Verification.RectangularMutationSequence
import Verification.FrozenExchangeReindex

/-!
# BFZ Forest Mutation Input

Uniform ordinary reference consequence of BFZ, Corollary 1.17 and
Theorem 1.20/Corollary 1.21, https://arxiv.org/pdf/math/0305434, p.7:
acyclic geometric-type exchange presentations, with all frozen variables
inverted, present the cluster algebra. A source/sink seed mutation therefore
gives the following literal algebra isomorphism. Rooted-forest support is
an explicit stronger acyclicity hypothesis on both principal matrices;
source/sink mutation preserves that support internally. BFZ 1.20 does not
require coprimality (unlike the upper=lower theorem 1.18). No assertion for
an arbitrary exchange quotient, path reduction, or cohomology is an input.
-/
noncomputable section
namespace Verification.BFZForestMutationInput
open Verification.RootedForestCertificate Verification.RectangularSourceSinkMutation
variable {V F : Type}
def extended (B : Matrix (V⊕F) V ℤ) : (V⊕F)→(V⊕Empty)→ℤ :=
  fun a=>Sum.elim (B a) Empty.elim

structure Standard (R : Type) [Field R] where
  equiv : ∀ (V F : Type) [Fintype V] [Fintype F] [DecidableEq V]
    (P : Forest V) (B : Matrix (V⊕F) V ℤ),
    Skew B → (∀i j,B (Sum.inl i) j≠0 ↔ P.Adj i j) →
    ∀k : V,SourceSink B k →
    FrozenExchangeReindex.Global R (extended B) ≃ₐ[R]
      FrozenExchangeReindex.Global R (extended (RectangularMutationSplitting.matrix B k))

#print axioms extended
#print axioms Standard
end Verification.BFZForestMutationInput
