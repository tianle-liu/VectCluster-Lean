/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestReorientation
import Verification.PathForestScalarNormalization
import Verification.OriginalScalarOne

/-!
# Path Forest Scalar Reorientation

Arbitrary nonzero scalar exchange coefficients are normalized internally
before the cited source/sink mutations. The final ring is the actual linear
path forest with the same mutable and frozen dimensions.
-/
noncomputable section
namespace Verification.PathForestScalarReorientation
open Verification.PathForestOrientation Verification.PathForestReorientation
variable (R : Type) [Field R]
variable {S F : Type} [Fintype S] [Fintype F]
variable (m : S→ℕ) (o : S→Bool) (a : S→ℕ→ℤˣ) (n : ℕ)
variable (e : Vertex m o≃Fin n) (B : Matrix (Fin n⊕F) (Fin n⊕Empty) ℤ)
variable (hprincipal : ∀i j,EmptyColumnRetraction.cut B (Sum.inl (e i)) (e j)=matrix m o a i j)
variable (hAS : ∀I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I→
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)
variable (Q : FZForestMutationInput.Standard) (H : BFZForestMutationInput.Standard R)

def algebraEquiv (u v : Fin n→Rˣ) : ScalarFrozenGlobal.Global R F n B u v ≃ₐ[R]
    FrozenAcyclicCover.Global R F n (linearMatrix m o a n e B hprincipal Q) :=
  (PathForestScalarNormalization.globalEquiv R m o (leftSigns m o a) (rightSigns m o a)
    n (linearLabel m o n e) B (parity_principal m o a n e B hprincipal) hAS u v).trans
    ((OriginalScalarOne.globalEquiv R F n B).symm.trans
      (PathForestReorientation.algebraEquiv m o a n e B hprincipal Q R H))

#print axioms algebraEquiv
end Verification.PathForestScalarReorientation
