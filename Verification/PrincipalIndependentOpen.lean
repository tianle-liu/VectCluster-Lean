/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenAcyclicCover
import Verification.ExchangeReindex
import Verification.EmptyColumnRetraction

/-!
# Principal Independent Open

Order-independent zero principal submatrices are independent for the
actual later-weight graph, without an additional diagonal or sign hypothesis.
-/
namespace Verification.PrincipalIndependentOpen
variable {F : Type} {n : ℕ}
variable (B : (Fin n⊕F)→(Fin n⊕Empty)→ℤ)

theorem independent (I : Finset (Fin n))
    (hI : ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I) :
    ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights F n B) I := by
  intro i hi j hj h
  rcases h with ⟨hij,h⟩|⟨hji,h⟩
  · apply h
    change (-B (Sum.inl j) (Sum.inl i)).toNat=0
    have hz := hI j hj i hi (ne_of_gt hij)
    change B (Sum.inl j) (Sum.inl i)=0 at hz
    rw [hz]
    rfl
  · apply h
    change (-B (Sum.inl i) (Sum.inl j)).toNat=0
    have hz := hI i hi j hj (ne_of_gt hji)
    change B (Sum.inl i) (Sum.inl j)=0 at hz
    rw [hz]
    rfl

#print axioms independent
end Verification.PrincipalIndependentOpen
