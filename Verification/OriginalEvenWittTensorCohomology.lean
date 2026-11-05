/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalEvenWittGraph
import Verification.GraphTensorCohomology
import Verification.OriginalWittTensorTerms

/-!
# Original Even Witt Tensor Cohomology

The original even exchange Witt tensor complex computes the full
uncompressed direct product of actual augmented independence cohomology
blocks, with arbitrary abelian coefficients and all torsion retained.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalEvenWittTensorCohomology
open CategoryTheory Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (c : Fin n → κ)
variable (hm : ∀ a i : Fin n, Even (B (Sum.inl a) (Sum.inl i)))
variable (hc : ∀ a i, B (Sum.inr a) (Sum.inl i) = if c i = a then 1 else 0)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hclique : ∀ a i : Fin n, a ≠ i → c a = c i → B (Sum.inl a) (Sum.inl i) ≠ 0)
variable (A : Type) [AddCommGroup A]

def cohomologyIso (p : ℕ) :
    (OriginalWittTensorTerms.complex κ n B A hpos hneg hsupport).homology p ≅
      ModuleCat.of ℤ ((SF : Finset (Fin n) × Finset κ) →
        (GraphTensorCohomology.simplex (OriginalEvenWittGraph.graph κ n B) c A SF).homology p) :=
  (((IntegerTensorExtension.functor ℤ A).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) p).mapIso
      (OriginalEvenWittGraph.iso κ n B c hm hc hpos hneg hsupport hclique)).trans
    (GraphTensorCohomology.uncompressedHomologyIso (OriginalEvenWittGraph.graph κ n B) c A p)

#print axioms cohomologyIso
end Verification.OriginalEvenWittTensorCohomology
