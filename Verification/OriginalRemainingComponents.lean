/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingLattice
import Verification.SmithComponents

/-!
# Original Remaining Components

Under (AR), the coefficient ring left after retaining the original
free mutable coordinates is a finite product of Laurent domains over
finite separable field extensions.
-/
noncomputable section
namespace Verification.OriginalRemainingComponents
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
open Verification.OriginalRemainingLattice
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

theorem remainingIdeal_eq : remainingIdeal R κ n I B=
    PrimitiveCharacters.prescribedIdeal (R := R) (remainingMap κ n I B)
      Finsupp.basisSingleOne (fun _=>-1) := by
  unfold remainingIdeal FreeCharacterFactor.coefficientIdeal
    ProductCharacterQuotient.coefficientIdeal PrimitiveCharacters.prescribedIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MonoidAlgebra.of R _ (Multiplicative.ofAdd
    ((splitting κ n I B) (ActualOpenChart.column (Selected n I) (Other n I⊕κ)
      (Other n I) (matrix κ n I B) i)).2) - algebraMap R _ (-1) =
    MonoidAlgebra.of R _ (Multiplicative.ofAdd
      ((splitting κ n I B) (GlobalExchangeSmooth.selectedMap κ n B I (Finsupp.single i 1))).2) -
      algebraMap R _ (-1)
  simp only [GlobalExchangeSmooth.selectedMap,ActualOpenGeometry.columnMap_single]

theorem separable_product
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) {m : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
    (he : ∀ i,IsUnit ((s.a i).natAbs:R)) :
    ∃ (J : Type) (_ : Finite J) (L : J→Type) (_ : ∀ j,Field (L j))
      (_ : ∀ j,Algebra R (L j)) (K : Type) (_ : Finite K)
      (_ : RemainingRing R κ n I B ≃ₐ[R] ∀ j,OriginalTorus.Torus (L j) K),
      ∀ j,Module.Finite R (L j) ∧ Algebra.IsSeparable R (L j) := by
  classical
  letI : Fintype (RemainingIndex κ n I B) := Fintype.ofFinite _
  obtain ⟨l,t⟩ := (LinearMap.range (remainingMap κ n I B)).smithNormalForm Finsupp.basisSingleOne
  obtain ⟨J,hJ,L,hL,aL,e,hsep⟩ := SmithComponents.character_separable_product
    (remainingMap κ n I B) (remaining_injective κ n I B hf) Finsupp.basisSingleOne t
    (remaining_tame κ n I B R hf s t he)
  letI := hJ
  letI := hL
  letI := aL
  refine ⟨J,hJ,L,hL,aL,
    PartialPowerProduct.FreeIndex (GlobalSmithStratum.smithEmbedding (remainingMap κ n I B) t),
    inferInstance,?_,hsep⟩
  exact (Ideal.quotientEquivAlgOfEq R (remainingIdeal_eq R κ n I B)).trans e

#print axioms remainingIdeal_eq
#print axioms separable_product
end Verification.OriginalRemainingComponents
