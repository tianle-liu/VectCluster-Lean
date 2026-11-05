/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineComponentUnits
import Verification.OriginalRostStrata
import Verification.StratumComponents

/-!
# Original Stratum Units

Unique componentwise unit coordinates on the actual original
zero-stratum ring under tame rank. The field factors are the actual
connected factors of its Smith decomposition, and the affine variables
are removed by an internal polynomial-unit theorem.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalStratumUnits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable {m : ℕ} (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
variable (he : ∀ i,IsUnit ((sm.a i).natAbs : R))


open Verification.GlobalSmithStratum Verification.DiagonalPowerFibers Verification.PartialPowerProduct

include hpos hneg hsupport hI hf he in
theorem component_units :
    ∃ (J : Type) (_ : Finite J) (L : J→Type) (_ : ∀ j,Field (L j))
      (_ : ∀ j,Algebra R (L j))
      (e : GlobalNormalFrame.ZeroLayer R κ n I B ≃+*
        ∀ j,MvPolynomial (Selected n I)
          (OriginalTorus.Torus (L j) (FreeIndex (smithEmbedding (GlobalExchangeSmooth.selectedMap κ n B I) sm)))),
      Nonempty ((GlobalNormalFrame.ZeroLayer R κ n I B)ˣ ≃*
        ∀ j,(L j)ˣ × Multiplicative
          (FreeIndex (smithEmbedding (GlobalExchangeSmooth.selectedMap κ n B I) sm)→₀ℤ)) ∧
      (∀ j,Module.Finite R (L j) ∧ Algebra.IsSeparable R (L j)) ∧
      (∀ j (p : PrimeSpectrum (MvPolynomial (Selected n I)
        (OriginalTorus.Torus (L j) (FreeIndex (smithEmbedding (GlobalExchangeSmooth.selectedMap κ n B I) sm))))),
        connectedComponent (StratumComponents.componentMap _ e j p)=
          Set.range (StratumComponents.componentMap _ e j)) := by
  obtain ⟨J,hJ,L,hL,aL,e,hsep⟩ := SmithComponents.zero_stratum_separable_product
    (Sum.inl : Other n I→Other n I⊕κ) (matrix κ n I B)
    (IndependentChartIndex.matrix_zero_block κ n I B hpos hneg hsupport hI)
    (GlobalExchangeSmooth.selectedMap κ n B I) Finsupp.basisSingleOne
    (fun i => ActualOpenGeometry.columnMap_single (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B) i)
    hf sm he
  letI := hJ
  letI := hL
  letI := aL
  letI : Fintype (FreeIndex (smithEmbedding (GlobalExchangeSmooth.selectedMap κ n B I) sm)) := Fintype.ofFinite _
  let e' := (IndependentStratumCoordinates.originalStratumEquiv R κ n I B).trans e.toRingEquiv
  refine ⟨J,hJ,L,hL,aL,e',⟨AffineComponentUnits.transportCoordinates L (Selected n I) _ e'⟩,
    fun j => ⟨(hsep j).1,(hsep j).2.1⟩,?_⟩
  exact fun j p => StratumComponents.componentMap_component _ e' j p

#print axioms component_units
end Verification.OriginalStratumUnits
