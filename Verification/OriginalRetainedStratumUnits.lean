/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingComponents
import Verification.OriginalFreeTorusCoordinates
import Verification.AffineComponentUnits
import Verification.StratumComponents

/-!
# Original Retained Stratum Units

Unit coordinates for the actual stratum with A(I) retained in its
original coordinates. The coefficient units belong to Laurent domains
over finite separable fields, while the independent exponent vector is
indexed by precisely the named free mutable coordinates.
-/
noncomputable section
namespace Verification.OriginalRetainedStratumUnits
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔ FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

include hpos hneg hsupport hI in
theorem component_units
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) {m : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
    (he : ∀ i,IsUnit ((s.a i).natAbs:R)) :
    ∃ (J : Type) (_ : Finite J) (L : J→Type) (_ : ∀ j,Field (L j))
      (_ : ∀ j,Algebra R (L j)) (K : Type) (_ : Finite K)
      (E : GlobalNormalFrame.ZeroLayer R κ n I B ≃+*
        ∀ j,MvPolynomial (Selected n I)
          (OriginalTorus.Torus (OriginalTorus.Torus (L j) K) (FreeIndex κ n I B))),
      Nonempty ((GlobalNormalFrame.ZeroLayer R κ n I B)ˣ ≃*
        ∀ j,(OriginalTorus.Torus (L j) K)ˣ × Multiplicative (FreeIndex κ n I B→₀ℤ)) ∧
      (∀ j,Module.Finite R (L j) ∧ Algebra.IsSeparable R (L j)) ∧
      (∀ j (p : PrimeSpectrum (MvPolynomial (Selected n I)
        (OriginalTorus.Torus (OriginalTorus.Torus (L j) K) (FreeIndex κ n I B)))),
        connectedComponent (StratumComponents.componentMap _ E j p)=
          Set.range (StratumComponents.componentMap _ E j)) := by
  classical
  obtain ⟨J,hJ,L,hL,aL,K,hK,e,hsep⟩ :=
    OriginalRemainingComponents.separable_product R κ n I B hf s he
  letI := hJ
  letI := hL
  letI := aL
  letI := hK
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype (FreeIndex κ n I B) := Fintype.ofFinite _
  let D : J→Type := fun j=>OriginalTorus.Torus (L j) K
  let eT := (MonoidAlgebraProducts.coefficientEquiv (G := Multiplicative (FreeIndex κ n I B→₀ℤ)) e).trans
    (MonoidAlgebraProducts.productEquiv R (Multiplicative (FreeIndex κ n I B→₀ℤ)) D)
  let E := ((stratumEquiv R κ n I B hpos hneg hsupport hI).trans
    (MvPolynomial.mapAlgEquiv (R := R) (Selected n I) eT)).trans
    (SmithComponents.polynomialProductEquiv (R := R) (I := Selected n I)
      (fun j=>OriginalTorus.Torus (D j) (FreeIndex κ n I B)))
  refine ⟨J,hJ,L,hL,aL,K,hK,E.toRingEquiv,
    ⟨AffineComponentUnits.transportCoordinates D (Selected n I) (FreeIndex κ n I B) E.toRingEquiv⟩,
    hsep,?_⟩
  exact fun j p=>StratumComponents.componentMap_component _ E.toRingEquiv j p

#print axioms component_units
end Verification.OriginalRetainedStratumUnits
