/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExplicitStratumCoordinates
import Verification.TorusSmooth
import Verification.SignedPrimitiveFiberUnits

/-!
# Original AS Monomial Units

Actual original coordinate units through the fixed integral AS torus
chart. Their scalar and monomial parts use that chart's same splitting.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 15000
namespace Verification.OriginalASMonomialUnits
open Verification.IndependentChartIndex Verification.ExplicitStratumTorus
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

def signedUnit (m : (Other n I ⊕ κ) →₀ ℤ) :
    (OriginalTorus.Torus R (Fin (torusRank κ n I B)))ˣ :=
  Units.map (algebraMap R _).toMonoidHom
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : I => (-1:Rˣ))
      (Multiplicative.ofAdd (splitting κ n I B hf hs m).1)) *
    (MonoidAlgebra.of R (Multiplicative (Fin (torusRank κ n I B) →₀ ℤ))).toHomUnits
      (Multiplicative.ofAdd (splitting κ n I B hf hs m).2)

#print axioms signedUnit

theorem fiber_monomial (m : (Other n I ⊕ κ) →₀ ℤ) :
    fiberEquiv R κ n I B hf hs (Ideal.Quotient.mk _
      (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) =
        (signedUnit R κ n I B hf hs m : OriginalTorus.Torus R (Fin (torusRank κ n I B))) := by
  exact SignedPrimitiveFiberUnits.monomial (GlobalExchangeSmooth.selectedMap κ n B I) hf hs
    (fun _ => (-1:Rˣ)) _ (ActualTransversePairSmooth.fiberIdeal_eq R
      (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)) m

#print axioms fiber_monomial

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

def inclusion : OriginalTorus.Torus R (Fin (torusRank κ n I B)) →ₐ[R]
    GlobalNormalFrame.ZeroLayer R κ n I B :=
  (affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R _
      (MvPolynomial (Selected n I) (OriginalTorus.Torus R (Fin (torusRank κ n I B)))))

def unit (m : (Other n I ⊕ κ) →₀ ℤ) : (GlobalNormalFrame.ZeroLayer R κ n I B)ˣ :=
  Units.map (inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom.toMonoidHom
    (signedUnit R κ n I B hf hs m)

theorem unit_original (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    (unit R κ n I B hf hs hpos hneg hsupport hI
      (Finsupp.single (GlobalSelectedColumns.rowEquiv κ n I a) 1) :
        GlobalNormalFrame.ZeroLayer R κ n I B) = ExplicitStratumCoordinates.original R κ n I B a.val := by
  apply (affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).injective
  change affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI
    ((affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm
      (MvPolynomial.C _)) = _
  rw [AlgEquiv.apply_symm_apply,ExplicitStratumCoordinates.affineTorusEquiv_original]
  congr 1
  exact (fiber_monomial R κ n I B hf hs _).symm

def smooth : Algebra.Smooth R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
  let U := OriginalTorus.Torus R (Fin (torusRank κ n I B))
  letI : Algebra.Smooth R U := TorusSmooth.torus_smooth R _
  letI : Algebra.Smooth U (MvPolynomial (Selected n I) U) := {}
  letI : Algebra.Smooth R (MvPolynomial (Selected n I) U) := Algebra.Smooth.comp R U _
  exact Algebra.Smooth.of_equiv (affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm

#print axioms inclusion
#print axioms unit
#print axioms unit_original
#print axioms smooth
end Verification.OriginalASMonomialUnits
