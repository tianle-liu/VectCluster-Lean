/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalASFullUnitCharacter
import Verification.OriginalSourceLaurentGenerators

/-!
# Original AS Adjacent Unit Character

Factorization of every original-lattice unit under the genuine adjacent
source map. The parameter exponent is the literal removed-coordinate entry;
the coefficient is the literal canonical projection of the target unit.
-/
noncomputable section
open scoped Classical
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
namespace Verification.OriginalASAdjacentUnitCharacter
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (hD : ∀ l i : Selected n J, IndependentChartIndex.matrix κ n J B (Sum.inl l) (Sum.inl i)=0)
variable (hfI : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B (J.erase v.val)))
variable (hsI : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B (J.erase v.val))))
variable (hfJ : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hsJ : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (laterWeights κ n B) (J.erase v.val))
variable (hJ : ExchangeOpenCover.Independent (laterWeights κ n B) J)
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n J) (Other n J ⊕ κ) (Other n J) (IndependentChartIndex.matrix κ n J B))
local notation "L" => LaurentBasepoint.Laurent New
local notation "CI" => OriginalASFullUnitCharacter.character κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI
local notation "CJ" => OriginalASFullUnitCharacter.character κ n J R B hfJ hsJ hpos hneg hsupport hJ
local notation "src" => OriginalSourceLaurentGenerators.map R κ n J B v hD
local notation "proj" => OriginalCanonicalFiberProjection.projection R κ n J B hpos hneg hsupport hJ

def parameterCharacter : Multiplicative ((Fin n ⊕ κ) →₀ ℤ) →* Lˣ where
  toFun m := (LaurentPolynomialUniversal.parameterUnit New) ^ (Multiplicative.toAdd m (Sum.inl v.val))
  map_one' := zpow_zero _
  map_mul' _ _ := zpow_add _ _ _

def coefficientCharacter : Multiplicative ((Fin n ⊕ κ) →₀ ℤ) →* Lˣ :=
  (Units.map (algebraMap New L).toMonoidHom).comp
    ((Units.map (proj).toRingHom.toMonoidHom).comp CJ)

theorem parameter_basis :
    Units.map (src).toRingHom.toMonoidHom (CI (Multiplicative.ofAdd (Finsupp.single (Sum.inl v.val) 1))) =
      LaurentPolynomialUniversal.parameterUnit New := by
  apply Units.ext
  change src (CI (Multiplicative.ofAdd (Finsupp.single (Sum.inl v.val) 1)) : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B)=_
  rw [OriginalASFullUnitCharacter.original κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI (a := ⟨Sum.inl v.val,by
    intro w hw he
    exact (Finset.mem_erase.mp hw).1 (Sum.inl.inj he).symm⟩)]
  exact (OriginalSourceLaurentGenerators.parameter R κ n J B v hD).trans LaurentPolynomialUniversal.parameterUnit_val.symm

theorem remaining_basis (a : AnticliqueSubcolumns.Rows (C := κ) J) :
    Units.map (src).toRingHom.toMonoidHom (CI (Multiplicative.ofAdd (Finsupp.single a.val 1))) =
      coefficientCharacter R κ n J B hfJ hsJ hpos hneg hsupport hJ
        (Multiplicative.ofAdd (Finsupp.single a.val 1)) := by
  apply Units.ext
  change src (CI (Multiplicative.ofAdd (Finsupp.single a.val 1)) : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B)=
    algebraMap New L (proj (CJ (Multiplicative.ofAdd (Finsupp.single a.val 1))))
  rw [OriginalASFullUnitCharacter.original κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI (a := ⟨a.val,fun w hw => a.property w (Finset.mem_of_mem_erase hw)⟩),
    OriginalASFullUnitCharacter.original κ n J R B hfJ hsJ hpos hneg hsupport hJ (a := a)]
  exact OriginalSourceLaurentGenerators.remaining R κ n J B v hD hpos hneg hsupport hJ a

theorem factorization :
    (Units.map (src).toRingHom.toMonoidHom).comp CI =
      parameterCharacter R κ n J B v * coefficientCharacter R κ n J B hfJ hsJ hpos hneg hsupport hJ := by
  apply MonoidHom.eq_of_eqOn_dense
  · exact PrimitiveCharacters.basis_generates Finsupp.basisSingleOne
  · rintro _ ⟨a,rfl⟩
    change Units.map (src).toRingHom.toMonoidHom (CI (Multiplicative.ofAdd (Finsupp.single a 1))) =
      (LaurentPolynomialUniversal.parameterUnit New) ^ ((Finsupp.single a (1:ℤ)) (Sum.inl v.val)) *
        coefficientCharacter R κ n J B hfJ hsJ hpos hneg hsupport hJ (Multiplicative.ofAdd (Finsupp.single a 1))
    by_cases hav : a=Sum.inl v.val
    · subst a
      rw [parameter_basis]
      simp only [Finsupp.single_eq_same,zpow_one]
      change _=_ * Units.map (algebraMap New L).toMonoidHom (Units.map (proj).toRingHom.toMonoidHom (CJ _))
      rw [OriginalASFullUnitCharacter.normal κ n J R B hfJ hsJ hpos hneg hsupport hJ (i := v),map_one,map_one,mul_one]
    · by_cases ha : ∃ w ∈ J,a=Sum.inl w
      · obtain ⟨w,hw,rfl⟩ := ha
        have hwI : w ∈ J.erase v.val := Finset.mem_erase.mpr ⟨fun h => hav (congrArg Sum.inl h),hw⟩
        rw [OriginalASFullUnitCharacter.normal κ n (J.erase v.val) R B hfI hsI hpos hneg hsupport hI (i := ⟨w,hwI⟩),map_one]
        change _=_ * Units.map (algebraMap New L).toMonoidHom (Units.map (proj).toRingHom.toMonoidHom (CJ _))
        rw [OriginalASFullUnitCharacter.normal κ n J R B hfJ hsJ hpos hneg hsupport hJ (i := ⟨w,hw⟩),map_one,map_one]
        simp [Finsupp.single_apply,hav]
      · have har : ∀ w ∈ J,a ≠ Sum.inl w := by
          intro w hw he
          exact ha ⟨w,hw,he⟩
        rw [remaining_basis R κ n J B v hD hfI hsI hfJ hsJ hpos hneg hsupport hI hJ (a := ⟨a,har⟩)]
        simp [Finsupp.single_apply,hav]

theorem factorization_apply (m : (Fin n ⊕ κ) →₀ ℤ) :
    Units.map (src).toRingHom.toMonoidHom (CI (Multiplicative.ofAdd m)) =
      (LaurentPolynomialUniversal.parameterUnit New) ^ (m (Sum.inl v.val)) *
        Units.map (algebraMap New L).toMonoidHom
          (Units.map (proj).toRingHom.toMonoidHom (CJ (Multiplicative.ofAdd m))) :=
  DFunLike.congr_fun (factorization R κ n J B v hD hfI hsI hfJ hsJ hpos hneg hsupport hI hJ) (Multiplicative.ofAdd m)

#print axioms parameterCharacter
#print axioms coefficientCharacter
#print axioms parameter_basis
#print axioms remaining_basis
#print axioms factorization
#print axioms factorization_apply
end Verification.OriginalASAdjacentUnitCharacter
