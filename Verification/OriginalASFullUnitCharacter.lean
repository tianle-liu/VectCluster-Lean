/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignedPrimitiveUnitCharacter
import Verification.OriginalWittNormalRemoval

/-!
# Original AS Full Unit Character

Extend the original nonvanishing-coordinate character to the full
initial-coordinate lattice by sending each normal coordinate to 1.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalASFullUnitCharacter
open Verification.IndependentChartIndex
variable (κ : Type) [Fintype κ] (n : ℕ) (I : Finset (Fin n))

def restriction : ((Fin n ⊕ κ) →₀ ℤ) →ₗ[ℤ] ((Other n I ⊕ κ) →₀ ℤ) :=
  (LinearMap.snd ℤ (Selected n I →₀ ℤ) ((Other n I ⊕ κ) →₀ ℤ)).comp
    ((Finsupp.sumFinsuppLEquivProdFinsupp ℤ).toLinearMap.comp
      (Finsupp.domLCongr (originals κ n I)).toLinearMap)

omit [Fintype κ] in
theorem restriction_apply (x : (Fin n ⊕ κ) →₀ ℤ) (a : Other n I ⊕ κ) :
    restriction κ n I x a = x ((originals κ n I).symm (Sum.inr a)) := rfl

omit [Fintype κ] in
theorem restriction_normal (i : I) : restriction κ n I (Finsupp.single (Sum.inl i.val) 1) = 0 := by
  ext a
  rw [restriction_apply]
  have hn : (originals κ n I).symm (Sum.inr a) ≠ Sum.inl i.val := by
    intro h
    have hh := congrArg (originals κ n I) h
    rw [Equiv.apply_symm_apply] at hh
    have hi : originals κ n I (Sum.inl i.val)=Sum.inl i :=
      (originals κ n I).apply_symm_apply (Sum.inl i)
    rw [hi] at hh
    cases hh
  simp [Finsupp.single_apply,Ne.symm hn]

omit [Fintype κ] in
theorem restriction_outside (a : Other n I ⊕ κ) :
    restriction κ n I (Finsupp.single ((originals κ n I).symm (Sum.inr a)) 1) = Finsupp.single a 1 := by
  ext b
  rw [restriction_apply]
  simp [Finsupp.single_apply,Equiv.apply_eq_iff_eq]

variable (R : Type) [CommRing R]
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)

def character : Multiplicative ((Fin n ⊕ κ) →₀ ℤ) →* (GlobalNormalFrame.ZeroLayer R κ n I B)ˣ :=
  (OriginalASUnitCharacter.character R κ n I B hf hs hpos hneg hsupport hI).comp
    (restriction κ n I).toAddMonoidHom.toMultiplicative

theorem normal (i : I) : character κ n I R B hf hs hpos hneg hsupport hI
    (Multiplicative.ofAdd (Finsupp.single (Sum.inl i.val) 1)) = 1 := by
  change OriginalASUnitCharacter.character R κ n I B hf hs hpos hneg hsupport hI
    (Multiplicative.ofAdd (restriction κ n I _)) = _
  simp only [toAdd_ofAdd]
  rw [restriction_normal]
  exact map_one _

theorem outside (a : Other n I ⊕ κ) :
    character κ n I R B hf hs hpos hneg hsupport hI
      (Multiplicative.ofAdd (Finsupp.single ((originals κ n I).symm (Sum.inr a)) 1)) =
      OriginalASMonomialUnits.unit R κ n I B hf hs hpos hneg hsupport hI (Finsupp.single a 1) := by
  change OriginalASUnitCharacter.character R κ n I B hf hs hpos hneg hsupport hI
    (Multiplicative.ofAdd (restriction κ n I _)) = _
  simp only [toAdd_ofAdd]
  rw [restriction_outside]
  rfl

theorem original (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    (character κ n I R B hf hs hpos hneg hsupport hI
      (Multiplicative.ofAdd (Finsupp.single a.val 1)) : GlobalNormalFrame.ZeroLayer R κ n I B) =
        ExplicitStratumCoordinates.original R κ n I B a.val := by
  have ha : (originals κ n I).symm (Sum.inr (GlobalSelectedColumns.rowEquiv κ n I a)) = a.val := by
    apply (originals κ n I).injective
    rw [Equiv.apply_symm_apply,ExplicitStratumCoordinates.row_originals]
  rw [← ha,outside]
  rw [OriginalASMonomialUnits.unit_original,ha]

def integerVector (a : OriginalWittQuotient.Bits (Fin n) κ) : (Fin n ⊕ κ) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

theorem integerVector_restriction (a : OriginalWittQuotient.Bits (Fin n) κ) :
    restriction κ n I (integerVector κ n a) = OriginalWittNormalRemoval.integerOutside κ n I a := by
  ext i
  rw [restriction_apply]
  rfl

theorem integerVector_character (a : OriginalWittQuotient.Bits (Fin n) κ) :
    character κ n I R B hf hs hpos hneg hsupport hI (Multiplicative.ofAdd (integerVector κ n a)) =
      OriginalASMonomialUnits.unit R κ n I B hf hs hpos hneg hsupport hI
        (OriginalWittNormalRemoval.integerOutside κ n I a) := by
  change OriginalASUnitCharacter.character R κ n I B hf hs hpos hneg hsupport hI
    (Multiplicative.ofAdd (restriction κ n I (integerVector κ n a))) = _
  rw [integerVector_restriction]
  rfl

#print axioms restriction
#print axioms restriction_apply
#print axioms restriction_normal
#print axioms restriction_outside
#print axioms character
#print axioms normal
#print axioms outside
#print axioms original
#print axioms integerVector
#print axioms integerVector_restriction
#print axioms integerVector_character
end Verification.OriginalASFullUnitCharacter
