/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittSectionCoordinates
import Verification.OriginalWittOutsideBits
import Verification.OriginalASMonomialUnits
import Verification.WittSignedCharacters

/-!
# Original Witt Monomial Comparison

The term isomorphism sends every genuine original character to its
one-dimensional Witt form. All maps are the actual chart maps.
-/
noncomputable section
open scoped Classical TensorProduct
namespace Verification.OriginalWittMonomialComparison
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput Verification.OriginalWittSectionCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,FrozenAcyclicCover.earlierWeights κ n B i j=0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j=0)
variable (hI : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I)
variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (D : Symbols R W)
variable (T : TorusBasis R W D) (H : WittSheafAffineInvariance.Standard R W)

theorem torusToStratum_apply (a : RingSection W
    (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))) :
    torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H a =
      pullback W (OriginalASMonomialUnits.inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom a := by
  change pullback W (ExplicitStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm.toRingEquiv.toRingHom
    (pullback W MvPolynomial.C a) = _
  exact (DFunLike.congr_fun (WittSheafAffineInvariance.pullback_comp W MvPolynomial.C
    (ExplicitStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI).symm.toRingEquiv.toRingHom) a).symm

theorem torusToStratum_coefficient (a : RingSection W R) :
    torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H
      (pullback W (algebraMap R (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))) a) =
      pullback W (algebraMap R (GlobalNormalFrame.ZeroLayer R κ n I B)) a := by
  rw [torusToStratum_apply]
  have hc : (OriginalASMonomialUnits.inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom.comp
      (algebraMap R (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))) =
      algebraMap R (GlobalNormalFrame.ZeroLayer R κ n I B) := by
    ext x
    exact (OriginalASMonomialUnits.inclusion R κ n I B hf hs hpos hneg hsupport hI).commutes x
  have h := DFunLike.congr_fun (WittSheafAffineInvariance.pullback_comp W
    (algebraMap R (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B))))
    (OriginalASMonomialUnits.inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom) a
  rw [hc] at h
  exact h.symm

theorem torusToStratum_form (u : (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))ˣ) :
    torusToStratum R κ n I B hf hs hpos hneg hsupport hI W H
      (form R W D (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
        (TorusSmooth.torus_smooth R (Fin (ExplicitStratumTorus.torusRank κ n I B))) u) =
    form R W D _ (OriginalASMonomialUnits.smooth R κ n I B hf hs hpos hneg hsupport hI)
      (Units.map (OriginalASMonomialUnits.inclusion R κ n I B hf hs hpos hneg hsupport hI).toRingHom.toMonoidHom u) := by
  rw [torusToStratum_apply]
  exact form_natural R W D _ _ _ _ _ u

theorem signedUnit_form (m : (IndependentChartIndex.Other n I ⊕ κ) →₀ ℤ) :
    form R W D (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
        (TorusSmooth.torus_smooth R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
      (OriginalASMonomialUnits.signedUnit R κ n I B hf hs m) =
    (((PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne
      (fun _ : I => (-1:ℤˣ)) (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).1) : ℤ) :
        RingSection W (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B))))) *
      form R W D (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
        (TorusSmooth.torus_smooth R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
        ((MonoidAlgebra.of R (Multiplicative (Fin (ExplicitStratumTorus.torusRank κ n I B) →₀ ℤ))).toHomUnits
          (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).2)) := by
  rw [OriginalASMonomialUnits.signedUnit,map_mul]
  congr 1
  have h := form_natural R W D R
    (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
    (WittSignedCharacters.smoothBase R) (TorusSmooth.torus_smooth R _)
    (Algebra.ofId R (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B))))
    (PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (fun _ : I => (-1:Rˣ))
      (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).1))
  rw [WittSignedCharacters.scalar_character_apply,map_intCast] at h
  exact h.symm

theorem original_monomial (m : (IndependentChartIndex.Other n I ⊕ κ) →₀ ℤ) :
    equiv R κ n I B hf hs hpos hneg hsupport hI W D T H
      (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd
        (OriginalWittOutsideBits.exponent κ n I m))) ⊗ₜ[ℤ] (1 : RingSection W R)) =
    form R W D _ (OriginalASMonomialUnits.smooth R κ n I B hf hs hpos hneg hsupport hI)
      (OriginalASMonomialUnits.unit R κ n I B hf hs hpos hneg hsupport hI m) := by
  rw [OriginalWittSectionCoordinates.monomial,OriginalWittOutsideBits.sign_exponent,
    OriginalWittOutsideBits.splitting_exponent]
  simp only [zsmul_eq_mul,mul_one]
  rw [WittTorusCharacters.basis_single,map_intCast]
  have h : WittTorusCharacters.character R W D
      (Fin (ExplicitStratumTorus.torusRank κ n I B))
      (Multiplicative.ofAdd (fun j => ((ExplicitStratumTorus.splitting κ n I B hf hs m).2 j : ZMod 2))) =
    form R W D (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
      (TorusSmooth.torus_smooth R _)
      ((MonoidAlgebra.of R (Multiplicative (Fin (ExplicitStratumTorus.torusRank κ n I B) →₀ ℤ))).toHomUnits
        (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).2)) :=
    DFunLike.congr_fun (WittTorusCharacters.integral_character R W D
      (Fin (ExplicitStratumTorus.torusRank κ n I B)))
      (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).2)
  erw [h]
  rw [← signedUnit_form R κ n I B hf hs W D m,torusToStratum_form]
  rfl

theorem original_monomial_coefficient (m : (IndependentChartIndex.Other n I ⊕ κ) →₀ ℤ)
    (a : RingSection W R) :
    equiv R κ n I B hf hs hpos hneg hsupport hI W D T H
      (Ideal.Quotient.mk _ (MonoidAlgebra.of ℤ _ (Multiplicative.ofAdd
        (OriginalWittOutsideBits.exponent κ n I m))) ⊗ₜ[ℤ] a) =
    form R W D _ (OriginalASMonomialUnits.smooth R κ n I B hf hs hpos hneg hsupport hI)
      (OriginalASMonomialUnits.unit R κ n I B hf hs hpos hneg hsupport hI m) *
        pullback W (algebraMap R (GlobalNormalFrame.ZeroLayer R κ n I B)) a := by
  rw [OriginalWittSectionCoordinates.monomial,OriginalWittOutsideBits.sign_exponent,
    OriginalWittOutsideBits.splitting_exponent,WittTorusCharacters.basis_single,map_zsmul,zsmul_eq_mul]
  have h : WittTorusCharacters.character R W D
      (Fin (ExplicitStratumTorus.torusRank κ n I B))
      (Multiplicative.ofAdd (fun j => ((ExplicitStratumTorus.splitting κ n I B hf hs m).2 j : ZMod 2))) =
    form R W D (OriginalTorus.Torus R (Fin (ExplicitStratumTorus.torusRank κ n I B)))
      (TorusSmooth.torus_smooth R _)
      ((MonoidAlgebra.of R (Multiplicative (Fin (ExplicitStratumTorus.torusRank κ n I B) →₀ ℤ))).toHomUnits
        (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).2)) :=
    DFunLike.congr_fun (WittTorusCharacters.integral_character R W D
      (Fin (ExplicitStratumTorus.torusRank κ n I B)))
      (Multiplicative.ofAdd (ExplicitStratumTorus.splitting κ n I B hf hs m).2)
  erw [h]
  rw [mul_right_comm,← signedUnit_form R κ n I B hf hs W D m,map_mul,
    torusToStratum_form,torusToStratum_coefficient]
  rfl

#print axioms original_monomial_coefficient

#print axioms original_monomial

#print axioms torusToStratum_coefficient
#print axioms torusToStratum_apply
#print axioms torusToStratum_form
#print axioms signedUnit_form
end Verification.OriginalWittMonomialComparison
