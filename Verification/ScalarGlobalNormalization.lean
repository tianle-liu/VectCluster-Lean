/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalScaling
import Verification.SplitScalarCharacters
import Verification.UnitScaledLocalization

/-!
# Scalar Global Normalization

An integral left inverse of the original extended columns constructs an
actual simultaneous scalar-normalization algebra equivalence. Mutable originals
remain polynomial; localization is performed only at the specified frozen set.
-/
noncomputable section
namespace Verification.ScalarGlobalNormalization
open MvPolynomial
open Classical
variable (R : Type*) [CommRing R]
variable {ρ σ κ : Type*} [Fintype ρ] [Fintype σ]
variable (j : σ → ρ) (B : Matrix ρ σ ℤ) (L : (ρ → ℤ) →ₗ[ℤ] (σ → ℤ))
variable (hL : L.comp B.mulVecLin=LinearMap.id) (a b : σ → Rˣ)

abbrev Presentation := MvPolynomial σ (MvPolynomial ρ R) ⧸ ScalarExchangeRelabel.relations R j B a b
abbrev Normalized := MvPolynomial σ (MvPolynomial ρ R) ⧸ ExchangeRelabel.relations R j B

def quotientEquiv : Presentation R j B a b ≃ₐ[R] Normalized R j B :=
  ScalarGlobalScaling.quotientEquiv R j B a b (SplitScalarCharacters.constants L a b)
    (SplitScalarCharacters.balance B L hL a b)

def original (r : ρ) : Presentation R j B a b := Ideal.Quotient.mk _ (C (X r))
def mutated (i : σ) : Presentation R j B a b := Ideal.Quotient.mk _ (X i)

theorem quotient_original (r : ρ) : quotientEquiv R j B L hL a b (original R j B a b r)=
    algebraMap R _ (SplitScalarCharacters.constants L a b r : R)*ExchangeRelabel.original R j B r :=
  ScalarGlobalScaling.quotient_original R j B a b (SplitScalarCharacters.constants L a b)
    (SplitScalarCharacters.balance B L hL a b) r

theorem quotient_mutated (i : σ) : quotientEquiv R j B L hL a b (mutated R j B a b i)=
    algebraMap R _ (ScalarGlobalScaling.partner R j B a (SplitScalarCharacters.constants L a b) i : R)*
      Ideal.Quotient.mk (ExchangeRelabel.relations R j B) (X i) := by
  change Ideal.Quotient.mk _ (ScalarGlobalScaling.ambient R j B a
    (SplitScalarCharacters.constants L a b) (X i))=_
  rw [ScalarGlobalScaling.ambient_X,map_mul]
  rfl

variable (frozen : κ → ρ)
abbrev Global := UnitScaledLocalization.Loc (fun k=>original R j B a b (frozen k))
abbrev NormalGlobal := ExchangeRelabel.Localized R j B frozen

def globalEquiv : Global R j B a b frozen ≃ₐ[R] NormalGlobal R j B frozen :=
  UnitScaledLocalization.equiv (quotientEquiv R j B L hL a b)
    (fun k=>original R j B a b (frozen k)) (fun k=>ExchangeRelabel.original R j B (frozen k))
      (fun k=>Units.map (algebraMap R (Normalized R j B)).toMonoidHom
        (SplitScalarCharacters.constants L a b (frozen k)))
          (fun k=>quotient_original R j B L hL a b (frozen k))

theorem global_original (r : ρ) :
    globalEquiv R j B L hL a b frozen
      (algebraMap (Presentation R j B a b) _ (original R j B a b r))=
    algebraMap R _ (SplitScalarCharacters.constants L a b r : R)*
      algebraMap (Normalized R j B) _ (ExchangeRelabel.original R j B r) := by
  change UnitScaledLocalization.equiv _ _ _ _ _ (algebraMap _ _ _)=_
  rw [UnitScaledLocalization.equiv_algebraMap,quotient_original,map_mul]
  rfl

theorem global_mutated (i : σ) :
    globalEquiv R j B L hL a b frozen
      (algebraMap (Presentation R j B a b) _ (mutated R j B a b i))=
    algebraMap R _ (ScalarGlobalScaling.partner R j B a (SplitScalarCharacters.constants L a b) i : R)*
      algebraMap (Normalized R j B) _ (Ideal.Quotient.mk (ExchangeRelabel.relations R j B) (X i)) := by
  change UnitScaledLocalization.equiv _ _ _ _ _ (algebraMap _ _ _)=_
  rw [UnitScaledLocalization.equiv_algebraMap,quotient_mutated,map_mul]
  rfl

#print axioms Presentation
#print axioms Normalized
#print axioms quotientEquiv
#print axioms original
#print axioms mutated
#print axioms quotient_original
#print axioms quotient_mutated
#print axioms Global
#print axioms NormalGlobal
#print axioms globalEquiv
#print axioms global_original
#print axioms global_mutated
end Verification.ScalarGlobalNormalization
