/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualCellTerms
import Verification.CoordinatePairEquiv
import Verification.TorusThomInput

/-!
# Actual Torus Thom

The standard torus--Thom computation is applied to the actual original
strata using their proved coefficient-preserving affine--torus ring
isomorphisms. Normal coordinates are preserved, so the resulting degrees
and symbol multiplicities are those of the genuine cellular source.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace Verification.ActualTorusThom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.ActualCellThom Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex Verification.IndependentStratumTorus
attribute [local instance] Abelian.hasFiniteBiproducts MvPolynomial.algebraMvPolynomial
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (P : CoordinatePurityInput.StandardPurity R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (Z : C) (K : ℕ → C) (T : TorusThomInput.StandardTorusThom R G Z K)

def normalRingEquiv (r : ℕ) (i : Index κ n B r) :
    MvPolynomial (Selected n i.val) (GlobalNormalFrame.ZeroLayer R κ n i.val B) ≃ₐ[R]
      TorusThomInput.NormalRing R (Selected n i.val) (Selected n i.val) (Fin (torusRank κ n i.val B)) :=
  MvPolynomial.mapAlgEquiv (Selected n i.val)
    (affineTorusEquiv R κ n i.val B (hf i.val i.property.2) (hs i.val i.property.2)
      hpos hneg hsupport i.property.2)

def thomIso (r : ℕ) (i : Index κ n B r) :
    localThom G R κ n B r i ≅
      TorusThomInput.thom R (Selected n i.val) (Selected n i.val) (Fin (torusRank κ n i.val B)) G :=
  CoordinatePairEquiv.relativeIso MvPolynomial.X MvPolynomial.X
    (normalRingEquiv R κ n B hpos hneg hsupport hf hs r i).toRingEquiv
    (fun j => by exact MvPolynomial.map_X _ j) G

def localSymbolsIso (r : ℕ) (i : Index κ n B r) :
    ActualCellTerms.localTerm G R κ n B r i ≅
      ⨁ fun A : Finset (Fin (torusRank κ n i.val B)) => if r + A.card = 0 then Z else K (r + A.card) :=
  (DerivedCategory.homologyFunctor C (-(r : ℤ))).mapIso
    (thomIso G R κ n B hpos hneg hsupport hf hs r i) ≪≫ (by
      have hc : Fintype.card (Selected n i.val) = r := (Fintype.card_coe i.val).trans i.property.1
      simpa only [TorusThomInput.symbolTerms,hc] using
        T.homologyIso (Selected n i.val) (Selected n i.val) (Fin (torusRank κ n i.val B)))

include hpos hneg hsupport hf hs T in
omit [Nontrivial R] in
theorem local_concentrated (r : ℕ) (i : Index κ n B r) (q : ℤ) (hq : q ≠ -(r : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor C q).obj (localThom G R κ n B r i)) := by
  have hc : Fintype.card (Selected n i.val) = r := (Fintype.card_coe i.val).trans i.property.1
  have hz := T.concentrated (Selected n i.val) (Selected n i.val)
    (Fin (torusRank κ n i.val B)) q (by simpa only [hc] using hq)
  exact ((DerivedCategory.homologyFunctor C q).mapIso
    (thomIso G R κ n B hpos hneg hsupport hf hs r i)).isZero_iff.mpr hz

def termIso (r : ℕ) : (GeometricCellularSource.source R G κ n B).X r ≅
    ⨁ fun i : Index κ n B r => ⨁ fun A : Finset (Fin (torusRank κ n i.val B)) => if r + A.card = 0 then Z else K (r + A.card) :=
  ActualCellTerms.termIso G E R κ n B P hpos hneg hsupport hf hs r ≪≫
    biproduct.mapIso (localSymbolsIso G R κ n B hpos hneg hsupport hf hs Z K T r)

include hf hs in
omit [CommRing R] [Nontrivial R] in
theorem torus_dimension (r : ℕ) (i : Index κ n B r) :
    torusRank κ n i.val B + 2 * r = n + Fintype.card κ := by
  simpa only [i.property.1] using
    rank_formula κ n i.val B (hf i.val i.property.2) (hs i.val i.property.2)

#print axioms normalRingEquiv
#print axioms thomIso
#print axioms localSymbolsIso
#print axioms local_concentrated
#print axioms termIso
#print axioms torus_dimension
end Verification.ActualTorusThom
