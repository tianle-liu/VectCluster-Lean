/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellIsoTransport
import Verification.StrictLocalizedCells
import Verification.OrderedThomSections

/-!
# Strict Localized Coordinate Transport

Explicit coordinate presentations induce actual strict-cell term
isomorphisms. This transport uses the increasing original normal numbering
and an arbitrary supplied base algebra isomorphism; no boundary comparison
is part of the construction.
-/
noncomputable section
namespace Verification.StrictLocalizedCoordinateTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (r : ℕ) (i : ActualCellThom.Index κ n B r)
variable (τ α : Type) [Fintype τ] [Fintype α]
variable (e : GlobalNormalFrame.ZeroLayer R κ n i.val B ≃ₐ[R] TorusThomInput.BaseRing R τ α)

def thomIso : ActualCellThom.localThom G R κ n B r i ≅
    TorusThomInput.thom R (Fin r) τ α G :=
  CompatibleTorusThom.thomIsoOn G R κ n B r i τ α e ≪≫
    OrderedThomSections.thomIso (Selected n i.val) r
      ((Fintype.card_coe i.val).trans i.property.1) (TorusThomInput.BaseRing R τ α) G

def standardCell : Cell J (-(r : ℤ)) (L.obj (TorusThomInput.thom R (Fin r) τ α G)) :=
  redegree (T.cell (Fin r) τ α) (by simp)

def termIso :
    (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i).term ≅
      (standardCell J L G R T r τ α).term :=
  StrictCellIsoTransport.iso J
    (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i)
    (standardCell J L G R T r τ α) (L.mapIso (thomIso G R κ n B r i τ α e))

omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem test (M : A) (a : (standardCell J L G R T r τ α).term ⟶ M) :
    StrictCellTests.testAddEquiv J
      (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i) M
      ((termIso J L G R T κ n B hpos hneg hsupport hf hs r i τ α e).hom ≫ a)=
    (L.mapIso (thomIso G R κ n B r i τ α e)).hom ≫
      StrictCellTests.testAddEquiv J (standardCell J L G R T r τ α) M a :=
  StrictCellIsoTransport.iso_test J _ _ _ M a

#print axioms thomIso
#print axioms standardCell
#print axioms termIso
#print axioms test
end Verification.StrictLocalizedCoordinateTransport
