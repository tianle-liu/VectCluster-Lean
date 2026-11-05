/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualCellThom
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual Cell Terms

The actual categorical homology defining each geometric cellular term
is transported through the proved finite excision and framed purity. This
is an isomorphism of actual coefficient objects, not a renaming of a matrix.
-/
noncomputable section
namespace Verification.ActualCellTerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.ActualCellThom Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
attribute [local instance] Abelian.hasFiniteBiproducts
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

def localTerm (r : ℕ) (i : Index κ n B r) : C :=
  (DerivedCategory.homologyFunctor C (-(r : ℤ))).obj (localThom G R κ n B r i)

def termIso (r : ℕ) : (GeometricCellularSource.source R G κ n B).X r ≅
    ⨁ fun i : Index κ n B r => localTerm G R κ n B r i :=
  ((DerivedCategory.homologyFunctorFactors C (-(r : ℤ))).app
    (FilteredConeComplex.relative (PrimeSchemeFiltration.filteredChains
      (Global R κ n B) (fun j => initial R κ n B (Sum.inl j)) G) r)).symm ≪≫
    (DerivedCategory.homologyFunctor C (-(r : ℤ))).mapIso
      (ActualCellThom.relativeIso G E R κ n B P hpos hneg hsupport hf hs r) ≪≫
        (DerivedCategory.homologyFunctor C (-(r : ℤ))).mapBiproduct (localThom G R κ n B r)

#print axioms localTerm
#print axioms termIso
end Verification.ActualCellTerms
