/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellTests
import Verification.StrictPositiveDifferential
import Verification.OriginalPositiveCellular
import Verification.StrictCoefficientCochains

/-!
# Original Strict Cell Tests

The actual coefficient cochains of the positive strict original model
have one summand per actual independent stratum, expressed as the ambient
Thom test group through the strict universal property.
-/
noncomputable section
namespace Verification.OriginalStrictCellTests
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

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

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

attribute [local instance] Abelian.hasFiniteBiproducts

def degreeIso (q : ℕ) :
    (OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex.X (-(q : ℤ)) ≅
      (StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P q).term :=
  StrictPositiveDifferential.termIso J L H
    (PrimeSchemeFiltration.filteredChains (Global R κ n B) (fun i => initial R κ n B (Sum.inl i)) G)
    (StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P)
    (StrictCellularGlobal.emptyStage L G R κ n B empty) q

def termEquiv (M : A) (q : ℕ) :
    (StrictCoefficientCochains.complex
      (OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex M).X q ≃+
    (∀ i : ActualCellThom.Index κ n B q,
      L.obj (ActualCellThom.localThom G R κ n B q i) ⟶
        J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(q : ℤ)) M))) :=
  (StrictCellTests.homOfIso (degreeIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty q) M).trans
    (StrictCellTests.biproductTests J
      (fun i : ActualCellThom.Index κ n B q => L.obj (ActualCellThom.localThom G R κ n B q i))
      (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs q) M)

#print axioms degreeIso
#print axioms termEquiv
end Verification.OriginalStrictCellTests
