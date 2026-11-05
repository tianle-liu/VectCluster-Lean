/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictPositiveCellular
import Verification.StrictCellularOriginal

/-!
# Original Positive Cellular

The original AS exchange space has the actual positive-boundary strict
cellular model, with its original projective cell terms and exact support
from minus the independence height to zero.
-/
noncomputable section
namespace Verification.OriginalPositiveCellular
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

def complex : CochainComplex A ℤ := StrictPositiveCellular.cochain J L H
  (PrimeSchemeFiltration.filteredChains (Global R κ n B) (fun i => initial R κ n B (Sum.inl i)) G)
  (StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P)
  (StrictCellularGlobal.emptyStage L G R κ n B empty)

def signIso : StrictCellularOriginal.literalComplex J L G R T κ n B hpos hneg hsupport hf hs E P H empty ≅
    complex J L G R T κ n B hpos hneg hsupport hf hs E P H empty :=
  StrictPositiveCellular.signIso J L H
    (PrimeSchemeFiltration.filteredChains (Global R κ n B) (fun i => initial R κ n B (Sum.inl i)) G)
    (StrictLocalizedCells.cell J L G R T κ n B hpos hneg hsupport hf hs E P)
    (StrictCellularGlobal.emptyStage L G R κ n B empty)

def model : Model J (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) :=
  StrictModelTransport.ofComplexIso J
    (StrictCellularOriginal.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (complex J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (signIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty)

def realizationIso :
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex ≅
      complex J L G R T κ n B hpos hneg hsupport hf hs E P H empty :=
  StrictCellularOriginal.realizationIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty ≪≫
    signIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty

theorem support_lower : (model J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex.IsStrictlyGE
    (-(StrictCellularGlobal.height κ n B : ℤ)) := by
  letI := StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty
  exact CochainComplex.isStrictlyGE_of_iso
    (realizationIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty) _

theorem support_upper : (model J L G R T κ n B hpos hneg hsupport hf hs E P H empty).complex.IsStrictlyLE 0 := by
  letI := StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty
  exact CochainComplex.isStrictlyLE_of_iso
    (realizationIso J L G R T κ n B hpos hneg hsupport hf hs E P H empty) _

#print axioms complex
#print axioms signIso
#print axioms model
#print axioms realizationIso
#print axioms support_lower
#print axioms support_upper
end Verification.OriginalPositiveCellular
