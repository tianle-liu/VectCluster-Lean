/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittTensorTerms
import Verification.OriginalOrderedWittResidue
import Verification.SelectedWittIncidenceSign

/-!
# Original Witt Coefficient Terms

Degreewise comparison between the literal integer Witt complex tensored
with actual ground-field Witt sections and the actual strict coefficient row.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalWittCoefficientTerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
open Verification.WittSheafSectionsInput
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

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

open scoped BigOperators
local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty



variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (WD : Symbols R W)
variable (WT : TorusBasis R W WD) (WH : WittSheafAffineInvariance.Standard R W)
variable (WE : Comparison R W site N)

def coefficientEquiv (p : ℕ) (j : ℤ) :
    ((I : ActualCellThom.Index κ n B p) →
      OriginalWittQuotient.Stratum (fun a v => B a (Sum.inl v)) I.val ⊗[ℤ] RingSection W R) ≃+
    ((I : ActualCellThom.Index κ n B p) →
      (N (j-p)).val.obj (op (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I.val B))))) :=
  AddEquiv.piCongrRight (fun I =>
    (OriginalWittSectionCoordinates.equiv R κ n I.val B (hf I.val I.property.2) (hs I.val I.property.2)
      hpos hneg hsupport I.property.2 W WD WT WH).trans
      (WE.sections _ (OriginalASMonomialUnits.smooth R κ n I.val B (hf I.val I.property.2)
        (hs I.val I.property.2) hpos hneg hsupport I.property.2) (j-p)))

def termEquiv (p : ℕ) (j : ℤ) :
    (OriginalWittTensorTerms.complex κ n B (RingSection W R) hpos hneg hsupport).X p ≃+
      (StrictCoefficientCochains.complex (Model).complex (M j)).X p :=
  ((OriginalWittTensorTerms.termEquiv κ n B (RingSection W R) p).toAddEquiv.trans
    (coefficientEquiv R κ n B hpos hneg hsupport hf hs site N W WD WT WH WE p j)).trans
      (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
        site M N V p j).symm

theorem termEquiv_apply (p : ℕ) (j : ℤ)
    (a : (OriginalWittTensorTerms.complex κ n B (RingSection W R) hpos hneg hsupport).X p)
    (I : ActualCellThom.Index κ n B p) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
      site M N V p j (termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V W WD WT WH WE p j a) I =
    WE.sections _ (OriginalASMonomialUnits.smooth R κ n I.val B (hf I.val I.property.2)
      (hs I.val I.property.2) hpos hneg hsupport I.property.2) (j-p)
      (OriginalWittSectionCoordinates.equiv R κ n I.val B (hf I.val I.property.2) (hs I.val I.property.2)
        hpos hneg hsupport I.property.2 W WD WT WH
          (OriginalWittTensorTerms.termEquiv κ n B (RingSection W R) p a I)) := by
  change (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
    site M N V p j) ((OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
      site M N V p j).symm _) I = _
  rw [AddEquiv.apply_symm_apply]
  rfl

#print axioms coefficientEquiv
#print axioms termEquiv
#print axioms termEquiv_apply
end Verification.OriginalWittCoefficientTerms
