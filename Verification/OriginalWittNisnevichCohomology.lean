/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittCochainIso
import Verification.OriginalNisnevichCohomology

/-!
# Original Witt Nisnevich Cohomology

The literal signed group-ring quotient complex, tensored with the
actual coefficient Witt ring, computes ordinary Nisnevich cohomology of
the represented eta-periodic Witt coefficient. No signature lattice is used.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalWittNisnevichCohomology
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
variable (R : Type) [Field R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (κ : Type) [Fintype κ] (n : ℕ)
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

variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (U : LocalizedAffineThomInvariance.Standard L R G)


variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v) = r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV U
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (WN : LaurentNormalization R W WD site N WE Cg)
variable (WO : WittThomOrientationInput.Normalization J L G R site M N V O W WD WE)
local notation "TC" => OriginalWittTensorTerms.complex κ n B (RingSection W R) hpos hneg hsupport
local notation "RC" => (fun j : ℤ => StrictCoefficientCochains.complex (Model).complex (M j))
local notation "TE" => OriginalWittCoefficientTerms.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
  E P H empty site M N V W WD WT WH WE
local notation "SE" => OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
  E P H empty site M N V



variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)

def cohomologyEquiv (j : ℤ) (p : ℕ) : (TC).homology p ≃+
    Nis.cohomology (Spec (CommRingCat.of (Global R κ n B))) (M j) p := by
  letI := GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport hf hs
  exact (OriginalWittCochainIso.homologyEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
    site M N V W WD WT WH WE Q K U hV O Cg hCg Norm WN WO j p).trans
      ((StrictCoefficientComparison.cohomologyEquiv J HC (Model)
        (OriginalPositiveCellular.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
        (M j) p).trans (NR.comparison (Global R κ n B) (M j) p).symm)

#print axioms cohomologyEquiv
end Verification.OriginalWittNisnevichCohomology
