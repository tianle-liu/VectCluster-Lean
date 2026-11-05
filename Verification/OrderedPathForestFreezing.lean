/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestCohomologicalDimension
import Verification.OriginalOrderedFreezing

/-!
# Ordered Path Forest Freezing

The actual ordered-freezing dimension theorem, instantiated with the
proved arbitrary-orientation path-forest vanishing. No path or article
cohomology conclusion is an input.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OrderedPathForestFreezing
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] Abelian.hasFiniteBiproducts
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)

open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence Verification.PathSignedFaceUnits
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.PathMilnorWittCoefficients
variable (R : Type) [Field R]
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)
variable (MW : GradedMilnorWittLaurent.Standard R site N W Cg)

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (CR : StrictProjectiveModel.ChainRepresentability (A:=A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v)=r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV H
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)

variable (Z₀ : A) (Symbols : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)

variable (PH : GradedMilnorWittHomogeneity.Standard site N W)
variable (SC : GradedMilnorWittStrictScalars.Standard J L G R site M N W PH V)



variable [MonoidalCategory A] [MonoidalPreadditive A]
variable (MS : ContractedStrictProductInput.Standard J L G R)
variable (unit : Z₀≅𝟙_ A) (TensorMW : PositiveMilnorWittTensorInput.Standard M)
variable (FZ : FZForestMutationInput.Standard) (BFZ : BFZForestMutationInput.Standard R)
variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))
variable (NP : StrictNisnevichInput.Standard Nis R)
variable (LP : StrictPrincipalLongExact.Standard Nis R)
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n⊕κ) → (Fin n⊕Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hall : ∀ I : Finset (Fin n),Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I)
variable (rank : Fin n → ℕ) (hinj : Function.Injective rank)
variable (horder : FreezingOrder.Good PathForestMatrixPredicate.IsPathForest
  (fun i j => B (Sum.inl i) (Sum.inl j)) (ExchangeRing.Adjacent (laterWeights κ n B)) rank)

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg hsupport hall hinj horder in
theorem scalar_bound (u v : Fin n → Rˣ) :
    StrictCohomologicalDimension.Bound Nis (ScalarFrozenGlobal.Global R κ n B u v) 1 :=
  ScalarOrderedFreezing.bound Nis R NP LP PathForestMatrixPredicate.IsPathForest
    (fun κ _ n B a b _ _ _ hall hf =>
      PathForestCohomologicalDimension.scalar_bound J L G E R P H site M N V hV Cg hCg O W QO MW
        T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC κ n B hall hf a b)
    n κ B u v hpos hneg hsupport hall rank hinj horder

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC NP LP hpos hneg hsupport hall hinj horder in
theorem original_bound : StrictCohomologicalDimension.Bound Nis (Global R κ n B) 1 :=
  OriginalOrderedFreezing.bound Nis R NP LP PathForestMatrixPredicate.IsPathForest
    (fun κ _ n B a b _ _ _ hall hf =>
      PathForestCohomologicalDimension.scalar_bound J L G E R P H site M N V hV Cg hCg O W QO MW
        T CR empty Q K Norm Z₀ Symbols PH SC MS unit TensorMW FZ BFZ Nis NR HC κ n B hall hf a b)
    n κ B hpos hneg hsupport hall rank hinj horder

#print axioms scalar_bound
#print axioms original_bound
end Verification.OrderedPathForestFreezing
