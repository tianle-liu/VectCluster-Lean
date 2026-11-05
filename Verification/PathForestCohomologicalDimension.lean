/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestOrientedModel
import Verification.PathForestMatrixPredicate
import Verification.PrincipalIndependentOpen
import Verification.StrictCohomologicalDimension

/-!
# Path Forest Cohomological Dimension

Positive Nisnevich cohomology vanishes for every strictly invariant
coefficient object on the actual exchange ring of any oriented path forest.
The principal-matrix predicate is the one consumed by ordered freezing.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathForestCohomologicalDimension
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
variable (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n⊕κ)→(Fin n⊕Empty)→ℤ)
variable (hall : ∀I,ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) I→
  AnticliqueSubcolumns.AS (fun r i=>B r (Sum.inl i)) I)
variable (hforest : PathForestMatrixPredicate.IsPathForest n (fun i j=>B (Sum.inl i) (Sum.inl j)))

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC hall hforest in
theorem original_bound : StrictCohomologicalDimension.Bound Nis (FrozenAcyclicCover.Global R κ n B) 0 := by
  rcases hforest with ⟨S,fs,hforest⟩
  letI := fs
  rcases hforest with ⟨m,o,a,e,hp⟩
  have hAS : ∀I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I→
      AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I :=
    fun I hI=>hall I (PrincipalIndependentOpen.independent B I hI)
  letI := PathForestOrientedModel.originalSmooth R m o a n e B hp hAS FZ BFZ
  intro U p hp'
  exact ContractedStrictProductInput.vanishes J L G R (FrozenAcyclicCover.Global R κ n B) Nis NR HC
    (PathForestOrientedModel.original J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC
      m o a n e B hp hAS FZ BFZ MS unit TensorMW) U p hp'

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS unit TensorMW FZ BFZ NR HC hall hforest in
theorem scalar_bound (u v : Fin n→Rˣ) :
    StrictCohomologicalDimension.Bound Nis (ScalarFrozenGlobal.Global R κ n B u v) 0 := by
  rcases hforest with ⟨S,fs,hforest⟩
  letI := fs
  rcases hforest with ⟨m,o,a,e,hp⟩
  have hAS : ∀I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I→
      AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I :=
    fun I hI=>hall I (PrincipalIndependentOpen.independent B I hI)
  letI := PathForestOrientedModel.scalarSmooth R m o a n e B hp hAS FZ BFZ u v
  intro U p hp'
  exact ContractedStrictProductInput.vanishes J L G R (ScalarFrozenGlobal.Global R κ n B u v) Nis NR HC
    (PathForestOrientedModel.scalar J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC
      m o a n e B hp hAS FZ BFZ MS unit TensorMW u v) U p hp'

#print axioms original_bound
#print axioms scalar_bound
end Verification.PathForestCohomologicalDimension
