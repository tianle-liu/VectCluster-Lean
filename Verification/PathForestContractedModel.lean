/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualPathForestScalarProduct
import Verification.PathMinimalSmooth
import Verification.PathMinimalContractedModels
import Verification.PathBaseContractedModel
import Verification.FiniteContractedFamily
import Verification.PathForestMinimalFactors
import Verification.PathForestUnusedTorus
import Verification.PathOriginalStrictComplex
import Verification.ContractedModelTransport
import Verification.PathOriginalZEquivalence

/-!
# Path Forest Contracted Model

The genuine original Y and Z path strict models are isomorphic to their fully proved full-rho complexes and contract to the exact degree-zero MW survivors. No geometric comparison is an input.
-/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.PathForestContractedModel
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


open Verification.PathForestPartitionPresentation Verification.PathForestFrozenPartition
variable {S F : Type} [Fintype S] [Fintype F] (m : S→ℕ) (o : S→Bool)

def factorSurvivor : Option S→A
  | none=>(T.cell Empty Empty (Unused (F:=F) o)).term
  | some s=>if o s=true then Z₀ ⊞ ⨁ fun k : Fin (2*m s+1+1)=>M ((k.val+1:ℕ):ℤ)
      else Z₀ ⊞ ⨁ fun k : Fin (m s)=>M ((2*(k.val+1):ℕ):ℤ)

def factorSmooth (j : Option S) : Algebra.Smooth R (Factor (F:=F) m o R j) := by
  cases j with
  | none=>exact PathForestUnusedTorus.smooth (F:=F) m o R
  | some s=>
    cases h : o s with
    | false=>
      letI := PathMinimalSmooth.y R (m s)
      exact Algebra.Smooth.of_equiv (PathForestMinimalFactors.evenEquiv (F:=F) m o R s h).symm
    | true=>
      letI := PathMinimalSmooth.z R (2*m s+1)
      exact Algebra.Smooth.of_equiv (PathForestMinimalFactors.oddEquiv (F:=F) m o R s h).symm

def factorModel (j : Option S) : ContractedStrictProductInput.ContractedModel J
    (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Factor (F:=F) m o R j))))))
    (factorSurvivor J L G R M T Z₀ (F:=F) m o j) := by
  cases j with
  | none=>exact PathForestUnusedTorus.model (F:=F) m o R J L G T empty
  | some s=>
    cases h : o s with
    | false=>
      simp only [factorSurvivor,h,Bool.false_eq_true,if_false]
      exact ContractedModelTransport.ring J L G (PathForestMinimalFactors.evenEquiv (F:=F) m o R s h).toRingEquiv
        (PathMinimalContractedModels.y J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC (m s))
    | true=>
      simp only [factorSurvivor,h,if_true]
      exact ContractedModelTransport.ring J L G (PathForestMinimalFactors.oddEquiv (F:=F) m o R s h).toRingEquiv
        (PathMinimalContractedModels.z J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC (2*m s+1))

variable [MonoidalCategory A] [MonoidalPreadditive A]
variable (MS : ContractedStrictProductInput.Standard J L G R)

def productModel :=
  letI : ∀ j,Algebra.Smooth R (Factor (F:=F) m o R j) := factorSmooth (F:=F) R m o
  FiniteContractedFamily.model J L G R MS
    (PathBaseContractedModel.base J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC)
    (Option S) (Factor (F:=F) m o R) (factorSurvivor J L G R M T Z₀ (F:=F) m o)
    (factorModel (F:=F) J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC m o)

variable (n : ℕ) (e : PathForestComponentMatrix.Vertices m o ≃ Fin n)
variable (B : Matrix (Fin n ⊕ F) (Fin n ⊕ Empty) ℤ)
variable (hprincipal : ∀ i j,B (Sum.inl (e i)) (Sum.inl (e j))=PathForestComponentMatrix.ordinaryMatrix m o i j)
variable (hAS : ∀ I,ExchangeReindex.PrincipalIndependent (EmptyColumnRetraction.cut B) I →
  AnticliqueSubcolumns.AS (EmptyColumnRetraction.cut B) I)

def originalModel :=
  ContractedModelTransport.ring J L G
    (PathForestPartitionPresentation.originalEquiv m o R n e B hprincipal hAS).toRingEquiv
    (productModel (F:=F) J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC m o MS)

def scalarModel (a b : Fin n→Rˣ) :=
  ContractedModelTransport.ring J L G
    (ActualPathForestScalarProduct.scalarEquiv R m o n e B hprincipal hAS a b).toRingEquiv
    (productModel (F:=F) J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC m o MS)

def originalSmooth : Algebra.Smooth R (Global R F n B) := by
  letI : ∀ j,Algebra.Smooth R (Factor (F:=F) m o R j) := factorSmooth (F:=F) R m o
  letI := FiniteContractedFamily.smooth R (Option S) (Factor (F:=F) m o R)
  exact Algebra.Smooth.of_equiv (R:=R) (A:=Product (F:=F) m o R) (B:=Global R F n B)
    (PathForestPartitionPresentation.originalEquiv m o R n e B hprincipal hAS).symm

def scalarSmooth (a b : Fin n→Rˣ) : Algebra.Smooth R (ScalarFrozenGlobal.Global R F n B a b) := by
  letI : ∀ j,Algebra.Smooth R (Factor (F:=F) m o R j) := factorSmooth (F:=F) R m o
  letI := FiniteContractedFamily.smooth R (Option S) (Factor (F:=F) m o R)
  exact Algebra.Smooth.of_equiv (R:=R) (A:=Product (F:=F) m o R) (B:=ScalarFrozenGlobal.Global R F n B a b)
    (ActualPathForestScalarProduct.scalarEquiv R m o n e B hprincipal hAS a b).symm

variable (Nis : StrictNisnevichInput.Theory A)
variable (NR : StrictNisnevichRepresentability.Standard J L G Nis R)
variable (HC : StrictCoefficientComparison.StandardHomology (A:=A))
include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS NR HC hprincipal hAS in
omit [MonoidalPreadditive A] in
theorem originalVanishes (U : A) (p : ℕ) (hp : 0<p) :
    IsZero (Nis.cohomology (Spec (CommRingCat.of (Global R F n B))) U p) := by
  letI := originalSmooth R m o n e B hprincipal hAS
  exact ContractedStrictProductInput.vanishes J L G R (Global R F n B) Nis NR HC
    (originalModel J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC m o MS n e B hprincipal hAS) U p hp

include E P H V hV Cg hCg O W QO MW T CR empty Q K Norm Symbols PH SC MS NR HC hprincipal hAS in
omit [MonoidalPreadditive A] in
theorem scalarVanishes (a b : Fin n→Rˣ) (U : A) (p : ℕ) (hp : 0<p) :
    IsZero (Nis.cohomology (Spec (CommRingCat.of (ScalarFrozenGlobal.Global R F n B a b))) U p) := by
  letI := scalarSmooth R m o n e B hprincipal hAS a b
  exact ContractedStrictProductInput.vanishes J L G R (ScalarFrozenGlobal.Global R F n B a b) Nis NR HC
    (scalarModel J L G E R P H site M N V hV Cg hCg O W QO MW T CR empty Q K Norm Z₀ Symbols PH SC m o MS n e B hprincipal hAS a b) U p hp

#print axioms factorSurvivor
#print axioms factorSmooth
#print axioms factorModel
#print axioms productModel
#print axioms originalModel
#print axioms scalarModel
#print axioms originalSmooth
#print axioms scalarSmooth
#print axioms originalVanishes
#print axioms scalarVanishes
end Verification.PathForestContractedModel
