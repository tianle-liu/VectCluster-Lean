/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedPureContraction
import Verification.SingleDegreeResidual
import Verification.LowerConeRetraction

/-!
# Filtered Zero Reduction

A finite strictly weight-raising perturbation of the constructed pure
path contraction has zero residual differential. Its actual homology in every
degree is therefore isomorphic to that of the pure complex.
-/

namespace Verification.FilteredZeroReduction

open CategoryTheory Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.PerturbedHomologyModel

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
variable (d : ι → ℤ) (w : ι → ℕ) (A D : Matrix ι ι R)
variable (T : Verification.WeightedPureContraction.Data d w A)
variable (hd : Homogeneous d 1 D) (hD : D*D=0) (b : ℕ) (hw : ∀ i,w i≤b)
variable (hV : ∀ i j,w i≤w j → (D-A) i j=0)

noncomputable def data : Verification.LowerConeRetraction.Data d D (pureProjection A T.homotopy) := by
  let V := D-A
  have hsum : A+V=D := by dsimp [V]; abel
  have hsq : (A+V)*(A+V)=0 := by rw [hsum]; exact hD
  have hVd : Homogeneous d 1 V := homogeneous_sub d 1 D A hd T.differential_degree
  let F := filteredRetraction d A T.homotopy V T.differential_degree T.homotopy_degree hVd
    T.differential_square T.homotopy_square T.homotopy_regular T.generalized hsq w b hw T.weight_preserving hV
  have hP := pureProjection_square A T.homotopy T.differential_square T.homotopy_square T.homotopy_regular T.generalized
  let E : Verification.LowerConeRetraction.Data d (A+V) (pureProjection A T.homotopy) := {
    toGradedRetraction := F
    right_support := Verification.TransposeReduction.residual_right A T.homotopy V _ hP
    projection_degree := Verification.PureDegreeSurvivors.projection_degree d A T.homotopy T.differential_degree T.homotopy_degree
    projection_square := hP }
  rw [← hsum]
  exact E

theorem residual_zero : (data d w A D T hd hD b hw hV).differential=0 :=
  Verification.SingleDegreeResidual.differential_zero d _ _ (data d w A D T hd hD b hw hV).degreeS
    (data d w A D T hd hD b hw hV).differential_support
    (data d w A D T hd hD b hw hV).right_support T.supported

noncomputable def homologyIso (p : ℤ) :
    (matrixComplex d D hd hD).homology p ≅
      (matrixComplex d A T.differential_degree T.differential_square).homology p :=
  (homotopyEquiv d D (pureProjection A T.homotopy) (data d w A D T hd hD b hw hV).toGradedRetraction).toHomologyIso p ≪≫
    Verification.SingleDegreeResidual.homologyIso d _ _ (data d w A D T hd hD b hw hV).degreeS
      (data d w A D T hd hD b hw hV).differential_support (data d w A D T hd hD b hw hV).square
      (residual_zero d w A D T hd hD b hw hV) p ≪≫
    (Verification.PureDegreeSurvivors.pureHomologyIso d A T.homotopy T.differential_degree T.homotopy_degree
      T.differential_square T.homotopy_square T.homotopy_regular T.generalized p).symm

#print axioms data
#print axioms residual_zero
#print axioms homologyIso

end Verification.FilteredZeroReduction
