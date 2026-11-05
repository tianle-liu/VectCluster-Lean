/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientComparison
import Verification.PostnikovStabilization

/-!
# Ambient Postnikov Stages

Cited Postnikov inputs use actual ambient mapping groups, independently
of any chosen strict model. Their conversion to the article's coefficient
complexes is proved from the strict Hom universal property. No model-specific
cohomology identification is stored as a literature assumption.
-/
noncomputable section
namespace Verification.AmbientPostnikovStages
open CategoryTheory
universe w v u v' u'
variable {R : Type} [CommRing R] [IsDomain R]
variable (Det : DeterminantStandardInput.Standard R) (Nat : OrientedLineStabilization.Naturality Det)
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] (X : D)

structure EulerStages (K2 : A) where
  tower : PostnikovTowerLimit.Tower
  convergence : ActualOrientations.Classes (R := R) (r := 2) ≃ PostnikovTowerLimit.Sections tower
  firstStage : tower.stage 0 ≃ (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))
  existence : ∀ n,(∀ M : A,Subsingleton (X ⟶ J.obj (StrictCoefficientComparison.target M (n+4)))) →
    Function.Surjective (tower.transition n)
  uniqueness : ∀ n,(∀ M : A,Subsingleton (X ⟶ J.obj (StrictCoefficientComparison.target M (n+3)))) →
    Function.Injective (tower.transition n)

structure StabilizationStages (r : ℕ) where
  tower : PostnikovTowerLimit.Tower
  convergence : ActualOrientations.Classes (R := R) (r := r) ≃ PostnikovTowerLimit.Sections tower
  firstStage : tower.stage 0 ≃ ActualOrientations.Classes (R := R) (r := r+1)
  projection : ∀ P,firstStage ((convergence P).val 0)=OrientedLineStabilization.advance Det Nat r P
  existence : ∀ n,(∀ M : A,Subsingleton (X ⟶ J.obj (StrictCoefficientComparison.target M (r+n+1)))) →
    Function.Surjective (tower.transition n)
  uniqueness : ∀ n,(∀ M : A,Subsingleton (X ⟶ J.obj (StrictCoefficientComparison.target M (r+n)))) →
    Function.Injective (tower.transition n)

variable {J X} (H : StrictCoefficientComparison.StandardHomology (A := A))
variable (P : StrictProjectiveModel.Model J X) (hp : P.complex.IsStrictlyLE 0)

def eulerForModel (K2 : A) (S : EulerStages (R := R) J X K2) :
    PostnikovEulerClassification.StandardStages R A (StrictCoefficientCochains.complex P.complex) K2 where
  tower := S.tower
  convergence := S.convergence
  firstStage := S.firstStage.trans (StrictCoefficientComparison.cohomologyEquiv J H P hp K2 2).symm.toEquiv
  existence n hz := S.existence n (fun M => StrictCoefficientComparison.ambient_subsingleton J H P hp M _ (hz M))
  uniqueness n hz := S.uniqueness n (fun M => StrictCoefficientComparison.ambient_subsingleton J H P hp M _ (hz M))

def stabilizationForModel (r : ℕ) (S : StabilizationStages Det Nat J X r) :
    PostnikovStabilization.StandardStages Det Nat A (StrictCoefficientCochains.complex P.complex) r where
  tower := S.tower
  convergence := S.convergence
  firstStage := S.firstStage
  projection := S.projection
  existence n hz := S.existence n (fun M => StrictCoefficientComparison.ambient_subsingleton J H P hp M _ (hz M))
  uniqueness n hz := S.uniqueness n (fun M => StrictCoefficientComparison.ambient_subsingleton J H P hp M _ (hz M))

theorem above {h : ℕ} (hb : P.complex.IsStrictlyGE (-(h : ℤ))) :
    PostnikovStabilization.Above A (StrictCoefficientCochains.complex P.complex) h :=
  fun M _q hq => StrictCoefficientCochains.homology_zero P.complex M hb hq

#print axioms EulerStages
#print axioms StabilizationStages
#print axioms eulerForModel
#print axioms stabilizationForModel
#print axioms above
end Verification.AmbientPostnikovStages
