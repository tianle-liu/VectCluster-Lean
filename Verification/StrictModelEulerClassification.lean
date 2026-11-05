/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AmbientPostnikovStages
import Verification.AllBundleEulerOrbits
import Verification.UnitNormalizedClassification

/-!
# Strict Model Euler Classification

Euler classification in the actual ambient cohomology group,
obtained from a bounded strict projective model. The cited fixed-unit
comparison and determinant action are uniform inputs on ambient groups;
the classifier's bijectivity and the unoriented quotient are proved.
-/
noncomputable section
namespace Verification.StrictModelEulerClassification
open CategoryTheory
universe w v u v' u'
variable {R : Type} [CommRing R] [IsDomain R]
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable {J : DerivedCategory A ⥤ D} [J.Additive] {X : D} {K2 : A}
variable (S : AmbientPostnikovStages.EulerStages (R := R) J X K2)
variable (G : Type*) [Group G]
variable [MulAction G (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))]
variable [MulAction Rˣ (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))]

structure StandardEuler where
  chowWitt : ActualOrientations.Classes (R := R) (r := 2) →
    (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))
  factor : G
  comparison : ∀ E,S.firstStage ((S.convergence E).val 0)=factor • chowWitt E
  unit_action : ∀ (u : Rˣ) (E : ActualOrientations.Oriented R 2),
    chowWitt (Quotient.mk _ (ActualOrientations.changeOrientation u E))=
      u • chowWitt (Quotient.mk _ E)

variable {G} (E : StandardEuler S G)
variable (H : StrictCoefficientComparison.StandardHomology (A := A))
variable (P : StrictProjectiveModel.Model J X) (hp : P.complex.IsStrictlyLE 0)
variable {h : ℕ} (hb : P.complex.IsStrictlyGE (-(h : ℤ))) (hh : h≤2)

def obstructionEquiv : ActualOrientations.Classes (R := R) (r := 2) ≃
    (X ⟶ J.obj (StrictCoefficientComparison.target K2 2)) :=
  (PostnikovEulerClassification.eulerEquiv
    (AmbientPostnikovStages.eulerForModel H P hp K2 S)
    (fun M _q hq => StrictCoefficientCochains.homology_zero P.complex M hb (by omega))).trans
      (StrictCoefficientComparison.cohomologyEquiv J H P hp K2 2).toEquiv

omit [IsDomain R] [MulAction Rˣ (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))] in
theorem obstructionEquiv_apply (Q : ActualOrientations.Classes (R := R) (r := 2)) :
    obstructionEquiv S H P hp hb hh Q=S.firstStage ((S.convergence Q).val 0) := by
  exact (StrictCoefficientComparison.cohomologyEquiv J H P hp K2 2).apply_symm_apply _

def chowWittEquiv : ActualOrientations.Classes (R := R) (r := 2) ≃
    (X ⟶ J.obj (StrictCoefficientComparison.target K2 2)) :=
  UnitNormalizedClassification.equivalence (obstructionEquiv S H P hp hb hh)
    E.chowWitt E.factor (fun Q => (obstructionEquiv_apply S H P hp hb hh Q).trans (E.comparison Q))

omit [IsDomain R] in
theorem chowWittEquiv_apply (Q : ActualOrientations.Classes (R := R) (r := 2)) :
    chowWittEquiv S E H P hp hb hh Q=E.chowWitt Q := rfl

variable (Det : DeterminantStandardInput.Standard R)
variable (k : Type) [Field k] [Algebra R k]
variable (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))

def unorientedEquiv : RankedProjectiveClasses.Classes R 2 ≃
    Quotient (MulAction.orbitRel Rˣ (X ⟶ J.obj (StrictCoefficientComparison.target K2 2))) :=
  AllBundleEulerOrbits.classification Det k hk (chowWittEquiv S E H P hp hb hh) E.unit_action

#print axioms StandardEuler
#print axioms obstructionEquiv
#print axioms obstructionEquiv_apply
#print axioms chowWittEquiv
#print axioms chowWittEquiv_apply
#print axioms unorientedEquiv
end Verification.StrictModelEulerClassification
