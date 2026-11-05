/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Polynomial Section Iso

The zero section of an actual polynomial algebra is inverted by any
contravariant theory that inverts the actual polynomial projection. This is
an explicit categorical inverse construction, for use with the cited A1
invariance theorem and the proved original closed-stratum coordinates.
-/
namespace Verification.PolynomialSectionIso
open CategoryTheory Opposite
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]

noncomputable def constant : A →ₐ[R] MvPolynomial ι A := IsScalarTower.toAlgHom R A _

noncomputable def zeroEvaluation : MvPolynomial ι A →ₐ[R] A :=
  (MvPolynomial.aeval (fun _ : ι => (0 : A))).restrictScalars R

theorem evaluation_constant : (zeroEvaluation R A ι).comp (constant R A ι) = AlgHom.id R A := by
  ext a
  exact MvPolynomial.aeval_C _ _

variable {D : Type*} [Category D] (F : (Under (CommRingCat.of R))ᵒᵖ ⥤ D)

noncomputable def projectionMap :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial ι A))) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) :=
  F.map (constant R A ι).toUnder.op

noncomputable def sectionMap :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ⟶
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial ι A))) :=
  F.map (zeroEvaluation R A ι).toUnder.op

theorem section_projection : sectionMap R A ι F ≫ projectionMap R A ι F = 𝟙 _ := by
  unfold sectionMap projectionMap
  rw [← Functor.map_comp]
  change F.map ((zeroEvaluation R A ι).comp (constant R A ι)).toUnder.op = 𝟙 _
  rw [evaluation_constant]
  exact F.map_id _

/-- The external A1-invariance input concerns the polynomial projection only;
the zero-section inverse is constructed and verified here. -/
noncomputable def zeroSectionIso [IsIso (projectionMap R A ι F)] :
    F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) A)) ≅
      F.obj (op (CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial ι A))) where
  hom := sectionMap R A ι F
  inv := projectionMap R A ι F
  hom_inv_id := section_projection R A ι F
  inv_hom_id := by
    apply (cancel_mono (projectionMap R A ι F)).1
    rw [Category.assoc, section_projection, Category.comp_id, Category.id_comp]

#print axioms constant
#print axioms zeroEvaluation
#print axioms evaluation_constant
#print axioms projectionMap
#print axioms sectionMap
#print axioms section_projection
#print axioms zeroSectionIso
end Verification.PolynomialSectionIso
