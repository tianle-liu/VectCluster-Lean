/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StandardThomContractionNormalization
import Verification.SheafReducedProjection
import Verification.ActualSheafContractionRestriction
import Verification.GradedSectionTotal

/-!
# Sheaf Graded Laurent Residue

The total Laurent residue is constructed from the genuine evaluation-at-one
kernel and its ordinary grading contraction. The constant rule is a theorem;
the total map agrees degree by degree with the coefficient sheaf used by the
actual geometric boundary. No cellular or chart compatibility is assumed.
-/
noncomputable section
namespace Verification.SheafGradedLaurentResidue
open CategoryTheory AlgebraicGeometry Opposite
open scoped DirectSum
open Verification.GradedSectionTotal
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))

abbrev Section (S : Type) [CommRing S] (q : ℤ) :=
  (N q).val.obj (op (Spec (CommRingCat.of S)))

theorem atOne_coefficient (q : ℤ) (a : Section site N S q) :
    AffineSheafContraction.sheafAtOne R S site N q
      (SheafReducedProjection.coefficientPullback R S site N q a) = a := by
  have h := congrArg (fun g : S →ₐ[R] S =>
    ActualSheafContractionRestriction.pullback site (N q) g.toRingHom)
    (LaurentBasepoint.atOne_coefficient R S)
  change ActualSheafContractionRestriction.pullback site (N q)
      ((LaurentBasepoint.atOne R S).toRingHom.comp (LaurentBasepoint.coefficient R S).toRingHom) = _ at h
  rw [ActualSheafContractionRestriction.pullback_comp] at h
  have ha := DFunLike.congr_fun h a
  change AffineSheafContraction.sheafAtOne R S site N q
    (SheafReducedProjection.coefficientPullback R S site N q a) = _ at ha
  rw [ha]
  change (N q).val.map (Spec.map (𝟙 (CommRingCat.of S))).op a = a
  simp only [Spec.map_id,op_id,CategoryTheory.Functor.map_id,ModuleCat.id_apply]

def reduce (q : ℤ) : Section site N (LaurentBasepoint.Laurent S) q →+
    (AffineSheafContraction.sheafAtOne R S site N q).ker where
  toFun a := ⟨a-SheafReducedProjection.coefficientPullback R S site N q
    (AffineSheafContraction.sheafAtOne R S site N q a),by
      change AffineSheafContraction.sheafAtOne R S site N q _ = 0
      rw [map_sub,atOne_coefficient,sub_self]⟩
  map_zero' := by apply Subtype.ext; simp only [map_zero,sub_zero,AddSubgroup.coe_zero]
  map_add' a b := by
    apply Subtype.ext
    simp only [AddSubgroup.coe_add,map_add]
    abel

theorem reduce_coefficient (q : ℤ) (a : Section site N S q) :
    reduce R S site N q (SheafReducedProjection.coefficientPullback R S site N q a)=0 := by
  apply Subtype.ext
  change _ - _ = 0
  rw [atOne_coefficient,sub_self]

theorem reduce_of_mem (q : ℤ) (a : (AffineSheafContraction.sheafAtOne R S site N q).ker) :
    reduce R S site N q a.val = a := by
  apply Subtype.ext
  change a.val-SheafReducedProjection.coefficientPullback R S site N q
    (AffineSheafContraction.sheafAtOne R S site N q a.val) = a.val
  rw [a.property,map_zero,sub_zero]

theorem kernel_eq_reduce (q : ℤ) (a : (AffineSheafContraction.sheafAtOne R S site N q).ker)
    (z : Section site N (LaurentBasepoint.Laurent S) q)
    (h : a.val=z-SheafReducedProjection.coefficientPullback R S site N q
      (AffineSheafContraction.sheafAtOne R S site N q z)) : a=reduce R S site N q z :=
  Subtype.ext h

variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S)

def degreeResidue (q : ℤ) : Section site N (LaurentBasepoint.Laurent S) q →+
    Section site N S (q-1) :=
  (K.contract S hs q).toAddMonoidHom.comp (reduce R S site N q)

theorem degreeResidue_coefficient (q : ℤ) (a : Section site N S q) :
    degreeResidue R S site N K hs q (SheafReducedProjection.coefficientPullback R S site N q a)=0 := by
  simp only [degreeResidue,AddMonoidHom.comp_apply,reduce_coefficient,map_zero]

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable (E : (⨁ q,Section site N S q) ≃+ B)
variable (EL : (⨁ q,Section site N (LaurentBasepoint.Laurent S) q) ≃+ A)

def totalResidue : A →+ B :=
  reindexMap EL E (fun q=>q-1) (degreeResidue R S site N K hs)

theorem totalResidue_degree (q : ℤ) (a : Section site N (LaurentBasepoint.Laurent S) q) :
    totalResidue R S site N K hs E EL (includeDegree EL q a) =
      includeDegree E (q-1) (K.contract S hs q (reduce R S site N q a)) :=
  reindexMap_degree EL E (fun q=>q-1) (degreeResidue R S site N K hs) q a

theorem totalResidue_kernel (q : ℤ) (a : (AffineSheafContraction.sheafAtOne R S site N q).ker) :
    totalResidue R S site N K hs E EL (includeDegree EL q a.val) =
      includeDegree E (q-1) (K.contract S hs q a) := by
  rw [totalResidue_degree,reduce_of_mem]

theorem totalResidue_constant (F : B →+ A)
    (hF : ∀ q a,F (includeDegree E q a) = includeDegree EL q
      (SheafReducedProjection.coefficientPullback R S site N q a)) (b : B) :
    totalResidue R S site N K hs E EL (F b)=0 := by
  have he : (totalResidue R S site N K hs E EL).comp F = 0 := by
    apply hom_ext E
    intro q a
    rw [AddMonoidHom.comp_apply,hF,totalResidue_degree,reduce_coefficient,map_zero,map_zero]
    rfl
  exact DFunLike.congr_fun he b

#print axioms Section
#print axioms atOne_coefficient
#print axioms reduce
#print axioms reduce_coefficient
#print axioms reduce_of_mem
#print axioms kernel_eq_reduce
#print axioms degreeResidue
#print axioms degreeResidue_coefficient
#print axioms totalResidue
#print axioms totalResidue_degree
#print axioms totalResidue_kernel
#print axioms totalResidue_constant
end Verification.SheafGradedLaurentResidue
