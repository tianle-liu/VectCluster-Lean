/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SheafGradedLaurentResidue

/-!
# Actual Graded Laurent Split

Ordinary Laurent splitting, derived from the actual u=1 evaluation and
its genuine contraction kernel. Both inverse formulas are explicit.
-/
noncomputable section
namespace Verification.ActualGradedLaurentSplit
open CategoryTheory AlgebraicGeometry Opposite
open Verification.SheafGradedLaurentResidue
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S) (q : ℤ)

def equiv : Section site N (LaurentBasepoint.Laurent S) q ≃+
    Section site N S q × Section site N S (q-1) where
  toFun a := ⟨AffineSheafContraction.sheafAtOne R S site N q a,
    degreeResidue R S site N K hs q a⟩
  invFun a := SheafReducedProjection.coefficientPullback R S site N q a.1 +
    ((K.contract S hs q).symm a.2).val
  left_inv a := by
    change SheafReducedProjection.coefficientPullback R S site N q
      (AffineSheafContraction.sheafAtOne R S site N q a) +
      ((K.contract S hs q).symm (K.contract S hs q (reduce R S site N q a))).val = a
    rw [AddEquiv.symm_apply_apply]
    change _ + (a-_) = a
    abel
  right_inv a := by
    apply Prod.ext
    · change AffineSheafContraction.sheafAtOne R S site N q
        (SheafReducedProjection.coefficientPullback R S site N q a.1 +
          ((K.contract S hs q).symm a.2).val) = a.1
      rw [map_add,atOne_coefficient,((K.contract S hs q).symm a.2).property,add_zero]
    · change degreeResidue R S site N K hs q
        (SheafReducedProjection.coefficientPullback R S site N q a.1 +
          ((K.contract S hs q).symm a.2).val) = a.2
      rw [map_add,degreeResidue_coefficient,zero_add]
      change K.contract S hs q (reduce R S site N q ((K.contract S hs q).symm a.2).val)=a.2
      rw [reduce_of_mem,AddEquiv.apply_symm_apply]
  map_add' a b := by
    apply Prod.ext
    · exact map_add (AffineSheafContraction.sheafAtOne R S site N q) a b
    · exact map_add (degreeResidue R S site N K hs q) a b

theorem equiv_first (a : Section site N (LaurentBasepoint.Laurent S) q) :
    (equiv R S site N K hs q a).1=AffineSheafContraction.sheafAtOne R S site N q a := rfl

theorem equiv_second (a : Section site N (LaurentBasepoint.Laurent S) q) :
    (equiv R S site N K hs q a).2=degreeResidue R S site N K hs q a := rfl

#print axioms equiv
#print axioms equiv_first
#print axioms equiv_second
end Verification.ActualGradedLaurentSplit
