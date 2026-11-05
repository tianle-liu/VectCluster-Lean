/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedDirectSumSplit
import Verification.ActualGradedLaurentSplit
import Verification.GradedMilnorWittLaurent

/-!
# Graded Milnor Witt Laurent Split

The actual total section ring of a Laurent line splits additively into
two copies of the actual coefficient section ring. Its projections are
evaluation at one and the constructed total residue.
-/
set_option maxHeartbeats 800000
noncomputable section
namespace Verification.GradedMilnorWittLaurentSplit
open CategoryTheory AlgebraicGeometry Opposite
open scoped DirectSum
open Verification.SheafGradedLaurentResidue Verification.GradedSectionTotal
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S)
local notation "B" => D.Total (CommRingCat.of S)
local notation "A" => D.Total (CommRingCat.of (LaurentBasepoint.Laurent S))

def equiv : A ≃+ B × B :=
  (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))).symm.trans
    ((DFinsupp.mapRange.addEquiv (ActualGradedLaurentSplit.equiv R S site N K hs)).trans
      ((GradedDirectSumSplit.product (fun q => (Section site N S q : Type)) (fun q=>Section site N S (q-1))).trans
        ((D.grading (CommRingCat.of S)).prodCongr
          ((GradedDirectSumSplit.shift (fun q => (Section site N S q : Type))).trans (D.grading (CommRingCat.of S))))))

theorem equiv_degree (q : ℤ) (a : Section site N (LaurentBasepoint.Laurent S) q) :
    equiv R S site N D K hs (includeDegree (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) q a)=
      (includeDegree (D.grading (CommRingCat.of S)) q (AffineSheafContraction.sheafAtOne R S site N q a),
      includeDegree (D.grading (CommRingCat.of S)) (q-1) (degreeResidue R S site N K hs q a)) := by
  change ((D.grading (CommRingCat.of S)).prodCongr
      ((GradedDirectSumSplit.shift (fun q => (Section site N S q : Type))).trans (D.grading (CommRingCat.of S))))
    (GradedDirectSumSplit.product (fun q => (Section site N S q : Type)) (fun q=>Section site N S (q-1))
      (DFinsupp.mapRange.addEquiv (ActualGradedLaurentSplit.equiv R S site N K hs)
        ((D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))).symm
          ((D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) (DirectSum.of _ q a)))))=_
  rw [AddEquiv.symm_apply_apply,GradedDirectSumSplit.congr_of]
  change ((D.grading (CommRingCat.of S)).prodCongr
      ((GradedDirectSumSplit.shift (fun q => (Section site N S q : Type))).trans (D.grading (CommRingCat.of S))))
    (GradedDirectSumSplit.product (fun q => (Section site N S q : Type)) (fun q=>Section site N S (q-1))
      (DirectSum.of _ q (AffineSheafContraction.sheafAtOne R S site N q a,
        degreeResidue R S site N K hs q a)))=_
  rw [GradedDirectSumSplit.product_of]
  apply Prod.ext
  · rfl
  · exact congrArg (D.grading (CommRingCat.of S))
      (GradedDirectSumSplit.shift_of (fun q => (Section site N S q : Type)) q (degreeResidue R S site N K hs q a))

def atOne : A →+* B := GradedMilnorWittSheaf.pullback site N D
  (S := CommRingCat.of (LaurentBasepoint.Laurent S)) (T := CommRingCat.of S)
  (LaurentBasepoint.atOne R S).toRingHom

theorem equiv_first (a : A) : (equiv R S site N D K hs a).1=atOne R S site N D a := by
  have h : (AddMonoidHom.fst B B).comp (equiv R S site N D K hs).toAddMonoidHom=
      (atOne R S site N D).toAddMonoidHom := by
    apply hom_ext (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
    intro q b
    simp only [AddMonoidHom.comp_apply,
      AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe]
    rw [equiv_degree]
    change includeDegree (D.grading (CommRingCat.of S)) q
      (AffineSheafContraction.sheafAtOne R S site N q b)=
      GradedMilnorWittSheaf.pullback site N D
        (S := CommRingCat.of (LaurentBasepoint.Laurent S)) (T := CommRingCat.of S)
        (LaurentBasepoint.atOne R S).toRingHom
        (includeDegree (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) q b)
    rw [GradedMilnorWittSheaf.pullback_degree]
    rfl
  exact congrArg (fun f : A →+ B => f a) h

theorem equiv_second (a : A) : (equiv R S site N D K hs a).2=
    GradedMilnorWittLaurent.residue R site N D K S hs a := by
  have h : (AddMonoidHom.snd B B).comp (equiv R S site N D K hs).toAddMonoidHom=
      GradedMilnorWittLaurent.residue R site N D K S hs := by
    apply hom_ext (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
    intro q b
    simp only [AddMonoidHom.comp_apply,
      AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe]
    rw [equiv_degree]
    exact (totalResidue_degree R S site N K hs
      (D.grading (CommRingCat.of S))
      (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) q b).symm
  exact congrArg (fun f : A →+ B => f a) h

theorem jointly_injective (a b : A) (h₁ : atOne R S site N D a=atOne R S site N D b)
    (h₂ : GradedMilnorWittLaurent.residue R site N D K S hs a=
      GradedMilnorWittLaurent.residue R site N D K S hs b) : a=b := by
  apply (equiv R S site N D K hs).injective
  apply Prod.ext
  · simpa only [equiv_first] using h₁
  · simpa only [equiv_second] using h₂

#print axioms equiv
#print axioms equiv_degree
#print axioms atOne
#print axioms equiv_first
#print axioms equiv_second
#print axioms jointly_injective
end Verification.GradedMilnorWittLaurentSplit
