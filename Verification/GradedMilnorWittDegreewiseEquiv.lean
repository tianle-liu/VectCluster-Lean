/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittSheaf

/-!
# Graded Milnor Witt Degreewise Equiv

Isomorphisms on the actual sheaf sections in every degree give an
isomorphism on their genuine total section ring. The map is still the
original ring pullback, not an independently chosen ring identification.
-/
noncomputable section
namespace Verification.GradedMilnorWittDegreewiseEquiv
open CategoryTheory AlgebraicGeometry
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open scoped DirectSum
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N) {S T : CommRingCat.{0}}
variable (E : ∀ q,Section site N S q ≃+ Section site N T q)

def total : D.Total S ≃+ D.Total T :=
  (D.grading S).symm.trans ((AddEquiv.ofBijective (DirectSum.map (fun q => (E q).toAddMonoidHom))
    ⟨(DirectSum.map_injective _).mpr (fun q => (E q).injective),
      (DirectSum.map_surjective _).mpr (fun q => (E q).surjective)⟩).trans (D.grading T))

theorem total_degree (q : ℤ) (a : Section site N S q) :
    total site N D E (includeDegree (D.grading S) q a)=
      includeDegree (D.grading T) q (E q a) := by
  simp only [total,includeDegree,AddEquiv.trans_apply,AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe,AddMonoidHom.coe_coe,AddEquiv.symm_apply_apply]
  congr 1
  exact DirectSum.map_of _ _ _

variable (f : S →+* T)
variable (h : ∀ q a,E q a=ActualSheafContractionRestriction.pullback site (N q) f a)

include h in
theorem total_pullback : (total site N D E).toAddMonoidHom=
    (GradedMilnorWittSheaf.pullback site N D f).toAddMonoidHom := by
  apply hom_ext (D.grading S)
  intro q a
  change total site N D E (includeDegree (D.grading S) q a)=
    GradedMilnorWittSheaf.pullback site N D f (includeDegree (D.grading S) q a)
  rw [total_degree,h,GradedMilnorWittSheaf.pullback_degree]

def equiv : D.Total S ≃+* D.Total T :=
  RingEquiv.ofBijective (GradedMilnorWittSheaf.pullback site N D f) (by
    have hh:=congrArg DFunLike.coe (total_pullback site N D E f h)
    change Function.Bijective ((GradedMilnorWittSheaf.pullback site N D f).toAddMonoidHom : D.Total S → D.Total T)
    rw [←hh]
    exact (total site N D E).bijective)

theorem equiv_apply (a : D.Total S) : equiv site N D E f h a=GradedMilnorWittSheaf.pullback site N D f a := rfl

#print axioms total
#print axioms total_degree
#print axioms total_pullback
#print axioms equiv
#print axioms equiv_apply
end Verification.GradedMilnorWittDegreewiseEquiv
