/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittSheaf

/-!
# Graded Milnor Witt Sheaf Equiv

Algebra isomorphisms act invertibly on actual total sheaf sections,
by functoriality of the constructed sheaf pullback.
-/
noncomputable section
namespace Verification.GradedMilnorWittSheafEquiv
open CategoryTheory AlgebraicGeometry
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable {S T : CommRingCat.{0}}

def equiv (e : S ≃+* T) : D.Total S ≃+* D.Total T :=
  RingEquiv.ofRingHom (GradedMilnorWittSheaf.pullback site N D e.toRingHom)
    (GradedMilnorWittSheaf.pullback site N D e.symm.toRingHom)
    (by rw [← GradedMilnorWittSheaf.pullback_comp,RingEquiv.toRingHom_comp_symm_toRingHom]
        exact GradedMilnorWittSheaf.pullback_id site N D)
    (by rw [← GradedMilnorWittSheaf.pullback_comp,RingEquiv.symm_toRingHom_comp_toRingHom]
        exact GradedMilnorWittSheaf.pullback_id site N D)

theorem equiv_apply (e : S ≃+* T) (a : D.Total S) :
    equiv site N D e a=GradedMilnorWittSheaf.pullback site N D e.toRingHom a := rfl

theorem equiv_symm_apply (e : S ≃+* T) (a : D.Total T) :
    (equiv site N D e).symm a=GradedMilnorWittSheaf.pullback site N D e.symm.toRingHom a := rfl

#print axioms equiv
#print axioms equiv_apply
#print axioms equiv_symm_apply
end Verification.GradedMilnorWittSheafEquiv
