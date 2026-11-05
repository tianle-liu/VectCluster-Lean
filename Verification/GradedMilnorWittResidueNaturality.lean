/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittLaurent
import Verification.SheafContractionNaturality

/-!
# Graded Milnor Witt Residue Naturality

The actual total Laurent residue commutes with ordinary coefficient base
change. Both the reduced kernel and the total section action are constructed.
-/
noncomputable section
namespace Verification.GradedMilnorWittResidueNaturality
open CategoryTheory AlgebraicGeometry Opposite
open Verification.SheafGradedLaurentResidue Verification.GradedSectionTotal
variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (f : S →ₐ[R] T)

theorem coefficient_square :
    (LaurentSheafBaseChange.laurentMap R S T f).comp (LaurentBasepoint.coefficient R S)=
      (LaurentBasepoint.coefficient R T).comp f := by
  ext a
  exact LaurentSheafBaseChange.map_coefficient R S T f a

theorem coefficient_pullback (q : ℤ) (a : Section site N S q) :
    ActualSheafContractionRestriction.pullback site (N q) (LaurentSheafBaseChange.laurentMap R S T f).toRingHom
      (SheafReducedProjection.coefficientPullback R S site N q a)=
    SheafReducedProjection.coefficientPullback R T site N q
      (ActualSheafContractionRestriction.pullback site (N q) f.toRingHom a) := by
  have h := congrArg (fun g : S →ₐ[R] LaurentBasepoint.Laurent T =>
    ActualSheafContractionRestriction.pullback site (N q) g.toRingHom) (coefficient_square R S T f)
  change ActualSheafContractionRestriction.pullback site (N q)
      ((LaurentSheafBaseChange.laurentMap R S T f).toRingHom.comp (LaurentBasepoint.coefficient R S).toRingHom)=
    ActualSheafContractionRestriction.pullback site (N q)
      ((LaurentBasepoint.coefficient R T).toRingHom.comp f.toRingHom) at h
  rw [ActualSheafContractionRestriction.pullback_comp,ActualSheafContractionRestriction.pullback_comp] at h
  exact congrArg (fun z : Section site N S q →+ Section site N (LaurentBasepoint.Laurent T) q => z a) h

theorem reduce_naturality (q : ℤ) (a : Section site N (LaurentBasepoint.Laurent S) q) :
    LaurentSheafBaseChange.kernelMap R S T f site N q (reduce R S site N q a)=
      reduce R T site N q (ActualSheafContractionRestriction.pullback site (N q)
        (LaurentSheafBaseChange.laurentMap R S T f).toRingHom a) := by
  apply Subtype.ext
  change ActualSheafContractionRestriction.pullback site (N q) _
    (a-SheafReducedProjection.coefficientPullback R S site N q (AffineSheafContraction.sheafAtOne R S site N q a))=_
  rw [map_sub,coefficient_pullback]
  change _=_-SheafReducedProjection.coefficientPullback R T site N q
    (AffineSheafContraction.sheafAtOne R T site N q
      (ActualSheafContractionRestriction.pullback site (N q) _ a))
  rw [LaurentSheafBaseChange.kernel_square]

variable (K : StandardThomContractionNormalization.Grading R site N)
variable (H : SheafContractionNaturality.Standard R site N K)
variable (hs : Algebra.Smooth R S) (ht : Algebra.Smooth R T)
include H

theorem degree_naturality (q : ℤ) (a : Section site N (LaurentBasepoint.Laurent S) q) :
    degreeResidue R T site N K ht q (ActualSheafContractionRestriction.pullback site (N q)
      (LaurentSheafBaseChange.laurentMap R S T f).toRingHom a)=
    ActualSheafContractionRestriction.pullback site (N (q-1)) f.toRingHom
      (degreeResidue R S site N K hs q a) := by
  change K.contract T ht q (reduce R T site N q _)=_
  rw [← reduce_naturality]
  exact H.naturality S T hs ht f q _

variable (D : GradedMilnorWittSheaf.Standard site N)

theorem total_naturality (a : D.Total (CommRingCat.of (LaurentBasepoint.Laurent S))) :
    GradedMilnorWittLaurent.residue R site N D K T ht
      (GradedMilnorWittSheaf.pullback site N D (LaurentSheafBaseChange.laurentMap R S T f).toRingHom a)=
    GradedMilnorWittSheaf.pullback site N D f.toRingHom
      (GradedMilnorWittLaurent.residue R site N D K S hs a) := by
  have hh : (GradedMilnorWittLaurent.residue R site N D K T ht).comp
      (GradedMilnorWittSheaf.pullback site N D (LaurentSheafBaseChange.laurentMap R S T f).toRingHom).toAddMonoidHom=
    (GradedMilnorWittSheaf.pullback site N D f.toRingHom).toAddMonoidHom.comp
      (GradedMilnorWittLaurent.residue R site N D K S hs) := by
    apply hom_ext (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
    intro q b
    change totalResidue R T site N K ht (D.grading (CommRingCat.of T))
      (D.grading (CommRingCat.of (LaurentBasepoint.Laurent T)))
      (GradedMilnorWittSheaf.pullback site N D (LaurentSheafBaseChange.laurentMap R S T f).toRingHom
        (includeDegree (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) q b))=
      GradedMilnorWittSheaf.pullback site N D f.toRingHom
        (totalResidue R S site N K hs (D.grading (CommRingCat.of S))
          (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
          (includeDegree (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) q b))
    rw [GradedMilnorWittSheaf.pullback_degree,totalResidue_degree,totalResidue_degree,
      GradedMilnorWittSheaf.pullback_degree]
    exact congrArg (includeDegree (D.grading (CommRingCat.of T)) (q-1))
      (degree_naturality R S T site N f K H hs ht q b)
  exact congrArg (fun h : D.Total (CommRingCat.of (LaurentBasepoint.Laurent S)) →+
    D.Total (CommRingCat.of T) => h a) hh

#print axioms coefficient_square
#print axioms coefficient_pullback
#print axioms reduce_naturality
#print axioms degree_naturality
#print axioms total_naturality
end Verification.GradedMilnorWittResidueNaturality
