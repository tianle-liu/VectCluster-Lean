/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittSheaf
import Verification.MilnorWittGradedLaurentNormalization

/-!
# Graded Milnor Witt Laurent

Uniform Laurent residues in the actual total coefficient-sheaf sections.
Constants vanish internally; the parameter rule follows from the ordinary
homogeneous MW contraction normalization over arbitrary smooth bases.
-/
noncomputable section
namespace Verification.GradedMilnorWittLaurent
open CategoryTheory AlgebraicGeometry Opposite
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S)

def residue : D.Total (CommRingCat.of (LaurentBasepoint.Laurent S)) →+ D.Total (CommRingCat.of S) :=
  totalResidue R S site N K hs (D.grading (CommRingCat.of S))
    (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))

def coefficient : D.Total (CommRingCat.of S) →+* D.Total (CommRingCat.of (LaurentBasepoint.Laurent S)) :=
  GradedMilnorWittSheaf.pullback site N D (LaurentBasepoint.coefficient R S).toRingHom

theorem constant (a : D.Total (CommRingCat.of S)) :
    residue R site N D K S hs (coefficient R site N D S a)=0 := by
  apply totalResidue_constant R S site N K hs (D.grading (CommRingCat.of S))
    (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S))) (coefficient R site N D S).toAddMonoidHom
  intro q b
  exact GradedMilnorWittSheaf.pullback_degree site N D
    (S := CommRingCat.of S) (T := CommRingCat.of (LaurentBasepoint.Laurent S))
    (LaurentBasepoint.coefficient R S).toRingHom q b

structure Standard : Prop where
  normalization : ∀ (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S),
    Nonempty (MilnorWittGradedLaurentNormalization.Standard R S site N K hs
      (D.grading (CommRingCat.of S)) (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
      (D.symbols (CommRingCat.of (LaurentBasepoint.Laurent S))) (coefficient R site N D S))

variable (P : Standard R site N D K)
include P

theorem parameter (a : D.Total (CommRingCat.of S)) :
    residue R site N D K S hs
      ((D.symbols (CommRingCat.of (LaurentBasepoint.Laurent S))).symbol
        (LaurentPolynomialUniversal.parameterUnit S)*coefficient R site N D S a)=a :=
  MilnorWittGradedLaurentNormalization.total_parameter R S site N K hs
    (D.grading (CommRingCat.of S)) (D.grading (CommRingCat.of (LaurentBasepoint.Laurent S)))
    (D.symbols (CommRingCat.of (LaurentBasepoint.Laurent S))) (coefficient R site N D S)
    (Classical.choice (P.normalization S hs)) a

#print axioms residue
#print axioms coefficient
#print axioms constant
#print axioms Standard
#print axioms parameter
end Verification.GradedMilnorWittLaurent
