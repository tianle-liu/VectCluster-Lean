/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SheafGradedLaurentResidue

/-!
# Sheaf Section Degree Transport

Transport degree-indexed section equivalences without replacing the
underlying sheaf pullback. This keeps all dependent group instances aligned.
-/
noncomputable section
namespace Verification.SheafSectionDegreeTransport
open CategoryTheory AlgebraicGeometry
open Verification.SheafGradedLaurentResidue
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable {S T : Type} [CommRing S] [CommRing T] {p q : ℤ}

def equiv (h : p=q) (E : Section site N S p ≃+ Section site N T p) :
    Section site N S q ≃+ Section site N T q := h ▸ E

theorem apply_eq (h : p=q) (E : Section site N S p ≃+ Section site N T p) (f : S →+* T)
    (hE : ∀ a,E a=ActualSheafContractionRestriction.pullback site (N p) f a)
    (a : Section site N S q) :
    equiv site N h E a=ActualSheafContractionRestriction.pullback site (N q) f a := by
  subst q
  exact hE a

#print axioms equiv
#print axioms apply_eq
end Verification.SheafSectionDegreeTransport
