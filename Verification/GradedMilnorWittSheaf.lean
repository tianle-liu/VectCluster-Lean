/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedSheafRingPullback
import Verification.MilnorWittSymbolNaturality

/-!
# Graded Milnor Witt Sheaf

Uniform ordinary Milnor-Witt section-ring input. Each total ring is
identified with the direct sum of the actual sheaf sections, and every
pullback is constructed from those sheaf maps. The only reference facts are
the graded multiplication and ordinary symbol relations/naturality.
-/
noncomputable section
namespace Verification.GradedMilnorWittSheaf
open CategoryTheory AlgebraicGeometry Opposite
open scoped DirectSum
open Verification.SheafGradedLaurentResidue Verification.GradedSectionTotal
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))

structure Standard where
  Total : CommRingCat.{0} → Type
  ring : ∀ S,Ring (Total S)
  grading : ∀ S,letI := ring S; (⨁ q,Section site N S q) ≃+ Total S
  symbols : ∀ S,letI := ring S; Symbols S (Total S)
  multiplicative : ∀ {S T : CommRingCat.{0}} (f : S →+* T),
    letI := ring S; letI := ring T
    GradedSheafRingPullback.Multiplicative site N (grading S) (grading T) f
  naturality : ∀ {S T : CommRingCat.{0}} (f : S →+* T),
    letI := ring S; letI := ring T
    Compatible (symbols S) (symbols T) f
      (GradedSheafRingPullback.ringHom site N (grading S) (grading T) f (multiplicative f))

attribute [instance] Standard.ring
variable (D : Standard site N)
variable {S T U : CommRingCat.{0}}

def pullback (f : S →+* T) : D.Total S →+* D.Total T :=
  GradedSheafRingPullback.ringHom site N (D.grading S) (D.grading T) f (D.multiplicative f)

theorem pullback_degree (f : S →+* T) (q : ℤ) (a : Section site N S q) :
    pullback site N D f (includeDegree (D.grading S) q a)=
      includeDegree (D.grading T) q (ActualSheafContractionRestriction.pullback site (N q) f a) :=
  GradedSheafRingPullback.ringHom_degree site N (D.grading S) (D.grading T) f (D.multiplicative f) q a

theorem pullback_comp (f : S →+* T) (g : T →+* U) :
    pullback site N D (g.comp f)=(pullback site N D g).comp (pullback site N D f) :=
  GradedSheafRingPullback.ringHom_comp site N (D.grading S) (D.grading T) (D.grading U) f g
    (D.multiplicative f) (D.multiplicative g) (D.multiplicative (g.comp f))

theorem pullback_id : pullback site N D (RingHom.id S)=RingHom.id (D.Total S) := by
  apply RingHom.ext
  intro a
  exact congrArg (fun h : D.Total S →+ D.Total S => h a)
    (GradedSheafRingPullback.additive_id site N (D.grading S))

theorem compatible (f : S →+* T) :
    Compatible (D.symbols S) (D.symbols T) f (pullback site N D f) := D.naturality f

theorem pullback_symbol (f : S →+* T) (u : Sˣ) :
    pullback site N D f ((D.symbols S).symbol u)=(D.symbols T).symbol (Units.map f.toMonoidHom u) :=
  (compatible site N D f).symbol u

#print axioms Standard
#print axioms pullback
#print axioms pullback_degree
#print axioms pullback_comp
#print axioms pullback_id
#print axioms compatible
#print axioms pullback_symbol
end Verification.GradedMilnorWittSheaf
