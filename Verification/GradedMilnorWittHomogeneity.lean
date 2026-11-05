/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittSheaf

/-!
# Graded Milnor Witt Homogeneity

Ordinary grading of MW section-ring multiplication, unit symbols and
eta. These uniform inputs concern arbitrary affine rings and contain no
cellular differential or family-specific comparison.
-/
noncomputable section
namespace Verification.GradedMilnorWittHomogeneity
open CategoryTheory AlgebraicGeometry
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)

structure Standard where
  oneSection : ∀ S : CommRingCat.{0},Section site N S 0
  one_value : ∀ S,includeDegree (D.grading S) 0 (oneSection S)=1
  etaSection : ∀ S : CommRingCat.{0},Section site N S (-1)
  eta_value : ∀ S,includeDegree (D.grading S) (-1) (etaSection S)=(D.symbols S).eta
  unitSection : ∀ (S : CommRingCat.{0}),Sˣ → Section site N S 1
  unit_value : ∀ S u,includeDegree (D.grading S) 1 (unitSection S u)=(D.symbols S).symbol u
  multiply : ∀ (S : CommRingCat.{0}) (p q : ℤ),Section site N S p → Section site N S q → Section site N S (p+q)
  multiply_value : ∀ S p q a b,includeDegree (D.grading S) (p+q) (multiply S p q a b)=
    includeDegree (D.grading S) p a*includeDegree (D.grading S) q b

def Homogeneous (S : CommRingCat.{0}) (q : ℤ) (a : D.Total S) : Prop :=
  ∃ b : Section site N S q,includeDegree (D.grading S) q b=a

variable {site N D}

theorem zero (S : CommRingCat.{0}) (q : ℤ) : Homogeneous site N D S q 0 := ⟨0,map_zero _⟩

theorem add {S : CommRingCat.{0}} {q : ℤ} {a b : D.Total S}
    (ha : Homogeneous site N D S q a) (hb : Homogeneous site N D S q b) :
    Homogeneous site N D S q (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b,map_add _ a b⟩

theorem neg {S : CommRingCat.{0}} {q : ℤ} {a : D.Total S}
    (ha : Homogeneous site N D S q a) : Homogeneous site N D S q (-a) := by
  obtain ⟨a,rfl⟩ := ha
  exact ⟨-a,map_neg _ a⟩

theorem mul (P : Standard site N D) {S : CommRingCat.{0}} {p q : ℤ} {a b : D.Total S}
    (ha : Homogeneous site N D S p a) (hb : Homogeneous site N D S q b) :
    Homogeneous site N D S (p+q) (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨P.multiply S p q a b,P.multiply_value S p q a b⟩

theorem pullback {S T : CommRingCat.{0}} (f : S →+* T) {q : ℤ} {a : D.Total S}
    (ha : Homogeneous site N D S q a) :
    Homogeneous site N D T q (GradedMilnorWittSheaf.pullback site N D f a) := by
  obtain ⟨a,rfl⟩ := ha
  exact ⟨ActualSheafContractionRestriction.pullback site (N q) f a,
    (GradedMilnorWittSheaf.pullback_degree site N D f q a).symm⟩

theorem rho (P : Standard site N D) (S : CommRingCat.{0}) : Homogeneous site N D S 1 (D.symbols S).rho := by
  refine ⟨P.unitSection S (-1),?_⟩
  rw [P.unit_value,(D.symbols S).negative,(D.symbols S).one,mul_zero,add_zero]

theorem g (P : Standard site N D) (S : CommRingCat.{0}) : Homogeneous site N D S 0 (D.symbols S).g := by
  have hη : Homogeneous site N D S (-1) (D.symbols S).eta := ⟨P.etaSection S,P.eta_value S⟩
  have hρ := rho P S
  have hprod : Homogeneous site N D S 0 ((D.symbols S).eta*(D.symbols S).rho) := by
    simpa using mul P hη hρ
  have hone : Homogeneous site N D S 0 (1 : D.Total S) := ⟨P.oneSection S,P.one_value S⟩
  have h := add hone hprod
  have he : 1+(D.symbols S).eta*(D.symbols S).rho=(D.symbols S).g := by
    rw [(D.symbols S).eta_rho]
    abel
  exact he ▸ h

#print axioms Standard
#print axioms Homogeneous
#print axioms zero
#print axioms add
#print axioms neg
#print axioms mul
#print axioms pullback
#print axioms rho
#print axioms g
end Verification.GradedMilnorWittHomogeneity
