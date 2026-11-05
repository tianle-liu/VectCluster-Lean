/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictModelEulerClassification
import Verification.ChowWittNisnevichInput

/-!
# Ordinary Euler Normalization Input

Ordinary Postnikov/Euler data, uniformly for every smooth affine
domain over the ground field. The normalization fixes the ordinary Euler
value on a trivial oriented projective module at zero. No cohomological
bound or classification of any exchange algebra is part of this input.
-/
noncomputable section
namespace Verification.OrdinaryEulerNormalizationInput
open CategoryTheory AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] (L : DerivedCategory C ⥤ D)
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (T : StrictNisnevichInput.Theory A) (k : Type) [Field k]
variable (NR : StrictNisnevichRepresentability.Standard J L G T k)
variable (MW : ℕ → A) (CW : Scheme → ℕ → AddCommGrp)
variable (CWRef : ChowWittNisnevichInput.Standard J L G T k NR MW CW)
variable (Factor : Type*) [Group Factor]

abbrev Ambient (S : Type) [CommRing S] :=
  L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S)))) ⟶
    J.obj (StrictCoefficientComparison.target (MW 2) 2)

structure Standard where
  factorAction : ∀ (S : Type) [CommRing S] [Algebra k S], MulAction Factor (Ambient J L G MW S)
  stages : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S],
    AmbientPostnikovStages.EulerStages (R := S) J
      (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of S))))) (MW 2)
  euler : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S],
    letI := factorAction S
    letI := CWRef.ambientAction S 2
    StrictModelEulerClassification.StandardEuler (stages S) Factor
  trivial_zero : ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S]
    (P : ActualOrientations.Oriented S 2),
    ActualProjectiveSplitting.Trivial P.bundle →
      letI := factorAction S
      letI := CWRef.ambientAction S 2
      (euler S).chowWitt (Quotient.mk _ P)=0

variable (O : Standard J L G T k NR MW CW CWRef Factor)
variable (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S]

def chowWitt : ActualOrientations.Classes (R := S) (r := 2) → CW (Spec (CommRingCat.of S)) 2 := by
  letI := O.factorAction S
  letI := CWRef.ambientAction S 2
  exact fun P => (ChowWittNisnevichInput.ambientEquiv J L G T k NR MW CW CWRef S 2).symm
    ((O.euler S).chowWitt P)

omit [J.Additive] in
theorem chowWitt_zero (P : ActualOrientations.Oriented S 2)
    (hP : ActualProjectiveSplitting.Trivial P.bundle) :
    chowWitt J L G T k NR MW CW CWRef Factor O S (Quotient.mk _ P)=0 := by
  letI := O.factorAction S
  letI := CWRef.ambientAction S 2
  unfold chowWitt
  rw [O.trivial_zero S P hP,map_zero]

omit [J.Additive] in
theorem chowWitt_unit (u : Sˣ) (P : ActualOrientations.Oriented S 2) :
    letI := CWRef.unitAction S 2
    chowWitt J L G T k NR MW CW CWRef Factor O S
      (Quotient.mk _ (ActualOrientations.changeOrientation u P))=
      u • chowWitt J L G T k NR MW CW CWRef Factor O S (Quotient.mk _ P) := by
  letI := O.factorAction S
  letI := CWRef.unitAction S 2
  letI := CWRef.ambientAction S 2
  apply (ChowWittNisnevichInput.ambientEquiv J L G T k NR MW CW CWRef S 2).injective
  rw [ChowWittNisnevichInput.ambient_smul]
  simp only [chowWitt,AddEquiv.apply_symm_apply]
  exact (O.euler S).unit_action u P

#print axioms Ambient
#print axioms Standard
#print axioms chowWitt
#print axioms chowWitt_zero
#print axioms chowWitt_unit
end Verification.OrdinaryEulerNormalizationInput
