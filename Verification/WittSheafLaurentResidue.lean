/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WittSheafSectionsInput

/-!
# Witt Sheaf Laurent Residue

Actual Witt Laurent residues, transported from the genuine sheaf
contraction. The constant, parameter, and parity formulas are proved for
this fixed map; no article coordinate outputs are assumed.
-/
noncomputable section
namespace Verification.WittSheafLaurentResidue
open CategoryTheory AlgebraicGeometry Opposite
open Verification.WittSheafSectionsInput
variable (R : Type) [CommRing R] (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0})
variable (D : Symbols R W) (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (E : Comparison R W site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (L : LaurentNormalization R W D site N E K)
variable (S : Type) [CommRing S] [Algebra R S] (hs : Algebra.Smooth R S)

def laurentSmooth : Algebra.Smooth R (LaurentBasepoint.Laurent S) := by
  letI := hs
  exact ActualOldFiberSmooth.laurent_smooth R S

def residue (q : ℤ) : RingSection W (LaurentBasepoint.Laurent S) →+ RingSection W S :=
  (E.sections S hs (q-1)).symm.toAddMonoidHom.comp
    ((SheafGradedLaurentResidue.degreeResidue R S site N K hs q).comp
      (E.sections (LaurentBasepoint.Laurent S) (laurentSmooth R S hs) q).toAddMonoidHom)

theorem residue_constant (q : ℤ) (a : RingSection W S) :
    residue R W site N E K S hs q (pullback W (LaurentBasepoint.coefficient R S).toRingHom a) = 0 := by
  change (E.sections S hs (q-1)).symm
    (SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (E.sections (LaurentBasepoint.Laurent S) (laurentSmooth R S hs) q
        (pullback W (LaurentBasepoint.coefficient R S).toRingHom a))) = 0
  rw [E.natural S (LaurentBasepoint.Laurent S) hs (laurentSmooth R S hs)
    (LaurentBasepoint.coefficient R S)]
  change (E.sections S hs (q-1)).symm
    (SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (SheafReducedProjection.coefficientPullback R S site N q (E.sections S hs q a))) = 0
  rw [SheafGradedLaurentResidue.degreeResidue_coefficient,map_zero]

include L in
theorem residue_parameter (q : ℤ) (a : RingSection W S) :
    residue R W site N E K S hs q
      (form R W D (LaurentBasepoint.Laurent S) (laurentSmooth R S hs)
        (LaurentPolynomialUniversal.parameterUnit S) *
        pullback W (LaurentBasepoint.coefficient R S).toRingHom a) = a := by
  change (E.sections S hs (q-1)).symm
    (SheafGradedLaurentResidue.degreeResidue R S site N K hs q
      (E.sections (LaurentBasepoint.Laurent S) (laurentSmooth R S hs) q
        (form R W D (LaurentBasepoint.Laurent S) (laurentSmooth R S hs)
          (LaurentPolynomialUniversal.parameterUnit S) *
            pullback W (LaurentBasepoint.coefficient R S).toRingHom a))) = a
  rw [L.parameter S hs q a]
  exact (E.sections S hs (q-1)).symm_apply_apply a

theorem involution_power {A : Type*} [Monoid A] (g : A) (hg : g*g=1) (n : ℕ) :
    g^n = g^(n%2) := by
  have hg2 : g^2=1 := by simpa only [pow_two] using hg
  conv_lhs => rw [← Nat.mod_add_div n 2,pow_add,pow_mul,hg2,one_pow,mul_one]

include L in
theorem residue_parity (q : ℤ) (a : RingSection W S) (n : ℕ) :
    residue R W site N E K S hs q
      ((form R W D (LaurentBasepoint.Laurent S) (laurentSmooth R S hs)
        (LaurentPolynomialUniversal.parameterUnit S))^n *
        pullback W (LaurentBasepoint.coefficient R S).toRingHom a) =
      if n%2=0 then 0 else a := by
  rw [involution_power _ (form_square R W D _ _ _) n]
  have h : n%2 < 2 := Nat.mod_lt n (by decide)
  by_cases he : n%2=0
  · simp only [he,pow_zero,one_mul,if_pos]
    exact residue_constant R W site N E K S hs q a
  · have ho : n%2=1 := by omega
    simp only [ho,pow_one,one_ne_zero,if_false]
    exact residue_parameter R W D site N E K L S hs q a

#print axioms laurentSmooth
#print axioms residue
#print axioms residue_constant
#print axioms residue_parameter
#print axioms involution_power
#print axioms residue_parity
end Verification.WittSheafLaurentResidue
