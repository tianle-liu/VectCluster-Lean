/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittLaurentSplit

/-!
# Graded Milnor Witt Laurent Words

The two actual Laurent summands have the concrete word representatives
1 and the ordinary parameter symbol. The resulting residue is linear over
coefficient sections on the right.
-/
noncomputable section
namespace Verification.GradedMilnorWittLaurentWords
open CategoryTheory AlgebraicGeometry
open Verification.GradedMilnorWittLaurentSplit
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S)
local notation "B" => D.Total (CommRingCat.of S)
local notation "A" => D.Total (CommRingCat.of (LaurentBasepoint.Laurent S))
local notation "F" => GradedMilnorWittLaurent.coefficient R site N D S
local notation "r" => GradedMilnorWittLaurent.residue R site N D K S hs
def parameterSymbol : A :=
  (D.symbols (CommRingCat.of (LaurentBasepoint.Laurent S))).symbol (LaurentPolynomialUniversal.parameterUnit S)
local notation "u" => parameterSymbol S site N D

theorem atOne_coefficient (a : B) : atOne R S site N D (F a)=a := by
  have h : (atOne R S site N D).comp F=RingHom.id B := by
    unfold atOne GradedMilnorWittLaurent.coefficient
    rw [← GradedMilnorWittSheaf.pullback_comp]
    rw [show (LaurentBasepoint.atOne R S).toRingHom.comp
      (LaurentBasepoint.coefficient R S).toRingHom=RingHom.id S from
      congrArg AlgHom.toRingHom (LaurentBasepoint.atOne_coefficient R S)]
    exact GradedMilnorWittSheaf.pullback_id site N D
  exact RingHom.congr_fun h a

theorem atOne_parameter : atOne R S site N D u=0 := by
  unfold atOne parameterSymbol
  rw [GradedMilnorWittSheaf.pullback_symbol]
  have h : Units.map (LaurentBasepoint.atOne R S).toRingHom.toMonoidHom
      (LaurentPolynomialUniversal.parameterUnit S)=1 := by
    apply Units.ext
    change LaurentBasepoint.atOne R S (LaurentPolynomialUniversal.parameterUnit S : LaurentBasepoint.Laurent S)=1
    rw [LaurentPolynomialUniversal.parameterUnit_val]
    exact LaurentBasepoint.atOne_parameter R S
  rw [h]
  exact (D.symbols (CommRingCat.of S)).one

variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem inverse_words (a b : B) : (equiv R S site N D K hs).symm (a,b)=F a+u*F b := by
  apply (equiv R S site N D K hs).injective
  rw [AddEquiv.apply_symm_apply]
  symm
  apply Prod.ext
  · rw [equiv_first,map_add,map_mul,atOne_coefficient,atOne_parameter,zero_mul,add_zero]
  · unfold parameterSymbol
    rw [equiv_second,map_add,GradedMilnorWittLaurent.constant,
      GradedMilnorWittLaurent.parameter R site N D K S hs P,zero_add]

theorem expansion (a : A) : a=F (atOne R S site N D a)+u*F (r a) := by
  calc
    a=(equiv R S site N D K hs).symm (equiv R S site N D K hs a) :=
      (AddEquiv.symm_apply_apply _ a).symm
    _=F (equiv R S site N D K hs a).1+u*F (equiv R S site N D K hs a).2 :=
      inverse_words R S site N D K hs P _ _
    _=_ := by rw [equiv_first,equiv_second]

theorem residue_coefficient_mul (a : A) (b : B) : r (a*F b)=r a*b := by
  conv_lhs => rw [expansion R S site N D K hs P a]
  unfold parameterSymbol
  rw [add_mul,mul_assoc,← map_mul,← map_mul,map_add,
    GradedMilnorWittLaurent.constant,GradedMilnorWittLaurent.parameter R site N D K S hs P,zero_add]

#print axioms parameterSymbol
#print axioms atOne_coefficient
#print axioms atOne_parameter
#print axioms inverse_words
#print axioms expansion
#print axioms residue_coefficient_mul
end Verification.GradedMilnorWittLaurentWords
