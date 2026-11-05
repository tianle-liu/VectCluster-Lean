/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SheafGradedLaurentResidue
import Verification.MilnorWittSymbolRelations
import Verification.LaurentPolynomialUniversal

/-!
# Milnor Witt Graded Laurent Normalization

Ordinary homogeneous Laurent-symbol normalization, uniform in a smooth
coefficient algebra. Multiplication by the canonical parameter symbol raises
degree by one, and its genuine u=1 contraction removes that symbol. The total
constant/parameter residue rules are then theorems, not new total-map inputs.
There is no exchange matrix, stratum, cellular differential or path in this
reference interface.
-/
noncomputable section
namespace Verification.MilnorWittGradedLaurentNormalization
open CategoryTheory AlgebraicGeometry Opposite
open scoped DirectSum
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.MilnorWittSymbolRelations
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0})
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S)
variable {A B : Type*} [Ring A] [Ring B]
variable (E : (⨁ q,Section site N S q) ≃+ B)
variable (EL : (⨁ q,Section site N (LaurentBasepoint.Laurent S) q) ≃+ A)
variable (DL : Symbols (LaurentBasepoint.Laurent S) A) (F : B →+* A)

structure Standard where
  parameterSection : ∀ q, Section site N S q →+ Section site N (LaurentBasepoint.Laurent S) (q+1)
  parameter_symbol : ∀ q a, includeDegree EL (q+1) (parameterSection q a) =
    DL.symbol (LaurentPolynomialUniversal.parameterUnit S) * F (includeDegree E q a)
  contraction_parameter : ∀ q a,
    degreeResidue R S site N K hs (q+1) (parameterSection q a) =
      StandardThomContractionNormalization.degreeCast site N S q ((q+1)-1) (by omega) a

theorem includeDegree_cast (q q' : ℤ) (h : q=q') (a : Section site N S q) :
    includeDegree E q' (StandardThomContractionNormalization.degreeCast site N S q q' h a) =
      includeDegree E q a := by cases h; rfl

variable (P : Standard R S site N K hs E EL DL F)

include P in
theorem total_parameter_degree (q : ℤ) (a : Section site N S q) :
    totalResidue R S site N K hs E EL
      (DL.symbol (LaurentPolynomialUniversal.parameterUnit S) * F (includeDegree E q a)) =
    includeDegree E q a := by
  rw [← P.parameter_symbol,totalResidue_degree]
  change includeDegree E ((q+1)-1) (degreeResidue R S site N K hs (q+1) (P.parameterSection q a)) = _
  rw [P.contraction_parameter,includeDegree_cast]

def parameterProduct : B →+ A where
  toFun b := DL.symbol (LaurentPolynomialUniversal.parameterUnit S) * F b
  map_zero' := by rw [map_zero,mul_zero]
  map_add' a b := by rw [map_add,mul_add]

include P in
theorem total_parameter (b : B) :
    totalResidue R S site N K hs E EL
      (DL.symbol (LaurentPolynomialUniversal.parameterUnit S) * F b) = b := by
  have he : (totalResidue R S site N K hs E EL).comp (parameterProduct S DL F) = AddMonoidHom.id B := by
    apply hom_ext E
    intro q a
    exact total_parameter_degree R S site N K hs E EL DL F P q a
  exact DFunLike.congr_fun he b

#print axioms Standard
#print axioms includeDegree_cast
#print axioms total_parameter_degree
#print axioms parameterProduct
#print axioms total_parameter
end Verification.MilnorWittGradedLaurentNormalization
