/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Split Exchange Chart

An actual simultaneous exchange-chart equivalence. The Laurent algebra on
symbols t_i is defined as the localization of R[t_i] at the submonoid generated
by all t_i. Quotienting by t_i=r_i gives precisely R[r_i^{-1}:i]. Taking
R to be the polynomial ring on x_i,y_i and r_i=x_i*y_i-1 gives the local
chart used in manuscript.tex:390–408, without assuming a presentation
equivalence or identifying rings only through field-valued points.
-/

noncomputable section

namespace Verification.SplitExchangeChart

open MvPolynomial

variable {R S ι : Type*} [CommRing R] [CommRing S]

theorem units_on_closure (f : R →+* S) (r : ι → R)
    (h : ∀ i, IsUnit (f (r i))) (m : Submonoid.closure (Set.range r)) :
    IsUnit (f m.val) := by
  rcases m with ⟨m, hm⟩
  change IsUnit (f m)
  induction hm using Submonoid.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | one => simpa only [map_one] using (isUnit_one : IsUnit (1 : S))
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

variable (R ι)

def variableMonoid : Submonoid (MvPolynomial ι R) :=
  Submonoid.closure (Set.range (X : ι → MvPolynomial ι R))

/-- The actual Laurent polynomial algebra on the indicated generators. -/
abbrev Laurent := Localization (variableMonoid R ι)

def laurentVariable (i : ι) : Laurent R ι :=
  algebraMap (MvPolynomial ι R) (Laurent R ι) (X i)

theorem laurentVariable_unit (i : ι) : IsUnit (laurentVariable R ι i) :=
  IsLocalization.map_units (M := variableMonoid R ι) (Laurent R ι)
    ⟨X i, Submonoid.subset_closure (Set.mem_range_self i)⟩

variable {R ι}

def valueMonoid (r : ι → R) : Submonoid R := Submonoid.closure (Set.range r)

abbrev ValueLocalization (r : ι → R) := Localization (valueMonoid r)

def relation (r : ι → R) (i : ι) : Laurent R ι :=
  algebraMap R (Laurent R ι) (r i) - laurentVariable R ι i

def relations (r : ι → R) : Ideal (Laurent R ι) := Ideal.span (Set.range (relation r))

abbrev ExchangeQuotient (r : ι → R) := Laurent R ι ⧸ relations r

def polynomialEvaluation (r : ι → R) : MvPolynomial ι R →+* ValueLocalization r :=
  eval₂Hom (algebraMap R (ValueLocalization r)) (fun i => algebraMap R _ (r i))

theorem polynomialEvaluation_units (r : ι → R) (m : variableMonoid R ι) :
    IsUnit (polynomialEvaluation r m.val) := by
  apply units_on_closure (polynomialEvaluation r) X _ m
  intro i
  simp only [polynomialEvaluation, eval₂Hom_X']
  exact IsLocalization.map_units (M := valueMonoid r) (ValueLocalization r)
    ⟨r i, Submonoid.subset_closure (Set.mem_range_self i)⟩

def laurentEvaluation (r : ι → R) : Laurent R ι →+* ValueLocalization r :=
  IsLocalization.lift (M := variableMonoid R ι) (polynomialEvaluation_units r)

theorem evaluation_coefficient (r : ι → R) (a : R) :
    laurentEvaluation r (algebraMap R (Laurent R ι) a) =
      algebraMap R (ValueLocalization r) a := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Laurent R ι)]
  simp only [laurentEvaluation, IsLocalization.lift_eq, MvPolynomial.algebraMap_eq,
    polynomialEvaluation, eval₂Hom_C]

theorem evaluation_variable (r : ι → R) (i : ι) :
    laurentEvaluation r (laurentVariable R ι i) =
      algebraMap R (ValueLocalization r) (r i) := by
  simp only [laurentVariable, laurentEvaluation, IsLocalization.lift_eq,
    polynomialEvaluation, eval₂Hom_X']

theorem evaluation_relation (r : ι → R) (i : ι) :
    laurentEvaluation r (relation r i) = 0 := by
  rw [relation, map_sub, evaluation_coefficient, evaluation_variable, sub_self]

def descend (r : ι → R) : ExchangeQuotient r →+* ValueLocalization r :=
  Ideal.Quotient.lift (relations r) (laurentEvaluation r) (by
    intro z hz
    have hker : relations r ≤ RingHom.ker (laurentEvaluation r) := by
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      exact evaluation_relation r i
    exact hker hz)

def quotientCoefficient (r : ι → R) : R →+* ExchangeQuotient r :=
  (Ideal.Quotient.mk (relations r)).comp (algebraMap R (Laurent R ι))

theorem quotient_generator_eq (u v : ι → R) (i : ι) :
    Ideal.Quotient.mk (Ideal.span (Set.range (fun j => u j - v j))) (u i) =
      Ideal.Quotient.mk (Ideal.span (Set.range (fun j => u j - v j))) (v i) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (Set.mem_range_self i)

theorem quotient_variable (r : ι → R) (i : ι) :
    Ideal.Quotient.mk (relations r) (laurentVariable R ι i) = quotientCoefficient r (r i) := by
  exact (quotient_generator_eq (fun j => algebraMap R (Laurent R ι) (r j))
    (laurentVariable R ι) i).symm

theorem quotient_coefficient_units (r : ι → R) (m : valueMonoid r) :
    IsUnit (quotientCoefficient r m.val) := by
  apply units_on_closure (quotientCoefficient r) r _ m
  intro i
  rw [← quotient_variable]
  exact (laurentVariable_unit R ι i).map (Ideal.Quotient.mk (relations r))

def includeBase (r : ι → R) : ValueLocalization r →+* ExchangeQuotient r :=
  IsLocalization.lift (M := valueMonoid r) (quotient_coefficient_units r)

theorem descend_includeBase (r : ι → R) :
    (descend r).comp (includeBase r) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (valueMonoid r)
  apply RingHom.ext
  intro a
  change descend r (includeBase r (algebraMap R (ValueLocalization r) a)) = _
  rw [includeBase, IsLocalization.lift_eq]
  exact evaluation_coefficient r a

theorem includeBase_descend (r : ι → R) :
    (includeBase r).comp (descend r) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (variableMonoid R ι)
  apply MvPolynomial.ringHom_ext
  · intro a
    change includeBase r (laurentEvaluation r
      (algebraMap (MvPolynomial ι R) (Laurent R ι) (C a))) = _
    rw [← MvPolynomial.algebraMap_eq R ι,
      ← IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Laurent R ι),
      evaluation_coefficient]
    rw [includeBase, IsLocalization.lift_eq]
    rfl
  · intro i
    change includeBase r (laurentEvaluation r (laurentVariable R ι i)) = _
    rw [evaluation_variable, includeBase, IsLocalization.lift_eq]
    exact (quotient_variable r i).symm

/-- Simultaneously impose every exchange chart equation and remove its Laurent
coordinate, by explicitly inverse universal-localization maps. -/
def quotientRingEquiv (r : ι → R) : ExchangeQuotient r ≃+* ValueLocalization r :=
  RingEquiv.ofRingHom (descend r) (includeBase r)
    (descend_includeBase r) (includeBase_descend r)

def quotientEquiv (r : ι → R) : ExchangeQuotient r ≃ₐ[R] ValueLocalization r :=
  AlgEquiv.ofRingEquiv (f := quotientRingEquiv r) (fun a => evaluation_coefficient r a)

section FiniteLocalization

variable [Fintype ι]

/-- Inverting finitely many prescribed values is the principal open obtained
by inverting their product. This includes the empty index set. -/
theorem awayProduct_isLocalization (r : ι → R) :
    IsLocalization (valueMonoid r) (Localization.Away (∏ i, r i)) := by
  apply IsLocalization.of_le (Submonoid.powers (∏ i, r i)) (valueMonoid r)
  · apply Submonoid.powers_le.mpr
    exact (valueMonoid r).prod_mem (fun i _ =>
      Submonoid.subset_closure (Set.mem_range_self i))
  · intro a ha
    apply units_on_closure (algebraMap R (Localization.Away (∏ i, r i))) r _ ⟨a, ha⟩
    intro i
    exact IsLocalization.Away.isUnit_of_dvd (∏ j, r j)
      (Finset.dvd_prod_of_mem r (Finset.mem_univ i))

def localizationProductEquiv (r : ι → R) :
    ValueLocalization r ≃ₐ[R] Localization.Away (∏ i, r i) := by
  letI := awayProduct_isLocalization r
  exact IsLocalization.algEquiv (valueMonoid r) _ _

theorem valueLocalization_smooth (r : ι → R) : Algebra.Smooth R (ValueLocalization r) := by
  letI : Algebra.Smooth R (Localization.Away (∏ i, r i)) :=
    Algebra.Smooth.of_isLocalization_Away (∏ i, r i)
  exact Algebra.Smooth.of_equiv (localizationProductEquiv r).symm

end FiniteLocalization

section ExchangeCharts

variable (R ι)

abbrev CoordinateRing := MvPolynomial (ι ⊕ ι) R

def xyMinusOne (i : ι) : CoordinateRing R ι :=
  X (Sum.inl i) * X (Sum.inr i) - 1

/-- R[x_i,y_i,t_i^{±1}]/(x_i*y_i-1-t_i), with all equations imposed. -/
abbrev SplitChart := ExchangeQuotient (xyMinusOne R ι)

/-- R[x_i,y_i,(x_i*y_i-1)^{-1}:i], constructed by localization. -/
abbrev OpenChart := ValueLocalization (xyMinusOne R ι)

def splitChartEquiv : SplitChart R ι ≃ₐ[CoordinateRing R ι] OpenChart R ι :=
  quotientEquiv (xyMinusOne R ι)

theorem splitChart_relation (i : ι) :
    relation (xyMinusOne R ι) i =
      algebraMap (CoordinateRing R ι) (Laurent (CoordinateRing R ι) ι) (X (Sum.inl i)) *
      algebraMap (CoordinateRing R ι) (Laurent (CoordinateRing R ι) ι) (X (Sum.inr i)) -
      1 - laurentVariable (CoordinateRing R ι) ι i := by
  simp only [relation, xyMinusOne, map_sub, map_mul, map_one]

end ExchangeCharts

section FiniteChartSmoothness

universe u
variable (k α : Type u) [CommRing k] [Fintype α]

theorem coordinateRing_smooth : Algebra.Smooth k (CoordinateRing k α) where

theorem openChart_smooth : Algebra.Smooth k (OpenChart k α) := by
  letI : Algebra.Smooth k (CoordinateRing k α) := coordinateRing_smooth k α
  letI : Algebra.Smooth (CoordinateRing k α) (OpenChart k α) :=
    valueLocalization_smooth (xyMinusOne k α)
  exact Algebra.Smooth.comp k (CoordinateRing k α) (OpenChart k α)

/-- Smoothness of the actual exchange quotient follows by the constructed
chart isomorphism; it is not an input hypothesis. -/
theorem splitChart_smooth : Algebra.Smooth k (SplitChart k α) := by
  letI : Algebra.Smooth k (OpenChart k α) := openChart_smooth k α
  exact Algebra.Smooth.of_equiv ((splitChartEquiv k α).symm.restrictScalars k)

/-- Separate the x parameters from the polynomial y coordinates. -/
def parameterPresentation : CoordinateRing k α ≃ₐ[k] MvPolynomial α (MvPolynomial α k) :=
  (MvPolynomial.renameEquiv k (Equiv.sumComm α α)).trans (MvPolynomial.sumAlgEquiv k α α)

instance parameterAlgebra : Algebra (MvPolynomial α k) (CoordinateRing k α) :=
  ((parameterPresentation k α).symm.toRingHom.comp C).toAlgebra

def parameterEquiv : MvPolynomial α (MvPolynomial α k) ≃ₐ[MvPolynomial α k] CoordinateRing k α :=
  AlgEquiv.ofRingEquiv (f := (parameterPresentation k α).symm.toRingEquiv) (fun _ => rfl)

omit [Fintype α] in
theorem parameter_presentation_x (i : α) :
    parameterPresentation k α (X (Sum.inl i)) = C (X i) := by
  change MvPolynomial.sumToIter k α α (MvPolynomial.rename (Equiv.sumComm α α) (X (Sum.inl i))) = _
  rw [rename_X]
  exact sumToIter_Xr k α α i

omit [Fintype α] in
theorem parameter_algebraMap_X (i : α) :
    algebraMap (MvPolynomial α k) (CoordinateRing k α) (X i) = X (Sum.inl i) := by
  apply (parameterPresentation k α).injective
  change parameterPresentation k α ((parameterPresentation k α).symm (C (X i))) = _
  rw [AlgEquiv.apply_symm_apply, parameter_presentation_x]

theorem coordinateRing_parameter_smooth :
    Algebra.Smooth (MvPolynomial α k) (CoordinateRing k α) := by
  letI : Algebra.Smooth (MvPolynomial α k) (MvPolynomial α (MvPolynomial α k)) := {}
  exact Algebra.Smooth.of_equiv (parameterEquiv k α)

theorem openChart_parameter_smooth : Algebra.Smooth (MvPolynomial α k) (OpenChart k α) := by
  letI : Algebra.Smooth (MvPolynomial α k) (CoordinateRing k α) :=
    coordinateRing_parameter_smooth k α
  letI : Algebra.Smooth (CoordinateRing k α) (OpenChart k α) :=
    valueLocalization_smooth (xyMinusOne k α)
  exact Algebra.Smooth.comp (MvPolynomial α k) (CoordinateRing k α) (OpenChart k α)

/-- The simultaneous x-coordinate map is smooth on the actual exchange chart. -/
theorem splitChart_parameter_smooth : Algebra.Smooth (MvPolynomial α k) (SplitChart k α) := by
  letI : Algebra.Smooth (MvPolynomial α k) (OpenChart k α) := openChart_parameter_smooth k α
  exact Algebra.Smooth.of_equiv ((splitChartEquiv k α).symm.restrictScalars (MvPolynomial α k))

omit [Fintype α] in
theorem splitChart_parameter_image_X (i : α) :
    algebraMap (MvPolynomial α k) (SplitChart k α) (X i) =
      quotientCoefficient (xyMinusOne k α) (X (Sum.inl i)) := by
  rw [IsScalarTower.algebraMap_apply (MvPolynomial α k) (CoordinateRing k α) (SplitChart k α),
    parameter_algebraMap_X]
  rfl

end FiniteChartSmoothness

#print axioms units_on_closure
#print axioms variableMonoid
#print axioms Laurent
#print axioms laurentVariable
#print axioms laurentVariable_unit
#print axioms valueMonoid
#print axioms ValueLocalization
#print axioms relation
#print axioms relations
#print axioms ExchangeQuotient
#print axioms polynomialEvaluation
#print axioms polynomialEvaluation_units
#print axioms laurentEvaluation
#print axioms evaluation_coefficient
#print axioms evaluation_variable
#print axioms evaluation_relation
#print axioms descend
#print axioms quotientCoefficient
#print axioms quotient_generator_eq
#print axioms quotient_variable
#print axioms quotient_coefficient_units
#print axioms includeBase
#print axioms descend_includeBase
#print axioms includeBase_descend
#print axioms quotientRingEquiv
#print axioms quotientEquiv
#print axioms awayProduct_isLocalization
#print axioms localizationProductEquiv
#print axioms valueLocalization_smooth
#print axioms CoordinateRing
#print axioms xyMinusOne
#print axioms SplitChart
#print axioms OpenChart
#print axioms splitChartEquiv
#print axioms splitChart_relation
#print axioms coordinateRing_smooth
#print axioms openChart_smooth
#print axioms splitChart_smooth
#print axioms parameterPresentation
#print axioms parameterAlgebra
#print axioms parameterEquiv
#print axioms parameter_presentation_x
#print axioms parameter_algebraMap_X
#print axioms coordinateRing_parameter_smooth
#print axioms openChart_parameter_smooth
#print axioms splitChart_parameter_smooth
#print axioms splitChart_parameter_image_X

end Verification.SplitExchangeChart
