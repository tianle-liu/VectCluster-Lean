/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.Nodup

/-!
# Polynomial Regular Sequence

Distinct polynomial variables form a weakly regular sequence over
every commutative ring. The proof uses the actual monomial ideal and
coefficient support criterion. Flat base change preserves this property;
properness of the resulting ideal supplies regularity.
-/
noncomputable section
namespace Verification.PolynomialRegularSequence
open MvPolynomial RingTheory.Sequence
variable (R κ : Type*) [CommRing R]

theorem variable_regular_mod (s : Set κ) (k : κ) (hk : k ∉ s) :
    IsSMulRegular (MvPolynomial κ R ⧸ Ideal.span (X '' s : Set (MvPolynomial κ R)))
      (X k : MvPolynomial κ R) := by
  classical
  apply (isSMulRegular_on_quot_iff_smul_mem_implies_mem _ _).mpr
  intro p hp
  change X k * p ∈ Ideal.span (X '' s : Set (MvPolynomial κ R)) at hp
  apply mem_ideal_span_X_image.mpr
  intro m hm
  have hm' : Finsupp.single k 1 + m ∈ (X k * p).support := by
    apply mem_support_iff.mpr
    rw [coeff_X_mul]
    exact mem_support_iff.mp hm
  obtain ⟨i, hi, hmi⟩ := mem_ideal_span_X_image.mp hp _ hm'
  have hki : k ≠ i := fun h => hk (h.symm ▸ hi)
  refine ⟨i,hi,?_⟩
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hki, zero_add] using hmi

theorem ofList_variables (l : List κ) :
    Ideal.ofList (l.map (X : κ → MvPolynomial κ R)) = Ideal.span (X '' {i | i ∈ l}) := by
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]

theorem variables_weaklyRegular (l : List κ) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial κ R) (l.map (X : κ → MvPolynomial κ R)) := by
  constructor
  intro i hi
  have hil : i < l.length := by simpa only [List.length_map] using hi
  have hnot : l[i] ∉ l.take i := by
    intro hm
    obtain ⟨j,hj,hji⟩ := List.mem_take_iff_getElem.mp hm
    have heq : j = i := hl.getElem_inj_iff.mp hji
    omega
  simp only [List.getElem_map]
  apply (isSMulRegular_on_quot_iff_smul_mem_implies_mem _ _).mpr
  intro p hp
  have hJ : (Ideal.ofList ((l.map (X : κ → MvPolynomial κ R)).take i) * ⊤) =
      Ideal.span (X '' {k | k ∈ l.take i}) := by
    rw [Ideal.mul_top, ← List.map_take, ofList_variables]
  change X l[i] * p ∈ Ideal.ofList ((l.map (X : κ → MvPolynomial κ R)).take i) * ⊤ at hp
  change p ∈ Ideal.ofList ((l.map (X : κ → MvPolynomial κ R)).take i) * ⊤
  rw [hJ] at hp ⊢
  exact (isSMulRegular_on_quot_iff_smul_mem_implies_mem _ _).mp
    (variable_regular_mod R κ {k | k ∈ l.take i} l[i] hnot) p hp


variable (A : Type*) [CommRing A] [Algebra (MvPolynomial κ R) A]

theorem flat_variables_weaklyRegular [Module.Flat (MvPolynomial κ R) A]
    (l : List κ) (hl : l.Nodup) : IsWeaklyRegular A
      (l.map (fun k => algebraMap (MvPolynomial κ R) A (X k))) := by
  have h := (variables_weaklyRegular R κ l hl).isWeaklyRegular_rTensor (M₂ := A)
  have hA := ((TensorProduct.lid (MvPolynomial κ R) A).isWeaklyRegular_congr
    (l.map (X : κ → MvPolynomial κ R))).mp h
  have hm := (isWeaklyRegular_map_algebraMap_iff A A (l.map (X : κ → MvPolynomial κ R))).mpr hA
  simpa only [List.map_map, Function.comp_def] using hm

theorem flat_variables_regular [Module.Flat (MvPolynomial κ R) A]
    (l : List κ) (hl : l.Nodup)
    (hproper : Ideal.ofList (l.map (fun k => algebraMap (MvPolynomial κ R) A (X k))) ≠ ⊤) :
    IsRegular A (l.map (fun k => algebraMap (MvPolynomial κ R) A (X k))) where
  toIsWeaklyRegular := flat_variables_weaklyRegular R κ A l hl
  top_ne_smul := by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hproper.symm

#print axioms variable_regular_mod
#print axioms ofList_variables
#print axioms variables_weaklyRegular
#print axioms flat_variables_weaklyRegular
#print axioms flat_variables_regular
end Verification.PolynomialRegularSequence
