/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerDifferential
import Verification.OriginalWittStratumFree
import Verification.FiniteHomologyFacts
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Original Witt Integer Complex

The manuscript's actual finite integral Witt complex, with literal
signed group-ring stratum terms and ordered coordinate residue maps.
-/
noncomputable section
open scoped Classical
namespace Verification.OriginalWittIntegerComplex
open Verification.OriginalWittIntegerDifferential Verification.OriginalWittQuotient
open Verification.AnticliqueSubcolumns
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

def degree (p : ℕ) : Submodule ℤ (Cochains B F) where
  carrier := {f | ∀ I : Index F, I.val.card ≠ p → f I = 0}
  zero_mem' := by intro I _; rfl
  add_mem' hf hg := by intro I hI; simp [hf I hI,hg I hI]
  smul_mem' c f hf := by intro I hI; simp [hf I hI]

abbrev DegreeIndex (F : Finset V → Prop) (p : ℕ) := {I : Index F // I.val.card=p}

def degreeEquiv (p : ℕ) :
    degree B F p ≃ₗ[ℤ] ((I : DegreeIndex F p) → Stratum B I.val.val) where
  toFun f I := f.val I.val
  invFun g := ⟨fun I => if h : I.val.card=p then g ⟨I,h⟩ else 0,by
    intro I hI
    simp only [dif_neg hI]⟩
  left_inv f := by
    apply Subtype.ext
    funext I
    by_cases h : I.val.card=p
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      exact (f.property I h).symm
  right_inv f := by funext I; simp only [dif_pos I.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def differential (p : ℕ) : degree B F p →ₗ[ℤ] degree B F (p+1) :=
  (((OriginalWittIntegerDifferential.differential B F down indep).toIntLinearMap).comp
    (degree B F p).subtype).codRestrict (degree B F (p+1))
      (fun f => degree_preserved B F down indep p f.val f.property)

omit [Fintype C] in
theorem differential_squared (p : ℕ) (f : degree B F p) :
    differential B F down indep (p+1) (differential B F down indep p f) = 0 := by
  apply Subtype.ext
  exact OriginalWittIntegerDifferential.differential_squared B F down indep f.val

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of ℤ (degree B F p))
    (fun p => ModuleCat.ofHom (differential B F down indep p))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact differential_squared B F down indep p f)

variable (hz : ∀ I, F I → ∀ i j : I, B (Sum.inl j.val) i.val = 0)
variable (hAS : ∀ I, F I → AS B I)

include hz hAS in
omit [LinearOrder V] in
theorem degree_free (p : ℕ) : Module.Free ℤ (degree B F p) := by
  letI : ∀ I : DegreeIndex F p, Module.Free ℤ (Stratum B I.val.val) :=
    fun I => OriginalWittStratumFree.free B I.val.val (hz _ I.val.property) (hAS _ I.val.property)
  exact Module.Free.of_equiv (degreeEquiv B F p).symm

include hz hAS in
omit [LinearOrder V] in
theorem degree_finite (p : ℕ) : Module.Finite ℤ (degree B F p) := by
  letI : ∀ I : DegreeIndex F p, Module.Finite ℤ (Stratum B I.val.val) :=
    fun I => OriginalWittStratumFree.finite B I.val.val (hz _ I.val.property) (hAS _ I.val.property)
  exact Module.Finite.equiv (degreeEquiv B F p).symm

omit [Fintype C] [LinearOrder V] in
theorem degree_above (p : ℕ) (hp : Fintype.card V < p) : Subsingleton (degree B F p) := by
  haveI : IsEmpty (DegreeIndex F p) := ⟨fun I => by
    have h := Finset.card_le_univ I.val.val
    rw [I.property] at h
    omega⟩
  exact (degreeEquiv B F p).injective.subsingleton

#print axioms degree
#print axioms DegreeIndex
#print axioms degreeEquiv
#print axioms differential
#print axioms differential_squared
#print axioms complex
#print axioms degree_free
#print axioms degree_finite
#print axioms degree_above
end Verification.OriginalWittIntegerComplex
