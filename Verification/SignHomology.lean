/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignComplex
import Verification.FiniteHomologyFacts
import Verification.OddMiddleHomology

/-!
# Sign Homology

Actual finite integral sign cochains and their categorical homology.
The geometric comparison is not a hypothesis used to construct this complex.
-/
noncomputable section
namespace Verification.SignHomology
open CategoryTheory CategoryTheory.Limits Verification.SignComplex
variable {ι : Type} [Fintype ι] [LinearOrder ι]
variable (Valid : State ι → Prop)

abbrev term (p : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (degreeCochains (R := ℤ) Valid p)

def coordinates (p : ℕ) : term Valid p ≃ₗ[ℤ]
    ({s : State ι // Valid s ∧ (holes s).card=p} → ℤ) :=
  (degreeCochainsEquiv Valid p).toIntLinearEquiv

instance term_finite (p : ℕ) : Module.Finite ℤ (term Valid p) :=
  Module.Finite.equiv (coordinates Valid p).symm

instance term_free (p : ℕ) : Module.Free ℤ (term Valid p) :=
  Module.Free.of_equiv (coordinates Valid p).symm

def differential (p : ℕ) : term Valid p ⟶ term Valid (p+1) :=
  ModuleCat.ofHom (degreeDifferential Valid p).toIntLinearMap

variable (closed : ∀ s, Valid s → ∀ i, s i=none → ∀ b, Valid (faceState s i b))

include closed in
theorem differential_squared (p : ℕ) :
    differential Valid p ≫ differential Valid (p+1)=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact degreeDifferential_squared Valid closed p x

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (term Valid) (differential Valid) (differential_squared Valid closed)

theorem homology_finite (p : ℕ) : Module.Finite ℤ ((complex Valid closed).homology p) := by
  let K := complex Valid closed
  let S := K.sc p
  letI : Module.Finite ℤ S.X₂ := term_finite Valid p
  convert Verification.FiniteHomologyFacts.short_homology_finite S using 1
  letI : Unique (Module ℤ ((complex Valid closed).homology p)) := AddCommGroup.uniqueIntModule
  exact Subsingleton.elim _ _

omit [LinearOrder ι] in

theorem term_zero (bound p : ℕ) (hb : ∀ s, Valid s → (holes s).card ≤ bound)
    (hp : bound < p) : Subsingleton (term Valid p) := by
  refine ⟨fun a b => ?_⟩
  exact (degreeCochains_vanish Valid bound p hb hp a).trans
    (degreeCochains_vanish Valid bound p hb hp b).symm

theorem homology_zero (bound p : ℕ) (hb : ∀ s, Valid s → (holes s).card ≤ bound)
    (hp : bound < p) : IsZero ((complex Valid closed).homology p) := by
  letI : Subsingleton ((complex Valid closed).sc p).X₂ := term_zero Valid bound p hb hp
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff,ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  have hx : x=0 := Subsingleton.elim _ _
  simp [hx]

theorem finite_odd_of_comparison (p : ℕ) {A : Type*} [AddCommGroup A]
    (f : A →+ (complex Valid closed).homology p) (hf : Function.Surjective f)
    (heven : ∀ a : A, ∃ g, f a=(2:ℤ) • g) :
    Finite ((complex Valid closed).homology p) ∧
      Odd (Nat.card ((complex Valid closed).homology p)) := by
  letI := homology_finite Valid closed p
  exact Verification.OddMiddleHomology.finite_odd_of_comparison _ f hf heven

#print axioms term
#print axioms coordinates
#print axioms term_finite
#print axioms term_free
#print axioms differential
#print axioms differential_squared
#print axioms complex
#print axioms homology_finite
#print axioms term_zero
#print axioms homology_zero
#print axioms finite_odd_of_comparison
end Verification.SignHomology
