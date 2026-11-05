/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.Tactic.NormNum

/-!
# Odd Middle Homology

The original middle-degree group argument: a finitely generated
abelian group divisible by two is finite of odd order. Divisibility is
derived whenever a surjective comparison map has image in twice the target.
-/
namespace Verification.OddMiddleHomology
open scoped Pointwise
variable (G : Type*) [AddCommGroup G] [Module.Finite ℤ G]

theorem odd_annihilator (h : Function.Surjective (fun g : G => (2:ℤ) • g)) :
    ∃ r : ℤ, r ≠ 0 ∧ (2:ℤ) ∣ r-1 ∧ ∀ g : G, r • g=0 := by
  have htop : (⊤ : Submodule ℤ G) ≤ Ideal.span {(2:ℤ)} • (⊤ : Submodule ℤ G) := by
    rw [Submodule.ideal_span_singleton_smul]
    intro g _
    obtain ⟨a,rfl⟩ := h g
    exact Submodule.smul_mem_pointwise_smul a (2:ℤ) ⊤ trivial
  obtain ⟨r,hr,hm⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(2:ℤ)}) (⊤ : Submodule ℤ G) Module.Finite.fg_top htop
  have hd : (2:ℤ) ∣ r-1 := Ideal.mem_span_singleton.mp hr
  have hn : r ≠ 0 := by
    intro hz
    rw [hz] at hd
    norm_num at hd
  exact ⟨r,hn,hd,fun g => hm g trivial⟩

theorem finite_of_double_surjective (h : Function.Surjective (fun g : G => (2:ℤ) • g)) :
    Finite G := by
  obtain ⟨r,hr,_,ha⟩ := odd_annihilator G h
  apply Module.finite_of_fg_torsion G
  intro g
  exact ⟨⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩,ha g⟩

theorem odd_card (h : Function.Surjective (fun g : G => (2:ℤ) • g)) : Odd (Nat.card G) := by
  classical
  letI := finite_of_double_surjective G h
  letI := Fintype.ofFinite G
  have hi : Function.Injective (fun g : G => (2:ℤ) • g) := (Finite.injective_iff_surjective).mpr h
  by_contra hn
  have hd : 2 ∣ Fintype.card G := by
    rwa [Nat.card_eq_fintype_card,Nat.not_odd_iff_even,even_iff_two_dvd] at hn
  obtain ⟨x,hx⟩ := exists_prime_addOrderOf_dvd_card 2 hd
  have hz : (2:ℤ) • x=0 := by
    have hh := addOrderOf_nsmul_eq_zero x
    rw [hx] at hh
    simpa only [two_smul] using hh
  have hx0 : x=0 := hi (by simpa using hz)
  subst x
  simp at hx

variable {A : Type*} [AddCommGroup A]

omit [Module.Finite ℤ G] in
theorem double_surjective_of_comparison (f : A →+ G) (hf : Function.Surjective f)
    (heven : ∀ a : A, ∃ g : G, f a=(2:ℤ) • g) :
    Function.Surjective (fun g : G => (2:ℤ) • g) := by
  intro g
  obtain ⟨a,rfl⟩ := hf g
  obtain ⟨b,hb⟩ := heven a
  exact ⟨b,hb.symm⟩

theorem finite_odd_of_comparison (f : A →+ G) (hf : Function.Surjective f)
    (heven : ∀ a : A, ∃ g : G, f a=(2:ℤ) • g) : Finite G ∧ Odd (Nat.card G) :=
  ⟨finite_of_double_surjective G (double_surjective_of_comparison G f hf heven),
    odd_card G (double_surjective_of_comparison G f hf heven)⟩

#print axioms odd_annihilator
#print axioms finite_of_double_surjective
#print axioms odd_card
#print axioms double_surjective_of_comparison
#print axioms finite_odd_of_comparison
end Verification.OddMiddleHomology
