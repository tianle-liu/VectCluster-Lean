/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordEndpointEvaluation
import Verification.PathNormalizedBasis

/-!
# Path Normalized Word Evaluation

Finite normalized word evaluation and its coefficient coordinates in
an ordinary, possibly noncommutative, Milnor-Witt section ring.
-/
noncomputable section
namespace Verification.PathNormalizedWordEvaluation
open Classical Verification.MilnorWittSymbolRelations
open Verification.PathMilnorWittWordFace Verification.PathMilnorWittCoefficients
open Verification.PathNormalizedBasis
local notation "C" => Verification.PathCoefficientRing.Coeff

theorem coefficient_hom_ext {A : Type*} [Ring A] (f g : C →+* A)
    (hg : f PathCoefficientRing.g=g PathCoefficientRing.g)
    (hr : f PathCoefficientRing.rho=g PathCoefficientRing.rho) : f=g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z;simp
  · intro b;cases b
    · exact hg
    · exact hr

theorem realize_naturality {A B : Type*} [Ring A] [Ring B]
    (D₀ : Coefficients A) (D₁ : Coefficients B) (F : A →+* B)
    (hg : F D₀.g=D₁.g) (hr : F D₀.rho=D₁.rho) (c : C) :
    F (realize D₀ c)=realize D₁ c := by
  have he : F.comp (realize D₀)=realize D₁ := by
    apply coefficient_hom_ext
    · simp only [RingHom.comp_apply,realize_g,hg]
    · simp only [RingHom.comp_apply,realize_rho,hr]
  exact RingHom.congr_fun he c

theorem normal_expansion (Q : List Bool → Prop) (n : ℕ) (f : List Bool →₀ C)
    (hf : f∈normalLayer (R:=C) Q n) :
    f=∑ w:NormalWord Q n,Finsupp.single w.val (f w.val) := by
  have hp : ∀ w∈f.support,w.length=n ∧ Q w := (Finsupp.mem_supported C f).mp hf
  have hh := Finsupp.sum_subtypeDomain_index (v:=f) (p:=fun w => w.length=n ∧ Q w)
    (h:=fun w c => Finsupp.single w c) hp
  rw [Finsupp.sum_single,Finsupp.sum_fintype _ _ (by intro i;simp)] at hh
  exact hh.symm

theorem evaluate_normal {S B : Type*} [CommRing S] [Ring B] (D : Symbols S B)
    (xs : List Sˣ) (Q : List Bool → Prop) (n : ℕ) (f : List Bool →₀ C)
    (hf : f∈normalLayer (R:=C) Q n) :
    evaluate D xs f=∑ w:NormalWord Q n,realize D.toCoefficients (f w.val)*wordValue D xs w.val := by
  conv_lhs => rw [normal_expansion Q n f hf]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun w _ => evaluate_single D xs w.val (f w.val))

theorem weighted_normal {S A B : Type*} [CommRing S] [Ring A] [Ring B]
    (D₀ : Coefficients A) (D₁ : Symbols S B) (F : A →+* B)
    (hg : F D₀.g=D₁.g) (hr : F D₀.rho=D₁.rho)
    (xs : List Sˣ) (Q : List Bool → Prop) (n : ℕ) (f : List Bool →₀ C)
    (hf : f∈normalLayer (R:=C) Q n) (w : ℕ) (c : A) :
    D₁.g^w * evaluate D₁ xs f * F c=
      ∑ i:NormalWord Q n,wordValue D₁ xs i.val * F (D₀.g^w * realize D₀ (f i.val) * c) := by
  rw [evaluate_normal D₁ xs Q n f hf,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,map_mul,map_pow,hg,realize_naturality D₀ D₁.toCoefficients F hg hr]
  have hc := central D₁.toCoefficients (PathCoefficientRing.g^w*f i.val) (wordValue D₁ xs i.val)
  simp only [map_mul,map_pow,realize_g] at hc
  rw [←mul_assoc,←mul_assoc,hc,mul_assoc]

#print axioms coefficient_hom_ext
#print axioms realize_naturality
#print axioms normal_expansion
#print axioms evaluate_normal
#print axioms weighted_normal
end Verification.PathNormalizedWordEvaluation
