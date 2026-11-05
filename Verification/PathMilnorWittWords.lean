/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittTriple

/-!
# Path Milnor Witt Words

Ordered words of actual unit symbols, with arbitrary unchanged prefixes and
suffixes. Their Laurent contraction is obtained internally from the standard
constant/parameter rules and the ordinary Milnor-Witt symbol identities.
-/
namespace Verification.PathMilnorWittWords
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
open Verification.PathMilnorWittTriple
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]

def monomial (D : Symbols S B) : List Sˣ → B
  | [] => 1
  | a::w => D.symbol a * monomial D w

def twisted (D : Symbols S B) : List Sˣ → B
  | [] => 1
  | a::w => (-D.g * D.symbol a) * twisted D w

theorem twisted_eq (D : Symbols S B) (xs : List Sˣ) :
    twisted D xs = (-D.g)^xs.length * monomial D xs := by
  induction xs with
  | nil => simp [twisted,monomial]
  | cons a xs ih =>
    rw [twisted,ih,monomial,List.length_cons,pow_succ']
    have hc := ((D.central_g (D.symbol a)).neg_left.pow_left xs.length).eq
    calc
      (-D.g * D.symbol a) * ((-D.g)^xs.length * monomial D xs) =
          -D.g * ((D.symbol a * (-D.g)^xs.length) * monomial D xs) := by simp only [mul_assoc]
      _ = -D.g * (((-D.g)^xs.length * D.symbol a) * monomial D xs) := by rw [hc]
      _ = _ := by simp only [mul_assoc]

variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F) (u : Tˣ)

include h in
theorem pullback (xs : List Sˣ) :
    monomial D₁ (xs.map (Units.map f.toMonoidHom)) = F (monomial D₀ xs) := by
  induction xs with
  | nil => simp [monomial]
  | cons a xs ih => simp only [List.map_cons,monomial,ih,map_mul,h.symbol]

include h in
theorem move_parameter (xs : List Sˣ) :
    monomial D₁ (xs.map (Units.map f.toMonoidHom)) * D₁.symbol u =
      D₁.symbol u * F (twisted D₀ xs) := by
  induction xs with
  | nil => simp [monomial,twisted]
  | cons a xs ih =>
    simp only [List.map_cons,monomial,twisted,map_mul]
    rw [mul_assoc,ih,← mul_assoc,swap_parameter D₀ D₁ f F h u a]
    simp only [map_mul,mul_assoc]

include h in
theorem normal_form (xs ys : List Sˣ) (a : Sˣ) (w : Verification.PathRhoFaces.Triple) :
    monomial D₁ (xs.map (Units.map f.toMonoidHom)) *
        word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol u)
          (D₁.symbol (Units.map f.toMonoidHom a)) w *
        monomial D₁ (ys.map (Units.map f.toMonoidHom)) =
      F (monomial D₀ xs * word (D₀.symbol a) 0 (D₀.symbol a) w * monomial D₀ ys) +
      D₁.symbol u * F (twisted D₀ xs * residue D₀ a w * monomial D₀ ys) := by
  rw [PathMilnorWittTriple.normal_form D₀ D₁ f F h u a w,mul_add,add_mul]
  rw [pullback D₀ D₁ f F h ys]
  rw [← mul_assoc (monomial D₁ _) (D₁.symbol u),move_parameter D₀ D₁ f F h u xs]
  rw [pullback D₀ D₁ f F h xs]
  simp only [map_mul,mul_assoc]

include h in
theorem contraction (r : A →+ B) (r_constant : ∀ b,r (F b)=0)
    (r_parameter : ∀ b,r (D₁.symbol u * F b)=b)
    (xs ys : List Sˣ) (a : Sˣ) (w : Verification.PathRhoFaces.Triple) :
    r (monomial D₁ (xs.map (Units.map f.toMonoidHom)) *
        word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol u)
          (D₁.symbol (Units.map f.toMonoidHom a)) w *
        monomial D₁ (ys.map (Units.map f.toMonoidHom))) =
      (-D₀.g)^xs.length * monomial D₀ xs * residue D₀ a w * monomial D₀ ys := by
  rw [normal_form D₀ D₁ f F h u xs ys a w,map_add,r_constant,r_parameter,zero_add,
    twisted_eq]

#print axioms monomial
#print axioms twisted
#print axioms twisted_eq
#print axioms pullback
#print axioms move_parameter
#print axioms normal_form
#print axioms contraction
end Verification.PathMilnorWittWords
