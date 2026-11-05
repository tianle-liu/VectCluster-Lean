/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittWords
import Verification.PathMilnorWittCoefficients
import Verification.PathWordColumnFormula

/-!
# Path Milnor Witt Word Face

Evaluation of the literal full-rho formal word column in actual
Milnor-Witt symbols. Both unchanged ordered prefixes and suffixes are
arbitrary; the repeated neighbor is an actual single coefficient unit.
-/
noncomputable section
namespace Verification.PathMilnorWittWordFace
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
open Verification.PathMilnorWittTriple Verification.PathMilnorWittWords
open Verification.PathRhoFaces Verification.PathWordColumnFormula
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]

def selected : List (Sˣ × Bool) → List Sˣ
  | [] => []
  | (a,b)::xs => if b then a::selected xs else selected xs

def wordValue (D : Symbols S B) : List Sˣ → List Bool → B
  | a::xs,b::bs => bit (D.symbol a) b * wordValue D xs bs
  | _,_ => 1

theorem paired_value (D : Symbols S B) (xs : List (Sˣ × Bool)) :
    wordValue D (xs.map Prod.fst) (xs.map Prod.snd) = monomial D (selected xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨a,b⟩; cases b <;> simp [wordValue,selected,bit,monomial,ih]

theorem block_value (D : Symbols S B) (xs ys : List (Sˣ × Bool)) (a : Sˣ) (b : Bool) :
    wordValue D (xs.map Prod.fst ++ a::ys.map Prod.fst)
      (xs.map Prod.snd ++ b::ys.map Prod.snd) =
    monomial D (selected xs) * bit (D.symbol a) b * monomial D (selected ys) := by
  induction xs with
  | nil => simp only [List.map_nil,List.nil_append,wordValue,selected,monomial,one_mul,paired_value]
  | cons x xs ih =>
    rcases x with ⟨x,c⟩
    cases c <;> simp only [List.map_cons,List.cons_append,wordValue,selected,bit,
      Bool.false_eq_true,↓reduceIte,monomial,one_mul,ih,mul_assoc]

def evaluate (D : Symbols S B) (xs : List Sˣ) : (List Bool →₀ Verification.PathCoefficientRing.Coeff) →+ B :=
  Finsupp.liftAddHom (fun w => (AddMonoidHom.mulRight (wordValue D xs w)).comp
    (Verification.PathMilnorWittCoefficients.realize D.toCoefficients).toAddMonoidHom)

theorem evaluate_single (D : Symbols S B) (xs : List Sˣ) (w : List Bool)
    (c : Verification.PathCoefficientRing.Coeff) :
    evaluate D xs (Finsupp.single w c) =
      Verification.PathMilnorWittCoefficients.realize D.toCoefficients c * wordValue D xs w := by
  rw [evaluate,Finsupp.liftAddHom_apply_single]
  rfl

theorem prefix_coefficient (D : Symbols S B) (xs : List (Sˣ × Bool)) :
    Verification.PathMilnorWittCoefficients.realize D.toCoefficients
      (phaseProduct (-Verification.PathCoefficientRing.g) (xs.map Prod.snd)) =
    (-D.g)^(selected xs).length := by
  induction xs with
  | nil => simp [phaseProduct,selected]
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    cases b <;> simp [phaseProduct,phase,selected,ih,
      Verification.PathMilnorWittCoefficients.realize_g,pow_succ']

theorem local_coefficient (D : Symbols S B) (a : Sˣ) (l r : Bool) :
    residue D a (l,true,r) =
      Verification.PathMilnorWittCoefficients.realize D.toCoefficients
        (phase (-Verification.PathCoefficientRing.g) l *
          repeatFactor Verification.PathCoefficientRing.rho l r) * bit (D.symbol a) (l || r) := by
  cases l <;> cases r <;> simp [residue,phase,repeatFactor,
    Verification.PathMilnorWittCoefficients.realize_g,Verification.PathMilnorWittCoefficients.realize_rho]

variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F) (u : Tˣ)

include h in
theorem column_contraction (r : A →+ B) (r_constant : ∀ b,r (F b)=0)
    (r_parameter : ∀ b,r (D₁.symbol u * F b)=b)
    (xs ys : List (Sˣ × Bool)) (a : Sˣ) (l m t : Bool) :
    r (monomial D₁ ((selected xs).map (Units.map f.toMonoidHom)) *
      word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol u)
        (D₁.symbol (Units.map f.toMonoidHom a)) (l,m,t) *
      monomial D₁ ((selected ys).map (Units.map f.toMonoidHom))) =
    evaluate D₀ (xs.map Prod.fst ++ a::ys.map Prod.fst)
      (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
        Verification.PathCoefficientRing.rho (xs.map Prod.snd).length
        (xs.map Prod.snd ++ l::m::t::ys.map Prod.snd)) := by
  rw [PathMilnorWittWords.contraction D₀ D₁ f F h u r r_constant r_parameter,
    column]
  cases m with
  | false => simp only [residue,Bool.false_eq_true,↓reduceIte,mul_zero,zero_mul,map_zero]
  | true =>
    simp only [↓reduceIte,Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [evaluate_single,block_value,map_mul,prefix_coefficient,local_coefficient]
    have hc := Verification.PathMilnorWittCoefficients.central D₀.toCoefficients
      (phase (-Verification.PathCoefficientRing.g) l * repeatFactor Verification.PathCoefficientRing.rho l t)
      (monomial D₀ (selected xs))
    calc
      _ = (-D₀.g)^(selected xs).length *
        (monomial D₀ (selected xs) *
          Verification.PathMilnorWittCoefficients.realize D₀.toCoefficients
            (phase (-Verification.PathCoefficientRing.g) l * repeatFactor Verification.PathCoefficientRing.rho l t)) *
        (bit (D₀.symbol a) (l || t) * monomial D₀ (selected ys)) := by simp only [mul_assoc]
      _ = _ := by rw [← hc]; simp only [mul_assoc]

#print axioms selected
#print axioms wordValue
#print axioms paired_value
#print axioms block_value
#print axioms evaluate
#print axioms evaluate_single
#print axioms prefix_coefficient
#print axioms local_coefficient
#print axioms column_contraction
end Verification.PathMilnorWittWordFace
