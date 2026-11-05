/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittSignedWordFace

/-!
# Path Milnor Witt List Face

Whole ordered unit lists realize the literal formal face column. Length
conditions are the word type conditions; no matrix identity is assumed.
-/
noncomputable section
namespace Verification.PathMilnorWittListFace
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
open Verification.PathMilnorWittTriple Verification.PathMilnorWittWords
open Verification.PathMilnorWittWordFace
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]

theorem value_append (D : Symbols S B) (xs ys : List Sˣ) (bs cs : List Bool)
    (h : xs.length=bs.length) :
    wordValue D (xs++ys) (bs++cs)=wordValue D xs bs * wordValue D ys cs := by
  induction xs generalizing bs with
  | nil => have hh : bs=[]:=List.length_eq_zero_iff.mp h.symm;subst bs;simp only [List.nil_append,wordValue,one_mul]
  | cons x xs ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hh : xs.length=bs.length:=by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h
      simp only [List.cons_append,wordValue,ih bs hh,mul_assoc]

theorem value_triple (D : Symbols S B) (xs ys : List Sˣ) (bs cs : List Bool)
    (h : xs.length=bs.length) (a b c : Sˣ) (l m t : Bool) :
    wordValue D (xs++a::b::c::ys) (bs++l::m::t::cs)=
      wordValue D xs bs * word (D.symbol a) (D.symbol b) (D.symbol c) (l,m,t) * wordValue D ys cs := by
  rw [value_append D xs (a::b::c::ys) bs (l::m::t::cs) h]
  simp only [wordValue,word,mul_assoc]

theorem value_mapped_pairs (D : Symbols T A) (f : Sˣ → Tˣ) (xs : List (Sˣ × Bool)) :
    wordValue D ((xs.map Prod.fst).map f) (xs.map Prod.snd)=
      monomial D ((selected xs).map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨x,b⟩
    cases b <;> simp only [List.map_cons,wordValue,selected,bit,Bool.false_eq_true,↓reduceIte,
      monomial,one_mul,ih]

variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F) (u : Tˣ)

include h in
theorem full_column (r : A →+ B) (r_constant : ∀ b,r (F b)=0)
    (r_parameter : ∀ b,r (D₁.symbol u * F b)=b) (w : ℕ)
    (xs ys : List Sˣ) (bs cs : List Bool) (hx : xs.length=bs.length) (hy : ys.length=cs.length)
    (a : Sˣ) (l m t : Bool) :
    r (wordValue D₁ (xs.map (Units.map f.toMonoidHom) ++
      Units.map f.toMonoidHom a :: ((-1:Tˣ)^w*u) :: Units.map f.toMonoidHom a ::
        ys.map (Units.map f.toMonoidHom)) (bs++l::m::t::cs))=
      D₀.g^w * evaluate D₀ (xs++a::ys)
        (Verification.PathRhoWords.faceColumn (-Verification.PathCoefficientRing.g)
          Verification.PathCoefficientRing.rho bs.length (bs++l::m::t::cs)) := by
  have hh := PathMilnorWittSignedWordFace.signed_column D₀ D₁ f F h u r r_constant r_parameter w
    (xs.zip bs) (ys.zip cs) a l m t
  rw [← value_mapped_pairs,← value_mapped_pairs] at hh
  rw [List.map_fst_zip (by omega : xs.length≤bs.length),
    List.map_fst_zip (by omega : ys.length≤cs.length),
    List.map_snd_zip (by omega : bs.length≤xs.length),
    List.map_snd_zip (by omega : cs.length≤ys.length)] at hh
  rw [value_triple D₁ _ _ bs cs (by simpa only [List.length_map] using hx)]
  exact hh

#print axioms value_append
#print axioms value_triple
#print axioms value_mapped_pairs
#print axioms full_column
end Verification.PathMilnorWittListFace
