/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittWordFace
import Verification.OrderedBinaryWords
import Verification.BinaryPathWordEquiv

/-!
# Path Ordered Word Values

False endpoint bits discard any endpoint unit, without assuming its
Milnor-Witt symbol vanishes. Products retain the actual increasing order.
-/
namespace Verification.PathOrderedWordValues
open Verification.PathMilnorWittWordFace Verification.PathMilnorWittTriple
open Verification.BinaryWordCoordinates Verification.BinaryPathWordEquiv
variable {S A : Type*} [CommRing S] [Ring A]

theorem false_tail (D : Verification.MilnorWittSymbolRelations.Symbols S A)
    (xs : List Sˣ) : wordValue D xs [false]=1 := by
  cases xs <;> simp [wordValue,bit]

theorem right_word (D : Verification.MilnorWittSymbolRelations.Symbols S A)
    (n : ℕ) (xs : List Sˣ) (hn : n≤xs.length) (i : Index n) :
    wordValue D xs (toList n i++[false])=
      Verification.OrderedBinaryWords.word n
        (fun k => D.symbol (xs[k.val]'(lt_of_lt_of_le k.isLt hn))) i := by
  induction n generalizing xs with
  | zero => exact false_tail D xs
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons a xs =>
      rcases i with ⟨b,i⟩
      have ht : n≤xs.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn
      cases b <;> simp only [toList,List.cons_append,wordValue,bit,
        Verification.OrderedBinaryWords.word,one_mul,ih xs ht i,
        List.getElem_cons_zero,Fin.val_zero,Fin.val_succ,List.getElem_cons_succ,
        Bool.false_eq_true,↓reduceIte]

theorem both_word (D : Verification.MilnorWittSymbolRelations.Symbols S A)
    (n : ℕ) (xs : List Sˣ) (hn : n+1≤xs.length) (i : Index n) :
    wordValue D xs (false::(toList n i++[false]))=
      Verification.OrderedBinaryWords.word n
        (fun k => D.symbol (xs[k.val+1]'(by have hh:=k.isLt;omega))) i := by
  cases xs with
  | nil => simp at hn
  | cons a xs =>
    have ht : n≤xs.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hn
    simpa only [wordValue,bit,Bool.false_eq_true,↓reduceIte,one_mul,List.getElem_cons_succ] using right_word D n xs ht i

theorem map_word {B : Type*} [Ring B] (F : A →+* B) (n : ℕ)
    (x : Fin n → A) (i : Index n) :
    F (Verification.OrderedBinaryWords.word n x i)=
      Verification.OrderedBinaryWords.word n (fun k => F (x k)) i :=
  Verification.OrderedBinaryWords.map_word F.toMonoidHom n x i

#print axioms map_word
#print axioms false_tail
#print axioms right_word
#print axioms both_word
end Verification.PathOrderedWordValues
