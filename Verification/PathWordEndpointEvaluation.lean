/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathMilnorWittListFace
import Verification.PathEndpointWords

/-!
# Path Word Endpoint Evaluation

Evaluation in ordinary MW symbols respects the actual constant-endpoint
projectors. This establishes endpoint quotient compatibility internally.
-/
noncomputable section
namespace Verification.PathWordEndpointEvaluation
open Verification.MilnorWittSymbolRelations Verification.PathMilnorWittWordFace
open Verification.PathMilnorWittCoefficients Verification.PathMilnorWittTriple
open Verification.PathEndpointWords Verification.PathRhoEndpoint
variable {S B : Type*} [CommRing S] [Ring B] (D : Symbols S B)
local notation "C" => Verification.PathCoefficientRing.Coeff
local notation "v" => realize D.toCoefficients

theorem evaluate_smul (xs : List Sˣ) (c : C) (f : List Bool →₀ C) :
    evaluate D xs (c • f)=v c * evaluate D xs f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [smul_zero,map_zero,mul_zero]
  | add f g hf hg => rw [smul_add,map_add,hf,hg,map_add,mul_add]
  | single w b => rw [Finsupp.smul_single,evaluate_single,evaluate_single];simp only [smul_eq_mul,map_mul,mul_assoc]

theorem right_value (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (bits : List Bool) (hlen : bits.length=xs.length+1) :
    wordValue D (xs++[a]) bits=v (rightScalar k bits)*wordValue D (xs++[a]) (normalizeRight bits) := by
  induction xs generalizing bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have he : bs=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil,List.length_cons,Nat.add_right_cancel_iff] using hlen)
      subst bs
      cases b <;> simp only [List.nil_append,wordValue,bit,Bool.false_eq_true,↓reduceIte,
        normalizeRight,rightScalar,evaluation,map_one,ha,one_mul,mul_one]
  | cons x xs ih =>
    cases bits with
    | nil => simp at hlen
    | cons b bs =>
      have hh : bs.length=xs.length+1 := by simp only [List.length_cons] at hlen;omega
      cases bs with
      | nil => simp at hh
      | cons c cs =>
        have hv := ih (c::cs) hh
        simp only [List.cons_append,wordValue,normalizeRight,rightScalar] at hv ⊢
        rw [hv,←mul_assoc,←central D.toCoefficients _ (bit (D.symbol x) b),mul_assoc]

theorem left_value (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (bits : List Bool) :
    wordValue D (a::xs) bits=v (leftScalar k bits)*wordValue D (a::xs) (normalizeLeft bits) := by
  cases bits with
  | nil => simp only [wordValue,normalizeLeft,leftScalar,map_one,one_mul]
  | cons b bs => cases b <;> simp only [wordValue,bit,Bool.false_eq_true,↓reduceIte,
      normalizeLeft,leftScalar,evaluation,map_one,ha,one_mul]

theorem right_single (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (bits : List Bool) (hlen : bits.length=xs.length+1) :
    evaluate D (xs++[a]) (Verification.PathRightEndpoint.projection k (Finsupp.single bits 1))=
      evaluate D (xs++[a]) (Finsupp.single bits 1) := by
  rw [right_projection_column,evaluate_smul,evaluate_single,evaluate_single,map_one,one_mul,one_mul]
  exact (right_value D k a ha xs bits hlen).symm

theorem left_single (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (bits : List Bool) :
    evaluate D (a::xs) (Verification.PathLeftEndpoint.projection k (Finsupp.single bits 1))=
      evaluate D (a::xs) (Finsupp.single bits 1) := by
  rw [left_projection_column,evaluate_smul,evaluate_single,evaluate_single,map_one,one_mul,one_mul]
  exact (left_value D k a ha xs bits).symm

theorem right_layer (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (f : List Bool →₀ C)
    (hf : f ∈ Verification.PathRhoFinite.layer (R:=C) (xs.length+1)) :
    evaluate D (xs++[a]) (Verification.PathRightEndpoint.projection k f)=evaluate D (xs++[a]) f := by
  let L : Submodule C (List Bool →₀ C) :=
    { carrier := {x | evaluate D (xs++[a]) (Verification.PathRightEndpoint.projection k x)=evaluate D (xs++[a]) x}
      zero_mem' := by simp only [Set.mem_setOf_eq,map_zero]
      add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *;rw [map_add,map_add,map_add,hx,hy]
      smul_mem' := by intro c x hx; simp only [Set.mem_setOf_eq] at *;rw [map_smul,evaluate_smul,evaluate_smul,hx] }
  have hh : Verification.PathRhoFinite.layer (R:=C) (xs.length+1)≤L := by
    rw [Verification.PathRhoFinite.layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨bits,hbits,rfl⟩
    exact right_single D k a ha xs bits hbits
  exact hh hf

theorem left_all (k : C) (a : Sˣ) (ha : D.symbol a=v k)
    (xs : List Sˣ) (f : List Bool →₀ C) :
    evaluate D (a::xs) (Verification.PathLeftEndpoint.projection k f)=evaluate D (a::xs) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => rw [map_add,map_add,map_add,hf,hg]
  | single bits c =>
    have he : Finsupp.single bits c=c • Finsupp.single bits (1:C) := by simp
    rw [he,map_smul,evaluate_smul,evaluate_smul,left_single D k a ha xs bits]

#print axioms evaluate_smul
#print axioms right_value
#print axioms left_value
#print axioms right_single
#print axioms left_single
#print axioms right_layer
#print axioms left_all
end Verification.PathWordEndpointEvaluation
