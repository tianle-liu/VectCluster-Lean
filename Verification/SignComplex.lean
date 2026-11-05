/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The finite sign differential

A state `ι → Option Bool` represents exactly a subset and a sign assignment
on its complement: `none` marks a vertex of the subset, and `some false` /
`some true` are the positive / negative signs. Vertices carry an arbitrary
finite linear order. The differential is the manuscript's alternating sum
of the positive-minus-negative coordinate extensions.

The algebraic results here concern the complex identity at manuscript.tex
2996--3010. They make no assertion about real-locus topology or comparison
with geometric cohomology.
-/

namespace Verification.SignComplex

open Finset

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

abbrev State (ι : Type*) := ι → Option Bool

def holes (s : State ι) : Finset ι := univ.filter (fun i => s i = none)

def faceState (s : State ι) (i : ι) (b : Bool) : State ι :=
  Function.update s i (some b)

theorem holes_faceState (s : State ι) (i : ι) (b : Bool) :
    holes (faceState s i b) = (holes s).erase i := by
  ext j
  by_cases h : j = i
  · subst j; simp [holes, faceState]
  · simp [holes, faceState, Function.update_of_ne h, h]

omit [Fintype ι] in
theorem faceState_commute (s : State ι) (i j : ι) (hi : i ≠ j) (a b : Bool) :
    faceState (faceState s i a) j b = faceState (faceState s j b) i a := by
  exact Function.update_comm hi _ _ _

def incidenceRank (s : State ι) (i : ι) : ℕ :=
  ((holes s).filter (fun j => j < i)).card

def incidenceSign (s : State ι) (i : ι) : ℤ := (-1) ^ incidenceRank s i

theorem incidenceRank_face_later (s : State ι) (i j : ι) (hij : i < j) (b : Bool) :
    incidenceRank (faceState s j b) i = incidenceRank s i := by
  simp only [incidenceRank, holes_faceState, Finset.filter_erase]
  rw [Finset.erase_eq_of_not_mem]
  simp only [Finset.mem_filter, not_and]
  intro _ hji
  exact (lt_asymm hij hji)

theorem incidenceRank_face_earlier (s : State ι) (i j : ι)
    (hi : s i = none) (hij : i < j) (b : Bool) :
    incidenceRank (faceState s i b) j + 1 = incidenceRank s j := by
  have himem : i ∈ (holes s).filter (fun k => k < j) := by simp [holes, hi, hij]
  simpa only [incidenceRank, holes_faceState, Finset.filter_erase] using
    Finset.card_erase_add_one himem

theorem incidenceSign_update_bit (s : State ι) (i j : ι) (a b : Bool) :
    incidenceSign (faceState s i a) j = incidenceSign (faceState s i b) j := by
  simp only [incidenceSign, incidenceRank, holes_faceState]

theorem incidence_sign_opposite (s : State ι) (i j : ι)
    (hi : s i = none) (hj : s j = none) (hij : i ≠ j) (a b : Bool) :
    incidenceSign s i * incidenceSign (faceState s i a) j =
      -(incidenceSign s j * incidenceSign (faceState s j b) i) := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have he := incidenceRank_face_earlier s i j hi hlt a
    have hl := incidenceRank_face_later s i j hlt b
    simp only [incidenceSign, hl]
    rw [← he, pow_succ]
    ring
  · have he := incidenceRank_face_earlier s j i hj hlt b
    have hl := incidenceRank_face_later s j i hlt a
    simp only [incidenceSign, hl]
    rw [← he, pow_succ]
    ring

section Differential

variable {R : Type*} [AddCommGroup R]

abbrev Cochain (ι R : Type*) := State ι → R

def signFace (i : ι) (f : Cochain ι R) (s : State ι) : R :=
  if s i = none then incidenceSign s i • (f (faceState s i false) - f (faceState s i true))
  else 0

def differential (f : Cochain ι R) : Cochain ι R := fun s => ∑ i, signFace i f s

/-- The defining formula, with the sum indexed only by the removed vertices. -/
theorem differential_eq_sum_holes (f : Cochain ι R) (s : State ι) :
    differential f s = ∑ i ∈ holes s, incidenceSign s i •
      (f (faceState s i false) - f (faceState s i true)) := by
  simp only [differential, holes, Finset.sum_filter, signFace]

theorem signFace_add (i : ι) (f g : Cochain ι R) (s : State ι) :
    signFace i (f + g) s = signFace i f s + signFace i g s := by
  by_cases h : s i = none
  · simp only [signFace, h, if_true, Pi.add_apply, smul_sub, smul_add]
    abel
  · simp [signFace, h]

theorem signFace_zero (i : ι) (s : State ι) : signFace i (0 : Cochain ι R) s = 0 := by
  simp [signFace]

theorem signFace_sum {κ : Type*} (t : Finset κ) (F : κ → Cochain ι R) (i : ι) (s : State ι) :
    signFace i (fun x => ∑ k ∈ t, F k x) s = ∑ k ∈ t, signFace i (F k) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using signFace_zero (R := R) i s
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (signFace_add i (F a) (fun x => ∑ k ∈ t, F k x) s).trans (by rw [ih])

theorem signFace_same (i : ι) (f : Cochain ι R) (s : State ι) :
    signFace i (signFace i f) s = 0 := by
  simp [signFace, faceState]

def rectangle (f : Cochain ι R) (s : State ι) (i j : ι) : R :=
  f (faceState (faceState s i false) j false) - f (faceState (faceState s i false) j true) -
    f (faceState (faceState s i true) j false) + f (faceState (faceState s i true) j true)

omit [Fintype ι] in
theorem rectangle_symmetric (f : Cochain ι R) (s : State ι) (i j : ι) (hij : i ≠ j) :
    rectangle f s i j = rectangle f s j i := by
  simp only [rectangle, faceState_commute s i j hij]
  abel

theorem signFace_twice (f : Cochain ι R) (s : State ι) (i j : ι)
    (hi : s i = none) (hj : s j = none) (hij : i ≠ j) :
    signFace i (signFace j f) s =
      (incidenceSign s i * incidenceSign (faceState s i false) j) • rectangle f s i j := by
  have hup (b : Bool) : faceState s i b j = none := by
    simpa [faceState, Function.update_of_ne (Ne.symm hij)] using hj
  simp only [signFace, hi, hup, if_true,
    incidenceSign_update_bit s i j true false, rectangle, smul_sub, smul_add, mul_smul]
  abel

theorem signFace_anticommute (f : Cochain ι R) (s : State ι) (i j : ι) (hij : i ≠ j) :
    signFace i (signFace j f) s + signFace j (signFace i f) s = 0 := by
  by_cases hi : s i = none
  · by_cases hj : s j = none
    · rw [signFace_twice f s i j hi hj hij,
        signFace_twice f s j i hj hi (Ne.symm hij),
        incidence_sign_opposite s i j hi hj hij false false,
        rectangle_symmetric f s i j hij]
      simp
    · have hup (b : Bool) : faceState s i b j ≠ none := by
        simpa [faceState, Function.update_of_ne (Ne.symm hij)] using hj
      simp [signFace, hj, hup]
  · have hup (b : Bool) : faceState s j b i ≠ none := by
      simpa [faceState, Function.update_of_ne hij] using hi
    simp [signFace, hi, hup]

/-- All ordered two-face contributions cancel by the swap involution. -/
theorem differential_squared (f : Cochain ι R) (s : State ι) :
    differential (differential f) s = 0 := by
  unfold differential
  simp_rw [signFace_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · intro p _
    by_cases h : p.1 = p.2
    · simp [h, signFace_same]
    · exact signFace_anticommute f s p.1 p.2 h
  · intro p _ hn he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hn (by simpa [h] using signFace_same p.2 f s)
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_univ, and_self]
  · intro p _
    cases p
    rfl

theorem differential_add (f g : Cochain ι R) :
    differential (f + g) = differential f + differential g := by
  funext s
  simp only [differential, signFace_add, Finset.sum_add_distrib, Pi.add_apply]

theorem differential_zero : differential (0 : Cochain ι R) = 0 := by
  funext s
  simp [differential, signFace_zero]

theorem faceState_card (s : State ι) (i : ι) (hi : s i = none) (b : Bool) :
    (holes (faceState s i b)).card + 1 = (holes s).card := by
  rw [holes_faceState]
  exact Finset.card_erase_add_one (by simp [holes, hi])

theorem differential_degree (f : Cochain ι R) (p : ℕ)
    (hf : ∀ s, (holes s).card ≠ p → f s = 0) :
    ∀ s, (holes s).card ≠ p + 1 → differential f s = 0 := by
  intro s hs
  unfold differential
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : s i = none
  · have hf0 : f (faceState s i false) = 0 :=
      hf _ (by have := faceState_card s i hi false; omega)
    have hf1 : f (faceState s i true) = 0 :=
      hf _ (by have := faceState_card s i hi true; omega)
    simp [signFace, hf0, hf1]
  · simp [signFace, hi]

section Restriction

variable (Valid : State ι → Prop)

noncomputable def extendCochain (f : {s : State ι // Valid s} → R) : Cochain ι R := by
  classical
  exact fun s => if hs : Valid s then f ⟨s, hs⟩ else 0

noncomputable def restrictedDifferential (f : {s : State ι // Valid s} → R) :
    {s : State ι // Valid s} → R := fun s => differential (extendCochain Valid f) s.val

omit [Fintype ι] [LinearOrder ι] in
theorem extendCochain_apply (f : {s : State ι // Valid s} → R) (s : State ι) (hs : Valid s) :
    extendCochain Valid f s = f ⟨s, hs⟩ := by simp [extendCochain, hs]

variable (closed : ∀ s, Valid s → ∀ i, s i = none → ∀ b, Valid (faceState s i b))

include closed in
theorem differential_local (f g : Cochain ι R)
    (hfg : ∀ s, Valid s → f s = g s) (s : State ι) (hs : Valid s) :
    differential f s = differential g s := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : s i = none
  · simp only [signFace, hi, if_true]
    rw [hfg _ (closed s hs i hi false), hfg _ (closed s hs i hi true)]
  · simp [signFace, hi]

include closed in
/-- The complex identity survives restriction to any family closed under allowed faces. -/
theorem restrictedDifferential_squared (f : {s : State ι // Valid s} → R)
    (s : {s : State ι // Valid s}) :
    restrictedDifferential Valid (restrictedDifferential Valid f) s = 0 := by
  change differential (extendCochain Valid (restrictedDifferential Valid f)) s.val = 0
  rw [differential_local Valid closed _ (differential (extendCochain Valid f))
    (fun t ht => by simp [extendCochain_apply Valid _ t ht, restrictedDifferential]) s.val s.property]
  exact differential_squared _ _

omit [Fintype ι] [LinearOrder ι] in
theorem extendCochain_add (f g : {s : State ι // Valid s} → R) :
    extendCochain Valid (f + g) = extendCochain Valid f + extendCochain Valid g := by
  funext s
  by_cases hs : Valid s <;> simp [extendCochain, hs]

omit [Fintype ι] [LinearOrder ι] in
theorem extendCochain_zero : extendCochain Valid (0 : {s : State ι // Valid s} → R) = 0 := by
  funext s
  simp [extendCochain]

theorem restrictedDifferential_add (f g : {s : State ι // Valid s} → R) :
    restrictedDifferential Valid (f + g) =
      restrictedDifferential Valid f + restrictedDifferential Valid g := by
  funext s
  simp [restrictedDifferential, extendCochain_add, differential_add]

theorem restrictedDifferential_zero :
    restrictedDifferential Valid (0 : {s : State ι // Valid s} → R) = 0 := by
  funext s
  simp [restrictedDifferential, extendCochain_zero, differential_zero]

/-- Actual additive cochains in degree `p`, extended by zero to the other degrees. -/
def degreeCochains (p : ℕ) : AddSubgroup ({s : State ι // Valid s} → R) where
  carrier := {f | ∀ s, (holes s.val).card ≠ p → f s = 0}
  zero_mem' := by intro s _; rfl
  add_mem' := by intro f g hf hg s hs; simp [hf s hs, hg s hs]
  neg_mem' := by intro f hf s hs; simp [hf s hs]

/-- These are exactly functions on the admissible states of degree `p`. -/
noncomputable def degreeCochainsEquiv (p : ℕ) :
    degreeCochains (R := R) Valid p ≃+
      ({s : State ι // Valid s ∧ (holes s).card = p} → R) := by
  classical
  exact {
    toFun := fun f s => f.val ⟨s.val, s.property.1⟩
    invFun := fun g => ⟨fun s => if hs : (holes s.val).card = p then
      g ⟨s.val, s.property, hs⟩ else 0, by intro s hs; simp [hs]⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext s
      by_cases hs : (holes s.val).card = p
      · simp [hs]
      · simpa [hs] using (f.property s hs).symm
    right_inv := by intro g; funext s; simp [s.property.2]
    map_add' := by intro f g; rfl }

omit [LinearOrder ι] in
theorem degreeCochains_vanish (bound p : ℕ)
    (hb : ∀ s, Valid s → (holes s).card ≤ bound) (hp : bound < p)
    (f : degreeCochains (R := R) Valid p) : f = 0 := by
  apply Subtype.ext
  funext s
  exact f.property s (by have := hb s.val s.property; omega)

theorem restrictedDifferential_degree (p : ℕ) (f : degreeCochains (R := R) Valid p) :
    restrictedDifferential Valid f.val ∈ degreeCochains (R := R) Valid (p + 1) := by
  intro s hs
  apply differential_degree (extendCochain Valid f.val) p _ s.val hs
  intro t ht
  by_cases hv : Valid t
  · rw [extendCochain_apply Valid _ t hv]
    exact f.property ⟨t, hv⟩ ht
  · simp [extendCochain, hv]

/-- The degree-indexed additive differential between the actual cochain groups. -/
noncomputable def degreeDifferential (p : ℕ) :
    degreeCochains (R := R) Valid p →+ degreeCochains (R := R) Valid (p + 1) where
  toFun f := ⟨restrictedDifferential Valid f.val, restrictedDifferential_degree Valid p f⟩
  map_zero' := by apply Subtype.ext; exact restrictedDifferential_zero Valid
  map_add' f g := by apply Subtype.ext; exact restrictedDifferential_add Valid f.val g.val

include closed in
theorem degreeDifferential_squared (p : ℕ) (f : degreeCochains (R := R) Valid p) :
    degreeDifferential Valid (p + 1) (degreeDifferential Valid p f) = 0 := by
  apply Subtype.ext
  funext s
  exact restrictedDifferential_squared Valid closed f.val s

include closed in
theorem degreeDifferential_comp (p : ℕ) :
    (degreeDifferential (R := R) Valid (p + 1)).comp (degreeDifferential Valid p) = 0 := by
  apply AddMonoidHom.ext
  intro f
  exact degreeDifferential_squared Valid closed p f

end Restriction

end Differential

section ExchangeSigns

variable {S : Type*} [Semiring S]

/-- Boolean sign bits, interpreted in a coefficient semiring (in the paper, `𝔽₂`). -/
def signBit (x : Option Bool) : S := if x = some true then 1 else 0

def exchangeSignValue (B : ι → ι → S) (s : State ι) (i : ι) : S :=
  ∑ a, B a i * signBit (s a)

omit [LinearOrder ι] in
/-- Summing over all coordinates is exactly the paper's sum over the complement. -/
theorem exchangeSignValue_complement (B : ι → ι → S) (s : State ι) (i : ι) :
    exchangeSignValue B s i = ∑ a ∈ univ.filter (fun a => s a ≠ none), B a i * signBit (s a) := by
  simp only [exchangeSignValue, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : s a = none <;> simp [ha, signBit]

theorem exchangeSignValue_face (B : ι → ι → S) (s : State ι) (i j : ι)
    (hB : B j i = 0) (b : Bool) :
    exchangeSignValue B (faceState s j b) i = exchangeSignValue B s i := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = j
  · subst a; simp [hB]
  · simp [faceState, Function.update_of_ne ha]

/-- Admissible independent subsets together with the exchange equations on sign bits. -/
def exchangeSignAllowed (B : ι → ι → S) (Family : Finset ι → Prop) (s : State ι) : Prop :=
  Family (holes s) ∧ ∀ i ∈ holes s, exchangeSignValue B s i = 1

/-- Independence makes both sign extensions admissible; no complex identity is assumed. -/
theorem exchangeSignAllowed_faces (B : ι → ι → S) (Family : Finset ι → Prop)
    (down : ∀ I J, J ⊆ I → Family I → Family J)
    (indep : ∀ I, Family I → ∀ i ∈ I, ∀ j ∈ I, i ≠ j → B j i = 0) :
    ∀ s, exchangeSignAllowed B Family s → ∀ j, s j = none →
      ∀ b, exchangeSignAllowed B Family (faceState s j b) := by
  intro s hs j hj b
  constructor
  · rw [holes_faceState]
    exact down _ _ (Finset.erase_subset _ _) hs.1
  · intro i hi
    rw [holes_faceState] at hi
    obtain ⟨hij, hi⟩ := Finset.mem_erase.mp hi
    rw [exchangeSignValue_face B s i j (indep _ hs.1 i hi j (by simp [holes, hj]) hij) b]
    exact hs.2 i hi

/-- The actual graph-independent mutable subsets, with frozen vertices excluded. -/
def independentFamily (mutable : Finset ι) (edge : ι → ι → Prop) (I : Finset ι) : Prop :=
  I ⊆ mutable ∧ ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ edge j i

omit [Fintype ι] [LinearOrder ι] in
theorem independentFamily_down (mutable : Finset ι) (edge : ι → ι → Prop) :
    ∀ I J, J ⊆ I → independentFamily mutable edge I → independentFamily mutable edge J := by
  intro I J hJI hI
  exact ⟨hJI.trans hI.1, fun i hi j hj hij => hI.2 i (hJI hi) j (hJI hj) hij⟩

/-- The manuscript's degree-indexed sign differential squares to zero on independent sets. -/
theorem exchange_sign_differential_squared {R : Type*} [AddCommGroup R]
    (B : ι → ι → S) (mutable : Finset ι) (edge : ι → ι → Prop)
    (hB : ∀ i j, ¬ edge j i → B j i = 0) (p : ℕ)
    (f : degreeCochains (R := R) (exchangeSignAllowed B (independentFamily mutable edge)) p) :
    degreeDifferential (exchangeSignAllowed B (independentFamily mutable edge)) (p + 1)
      (degreeDifferential (exchangeSignAllowed B (independentFamily mutable edge)) p f) = 0 := by
  apply degreeDifferential_squared
  apply exchangeSignAllowed_faces B (independentFamily mutable edge)
    (independentFamily_down mutable edge)
  intro I hI i hi j hj hij
  exact hB i j (hI.2 i hi j hj hij)

end ExchangeSigns

#print axioms holes_faceState
#print axioms faceState_commute
#print axioms incidenceRank_face_later
#print axioms incidenceRank_face_earlier
#print axioms incidenceSign_update_bit
#print axioms incidence_sign_opposite
#print axioms differential_eq_sum_holes
#print axioms signFace_add
#print axioms signFace_zero
#print axioms signFace_sum
#print axioms signFace_same
#print axioms rectangle_symmetric
#print axioms signFace_twice
#print axioms signFace_anticommute
#print axioms differential_squared
#print axioms differential_add
#print axioms differential_zero
#print axioms faceState_card
#print axioms differential_degree
#print axioms extendCochain_apply
#print axioms differential_local
#print axioms restrictedDifferential_squared
#print axioms extendCochain_add
#print axioms extendCochain_zero
#print axioms restrictedDifferential_add
#print axioms restrictedDifferential_zero
#print axioms restrictedDifferential_degree
#print axioms degreeCochainsEquiv
#print axioms degreeCochains_vanish
#print axioms degreeDifferential
#print axioms degreeDifferential_squared
#print axioms degreeDifferential_comp
#print axioms exchangeSignValue_face
#print axioms exchangeSignValue_complement
#print axioms exchangeSignAllowed_faces
#print axioms independentFamily_down
#print axioms exchange_sign_differential_squared

end Verification.SignComplex

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.SignComplex.Cochain
#print axioms Verification.SignComplex.State
#print axioms Verification.SignComplex.degreeCochains
#print axioms Verification.SignComplex.differential
#print axioms Verification.SignComplex.exchangeSignAllowed
#print axioms Verification.SignComplex.exchangeSignValue
#print axioms Verification.SignComplex.extendCochain
#print axioms Verification.SignComplex.faceState
#print axioms Verification.SignComplex.holes
#print axioms Verification.SignComplex.incidenceRank
#print axioms Verification.SignComplex.incidenceSign
#print axioms Verification.SignComplex.independentFamily
#print axioms Verification.SignComplex.rectangle
#print axioms Verification.SignComplex.restrictedDifferential
#print axioms Verification.SignComplex.signBit
#print axioms Verification.SignComplex.signFace
