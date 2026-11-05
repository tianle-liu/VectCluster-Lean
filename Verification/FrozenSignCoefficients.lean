/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignIntertwiner

/-!
# Frozen Sign Coefficients

The original label complex for every additive coefficient group, hence
for every coefficient ring in the sign theorem, with the literal face formula.
-/
noncomputable section
namespace Verification.FrozenSignCoefficients
open Verification.FrozenSignTerms Verification.FrozenSignStates Verification.FrozenSignFamily
open Verification.FrozenSignDifferential Verification.FrozenSignIncidence Verification.SignComplex
variable {V C A : Type} [Fintype V] [Fintype C] [DecidableEq V] [LinearOrder (V ⊕ C)] [AddCommGroup A]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

def functionCoordinates (p : ℕ) :
    ({s : State (V ⊕ C) // allowed B F s ∧ (holes s).card=p} → A) ≃+ (Labels B F p → A) where
  toFun f q := f (degreeEquiv B F p q)
  invFun f s := f ((degreeEquiv B F p).symm s)
  left_inv f := by funext s; simp
  right_inv f := by funext q;simp
  map_add' _ _ := rfl

def coordinates (p : ℕ) : degreeCochains (R := A) (allowed B F) p ≃+ (Labels B F p → A) :=
  (degreeCochainsEquiv (allowed B F) p).trans (functionCoordinates B F p)

omit [DecidableEq V] in
theorem coordinates_apply (p : ℕ) (f : degreeCochains (R := A) (allowed B F) p) (q : Labels B F p) :
    coordinates B F p f q=f.val ⟨state B q.1.val q.2,state_allowed B F q.1.val q.1.property.1 q.2⟩ := rfl

def differential (p : ℕ) : (Labels B F p → A) →+ (Labels B F (p+1) → A) :=
  (coordinates B F (p+1)).toAddMonoidHom.comp
    ((degreeDifferential (allowed B F) p).comp (coordinates B F p).symm.toAddMonoidHom)

omit [DecidableEq V] in
include down indep in
theorem differential_squared (p : ℕ) (f : Labels B F p → A) :
    differential B F (p+1) (differential B F p f)=0 := by
  change coordinates B F (p+2) (degreeDifferential (allowed B F) (p+1)
    ((coordinates B F (p+1)).symm (coordinates B F (p+1)
      (degreeDifferential (allowed B F) p ((coordinates B F p).symm f)))))=0
  rw [AddEquiv.symm_apply_apply,degreeDifferential_squared (allowed B F) (faces B F down indep),map_zero]

theorem face_evaluation (p : ℕ) (f : degreeCochains (R := A) (allowed B F) p)
    (J : Index F (p+1)) (j : J.val) (ε : ActualSignLabels.labels B J.val) :
    let I := sourceIndex F down p J j
    let e := extension B I.val J.val j.val (Finset.not_mem_erase _ _)
      (Finset.insert_erase j.property) (face_zero B F indep p J j) ε
    coordinates B F p f ⟨I,e 0⟩-coordinates B F p f ⟨I,e 1⟩=
      extendCochain (allowed B F) f.val (faceState (state B J.val ε) (Sum.inl j.val) false)-
      extendCochain (allowed B F) f.val (faceState (state B J.val ε) (Sum.inl j.val) true) := by
  dsimp only
  let I := sourceIndex F down p J j
  let hB := face_zero B F indep p J j
  let e := extension B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε
  have h0 : state B I.val (e 0)=faceState (state B J.val ε) (Sum.inl j.val) false := by
    simpa only [show decide ((0:ZMod 2)=1)=false by decide] using
      extension_state B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε 0
  have h1 : state B I.val (e 1)=faceState (state B J.val ε) (Sum.inl j.val) true := by
    simpa only [decide_true] using
      extension_state B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε 1
  change coordinates B F p f ⟨I,e 0⟩-coordinates B F p f ⟨I,e 1⟩=_
  rw [coordinates_apply,coordinates_apply,← h0,← h1]
  rw [extendCochain_apply _ _ _ (state_allowed B F I.val I.property.1 (e 0)),
    extendCochain_apply _ _ _ (state_allowed B F I.val I.property.1 (e 1))]

theorem differential_formula (p : ℕ) (f : Labels B F p → A) (q : Labels B F (p+1)) :
    differential B F p f q=∑ j : q.1.val, incidence (C := C) q.1.val j.val •
      (f ⟨sourceIndex F down p q.1 j,
        extension B (q.1.val.erase j.val) q.1.val j.val (Finset.not_mem_erase _ _)
          (Finset.insert_erase j.property) (face_zero B F indep p q.1 j) q.2 0⟩-
       f ⟨sourceIndex F down p q.1 j,
        extension B (q.1.val.erase j.val) q.1.val j.val (Finset.not_mem_erase _ _)
          (Finset.insert_erase j.property) (face_zero B F indep p q.1 j) q.2 1⟩) := by
  let a := (coordinates B F p).symm f
  change coordinates B F (p+1) (degreeDifferential (allowed B F) p a) q=_
  rw [coordinates_apply]
  change SignComplex.differential (extendCochain (allowed B F) a.val) (state B q.1.val q.2)=_
  rw [differential_eq_sum_holes,state_holes]
  simp only [zeroSet,Finset.sum_map,Function.Embedding.inl_apply]
  rw [← Finset.sum_coe_sort q.1.val]
  apply Finset.sum_congr rfl
  intro j _
  rw [state_incidence,← face_evaluation B F down indep p a q.1 j q.2]
  simp only [a,AddEquiv.apply_symm_apply]
  rfl

def complex : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of ℤ (Labels B F p → A))
    (fun p => ModuleCat.ofHom (differential B F p).toIntLinearMap)
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact differential_squared B F down indep p f)

#print axioms functionCoordinates
#print axioms coordinates
#print axioms coordinates_apply
#print axioms differential
#print axioms differential_squared
#print axioms face_evaluation
#print axioms differential_formula
#print axioms complex
end Verification.FrozenSignCoefficients
