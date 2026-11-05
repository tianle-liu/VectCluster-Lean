/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealTorusSigns
import Verification.RealSignStrata

/-!
# Real Character Components

Actual connected components of the real character equations χ_i=-1,
including the affine stratum factor. The labels are the literal F₂ equations.
-/
noncomputable section
namespace Verification.RealCharacterComponents
open Verification.RealTorusSigns Verification.RealSignStrata Verification.RealCharacterFibers
variable {ι κ : Type*} [Fintype κ]

def bit (b : Bool) : ZMod 2 := if b then 1 else 0

omit [Fintype κ] in
theorem bits_bit (σ : κ → Bool) : bits (fun a => bit (σ a))=σ := by
  funext a
  cases h : σ a <;> simp [bits,bit,h]

omit [Fintype κ] in
theorem bit_bits (ε : κ → ZMod 2) : (fun a => bit (bits ε a))=ε := by
  funext a
  have h : ε a=0 ∨ ε a=1 := by
    generalize ε a=z
    fin_cases z <;> simp
  rcases h with h | h <;> simp [bits,bit,h]

theorem label_of_negative (B : κ → ι → ℤ) (ε : κ → ZMod 2)
    (x : RealOrthants.orthant (bits ε))
    (hx : ∀ i, (∏ a, x.val a^B a i) = -1) :
    ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1 := by
  intro i
  have h := character_log (bits ε) (fun a => B a i) x
  rw [hx i] at h
  have hchar : signCharacter (bits ε) (fun a => B a i)=
      (RealBitSigns.unit (∑ a, (B a i : ZMod 2)*ε a) : ℝ) := by
    unfold signCharacter bits
    simp_rw [sign_of_bit]
    exact RealBitSigns.monomial_sign _ _
  rw [hchar] at h
  have he := Real.exp_pos (∑ a, (B a i:ℝ)*Real.log (x.val a))
  have hz : (∑ a, (B a i : ZMod 2)*ε a)=0 ∨ (∑ a, (B a i : ZMod 2)*ε a)=1 := by
    generalize (∑ a, (B a i : ZMod 2)*ε a)=z
    fin_cases z <;> simp
  rcases hz with hz | hz
  · rw [hz,RealBitSigns.unit_zero] at h
    norm_num at h
    linarith
  · exact hz

def Negative (B : κ → ι → ℤ) := {x : Torus κ // ∀ i, (∏ a, x.val a^B a i) = -1}

instance negativeTopology (B : κ → ι → ℤ) : TopologicalSpace (Negative B) :=
  inferInstanceAs (TopologicalSpace {x : Torus κ // ∀ i, (∏ a, x.val a^B a i) = -1})

def Labels (B : κ → ι → ℤ) := {ε : κ → ZMod 2 // ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1}

instance bitTopology : TopologicalSpace (ZMod 2) := ⊥
instance bitDiscrete : DiscreteTopology (ZMod 2) := ⟨rfl⟩
instance labelsTopology (B : κ → ι → ℤ) : TopologicalSpace (Labels B) :=
  inferInstanceAs (TopologicalSpace {ε : κ → ZMod 2 // ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1})
instance labelsDiscrete (B : κ → ι → ℤ) : DiscreteTopology (Labels B) := by
  classical
  exact inferInstanceAs (DiscreteTopology {ε : κ → ZMod 2 // ∀ i, ∑ a, (B a i : ZMod 2)*ε a=1})

def label (B : κ → ι → ℤ) (x : Negative B) : Labels B :=
  ⟨fun a => bit (signs x.val a),by
    let y : RealOrthants.orthant (bits (fun a => bit (signs x.val a))) :=
      ⟨x.val.val,by rw [bits_bit]; exact signs_condition x.val⟩
    exact label_of_negative B _ y x.property⟩

theorem label_continuous (B : κ → ι → ℤ) : Continuous (label B) := by
  have hf : Continuous (fun x : Negative B => fun a => bit (signs x.val a)) := by
    apply continuous_pi
    intro a
    exact (continuous_of_discreteTopology : Continuous bit).comp
      ((continuous_apply a).comp (signs_continuous.comp continuous_subtype_val))
  exact hf.subtype_mk _

def fiberToPiece (B : κ → ι → ℤ) (ε : Labels B)
    (x : {x : Negative B // label B x=ε}) : negativeFiber B ε.val :=
  ⟨⟨x.val.val.val,by
    have hh := congrArg Subtype.val x.property
    change (fun a => bit (signs x.val.val a))=ε.val at hh
    rw [← hh,bits_bit]
    exact signs_condition x.val.val⟩,x.val.property⟩

def pieceToFiber (B : κ → ι → ℤ) (ε : Labels B)
    (x : negativeFiber B ε.val) : {x : Negative B // label B x=ε} := by
  let y := orthantToFiber (bits ε.val) x.val
  exact ⟨⟨y.val,x.property⟩,by
    apply Subtype.ext
    change (fun a => bit (signs y.val a))=ε.val
    rw [y.property,bit_bits]⟩

def fiberEquiv (B : κ → ι → ℤ) (ε : Labels B) :
    {x : Negative B // label B x=ε} ≃ₜ negativeFiber B ε.val where
  toFun := fiberToPiece B ε
  invFun := pieceToFiber B ε
  left_inv x := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := ((continuous_subtype_val.comp (continuous_subtype_val.comp
    continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ |>.subtype_mk _

theorem label_fiber_contractible (B : κ → ι → ℤ) (ε : Labels B) :
    ContractibleSpace {x : Negative B // label B x=ε} := by
  letI := RealSignStrata.contractible B ε.val ε.property
  exact (fiberEquiv B ε).contractibleSpace

theorem label_surjective (B : κ → ι → ℤ) : Function.Surjective (label B) := by
  intro ε
  obtain ⟨x⟩ := RealSignStrata.nonempty B ε.val ε.property
  exact ⟨(pieceToFiber B ε x).val,(pieceToFiber B ε x).property⟩

def componentsEquiv (B : κ → ι → ℤ) : ConnectedComponents (Negative B) ≃ Labels B := by
  apply DiscreteFiberComponents.componentsEquiv (label B) (label_continuous B) _ (label_surjective B)
  intro ε
  letI := label_fiber_contractible B ε
  infer_instance

#print axioms bit
#print axioms bits_bit
#print axioms bit_bits
#print axioms label_of_negative
#print axioms Negative
#print axioms negativeTopology
#print axioms Labels
#print axioms bitTopology
#print axioms bitDiscrete
#print axioms labelsTopology
#print axioms labelsDiscrete
#print axioms label
#print axioms label_continuous
#print axioms fiberToPiece
#print axioms pieceToFiber
#print axioms fiberEquiv
#print axioms label_fiber_contractible
#print axioms label_surjective
#print axioms componentsEquiv
end Verification.RealCharacterComponents
