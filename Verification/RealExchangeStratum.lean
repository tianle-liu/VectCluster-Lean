/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealExchangeCharacters
import Verification.RealCharacterComponents

/-!
# Real Exchange Stratum

A homeomorphism for the literal real zero stratum of the exchange
variety, retaining all original and partner coordinates and all relations.
-/
noncomputable section
namespace Verification.RealExchangeStratum
open Verification.RealExchangeCharacters Verification.RealCharacterComponents
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ]

def initial (j : τ → κ) (x : (ι ⊕ κ) → ℝ) : (ι ⊕ τ) → ℝ :=
  Sum.elim (fun i => x (Sum.inl i)) (fun t => x (Sum.inr (j t)))

def Point (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :=
  {p : ((ι ⊕ κ) → ℝ) × ((ι ⊕ τ) → ℝ) //
    (∀ i, p.1 (Sum.inl i)=0) ∧ (∀ a, p.1 (Sum.inr a)≠0) ∧
      ∀ v, initial j p.1 v*p.2 v=exchange p.1 (fun a => B a v)}

instance pointTopology (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    TopologicalSpace (Point j B) := inferInstanceAs (TopologicalSpace
      {p : ((ι ⊕ κ) → ℝ) × ((ι ⊕ τ) → ℝ) //
        (∀ i, p.1 (Sum.inl i)=0) ∧ (∀ a, p.1 (Sum.inr a)≠0) ∧
          ∀ v, initial j p.1 v*p.2 v=exchange p.1 (fun a => B a v)})

def reduced (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) : κ → ι → ℤ :=
  fun a i => B (Sum.inr a) (Sum.inl i)

theorem exchange_reduced (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0)
    (x : (ι ⊕ κ) → ℝ) (i : ι) :
    exchange x (fun a => B a (Sum.inl i))=exchange (fun a => x (Sum.inr a)) (fun a => reduced B a i) := by
  simp [exchange,Fintype.prod_sum_type,hB,reduced]

def project (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0) (p : Point j B) :
    (ι → ℝ) × Negative (reduced B) :=
  (fun i => p.val.2 (Sum.inl i),⟨⟨fun a => p.val.1 (Sum.inr a),p.property.2.1⟩,by
    intro i
    apply (exchange_zero_iff _ p.property.2.1 _).mp
    rw [← exchange_reduced B hB p.val.1 i,← p.property.2.2 (Sum.inl i)]
    simp [initial,p.property.1]⟩)

def restoreOriginal (x : κ → ℝ) : (ι ⊕ κ) → ℝ := Sum.elim (fun _ => 0) x

def restorePartner (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (a : ι → ℝ) (x : κ → ℝ) : (ι ⊕ τ) → ℝ :=
  Sum.elim a (fun t => exchange (restoreOriginal x) (fun c => B c (Sum.inr t))/x (j t))

def restore (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0)
    (p : (ι → ℝ) × Negative (reduced B)) : Point j B :=
  ⟨(restoreOriginal p.2.val.val,restorePartner j B p.1 p.2.val.val),by
    refine ⟨fun _ => rfl,p.2.val.property,?_⟩
    intro v
    cases v with
    | inl i =>
      change 0*p.1 i=exchange _ _
      rw [zero_mul,exchange_reduced B hB]
      exact ((exchange_zero_iff _ p.2.val.property _).mpr (p.2.property i)).symm
    | inr t =>
      change p.2.val.val (j t)*(exchange _ _/p.2.val.val (j t))=_
      exact mul_div_cancel₀ _ (p.2.val.property (j t))⟩

theorem project_restore (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0)
    (p : (ι → ℝ) × Negative (reduced B)) : project j B hB (restore j B hB p)=p := rfl

theorem restore_project (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0) (p : Point j B) :
    restore j B hB (project j B hB p)=p := by
  have hx : restoreOriginal (fun a => p.val.1 (Sum.inr a))=p.val.1 := by
    funext v
    cases v with
    | inl i => exact (p.property.1 i).symm
    | inr a => rfl
  apply Subtype.ext
  apply Prod.ext hx
  funext v
  cases v with
  | inl i => rfl
  | inr t =>
    change exchange (restoreOriginal (fun a => p.val.1 (Sum.inr a))) _ /
      p.val.1 (Sum.inr (j t))=p.val.2 (Sum.inr t)
    rw [hx,← p.property.2.2 (Sum.inr t)]
    change (p.val.1 (Sum.inr (j t))*p.val.2 (Sum.inr t))/p.val.1 (Sum.inr (j t))=_
    exact mul_div_cancel_left₀ _ (p.property.2.1 (j t))

omit [Fintype ι] [Fintype κ] in
theorem restoreOriginal_continuous : Continuous (restoreOriginal : (κ → ℝ) → (ι ⊕ κ) → ℝ) := by
  apply continuous_pi
  intro v
  cases v with
  | inl i => exact continuous_const
  | inr a => exact continuous_apply a

theorem project_continuous (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0) : Continuous (project j B hB) := by
  apply Continuous.prodMk
  · exact continuous_pi (fun i => (continuous_apply (Sum.inl i)).comp continuous_subtype_val.snd)
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_pi (fun a => (continuous_apply (Sum.inr a)).comp continuous_subtype_val.fst)

theorem restore_continuous (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0) : Continuous (restore j B hB) := by
  have hx : Continuous (fun p : (ι → ℝ) × Negative (reduced B) => p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact restoreOriginal_continuous.comp hx
  · apply continuous_pi
    intro v
    cases v with
    | inl i => exact (continuous_apply i).comp continuous_fst
    | inr t =>
      exact ((exchange_continuous _).comp (restoreOriginal_continuous.comp hx)).div
        ((continuous_apply (j t)).comp hx) (fun p => p.2.val.property (j t))

def coordinates (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i)=0) :
    Point j B ≃ₜ ((ι → ℝ) × Negative (reduced B)) where
  toFun := project j B hB
  invFun := restore j B hB
  left_inv := restore_project j B hB
  right_inv := project_restore j B hB
  continuous_toFun := project_continuous j B hB
  continuous_invFun := restore_continuous j B hB

#print axioms initial
#print axioms Point
#print axioms pointTopology
#print axioms reduced
#print axioms exchange_reduced
#print axioms project
#print axioms restoreOriginal
#print axioms restorePartner
#print axioms restore
#print axioms project_restore
#print axioms restore_project
#print axioms restoreOriginal_continuous
#print axioms project_continuous
#print axioms restore_continuous
#print axioms coordinates
end Verification.RealExchangeStratum
