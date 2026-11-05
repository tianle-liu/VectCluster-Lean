/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimitiveSignFiber

/-!
# Matrix Sign Labels

Literal affine equations for the sign bits, with arbitrary prescribed
right-hand side. The column map is the original integral map.
-/
noncomputable section
namespace Verification.MatrixSignLabels
open Verification.PrimitiveSignFiber
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def characterEquiv : (κ → Bit) ≃ₗ[ℤ] ((κ →₀ ℤ) →ₗ[ℤ] Bit) :=
  (Finsupp.basisSingleOne : Basis κ ℤ (κ →₀ ℤ)).constr ℤ

theorem character_apply (x : κ → Bit) (m : κ →₀ ℤ) :
    characterEquiv x m=∑ a, (m a : Bit)*x a := by
  classical
  rw [characterEquiv,Basis.constr_apply_fintype]
  apply Finset.sum_congr rfl
  intro a _
  simp [zsmul_eq_mul]

theorem character_single (x : κ → Bit) (a : κ) :
    characterEquiv x (Finsupp.single a 1)=x a := by
  classical
  rw [character_apply]
  simp [Finsupp.single_apply]

def labels (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (u : ι → Bit) :=
  {x : κ → Bit // ∀ i, ∑ a, (f (Finsupp.single i 1) a : Bit)*x a=u i}

def fiberEquiv (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (u : ι → Bit) :
    labels f u ≃ fiber f (characterEquiv u) := by
  classical
  apply Equiv.subtypeEquiv characterEquiv.toEquiv
  intro x
  constructor
  · intro hx
    apply (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)).ext
    intro i
    change characterEquiv x (f (Finsupp.single i 1))=characterEquiv u (Finsupp.single i 1)
    rw [character_single,character_apply]
    exact hx i
  · intro hx i
    have hh := LinearMap.congr_fun hx (Finsupp.single i 1)
    change characterEquiv x (f (Finsupp.single i 1))=characterEquiv u (Finsupp.single i 1) at hh
    rw [character_single,character_apply] at hh
    exact hh

def coordinates (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (u : ι → Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    labels f u ≃ (Fin (Fintype.card κ-Fintype.card ι) → Bit) := by
  have hr := Verification.PrimitiveTorusRank.quotient_rank f
    (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)) hf hs
  have he : Module.finrank ℤ ((κ →₀ ℤ) ⧸ LinearMap.range f)=Fintype.card κ-Fintype.card ι := by omega
  exact ((fiberEquiv f u).trans
    (Verification.PrimitiveSignFiber.coordinates f (characterEquiv u) hf hs)).trans
      (Equiv.piCongrLeft' (fun _ => Bit) (finCongr he))

theorem card_labels (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (u : ι → Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nat.card (labels f u)=2^(Fintype.card κ-Fintype.card ι) := by
  rw [Nat.card_congr (coordinates f u hf hs)]
  simp [Nat.card_eq_fintype_card,Bit]

theorem nonempty_labels (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) (u : ι → Bit)
    (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty (labels f u) := ⟨(coordinates f u hf hs).symm 0⟩

#print axioms characterEquiv
#print axioms character_apply
#print axioms character_single
#print axioms labels
#print axioms fiberEquiv
#print axioms coordinates
#print axioms card_labels
#print axioms nonempty_labels
end Verification.MatrixSignLabels
