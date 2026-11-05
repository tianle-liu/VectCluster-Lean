/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealCharacterComponents

/-!
# Real Affine Components

The affine factor retains exactly the same real components; this is
applied to the literal outside-coordinate character matrix of each stratum.
-/
noncomputable section
namespace Verification.RealAffineComponents
open Verification.RealCharacterComponents
variable {ι κ : Type*} [Fintype κ]

def label (α : Type*) (B : κ → ι → ℤ) : ((α → ℝ) × Negative B) → Labels B :=
  fun x => RealCharacterComponents.label B x.2

def fiberEquiv (α : Type*) (B : κ → ι → ℤ) (ε : Labels B) :
    {x : ((α → ℝ) × Negative B) // label α B x=ε} ≃ₜ
      ((α → ℝ) × {x : Negative B // RealCharacterComponents.label B x=ε}) where
  toFun x := (x.val.1,⟨x.val.2,x.property⟩)
  invFun x := ⟨(x.1,x.2.val),x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem fiber_contractible (α : Type*) (B : κ → ι → ℤ) (ε : Labels B) :
    ContractibleSpace {x : ((α → ℝ) × Negative B) // label α B x=ε} := by
  exact ((fiberEquiv α B ε).trans ((Homeomorph.refl _).prodCongr
    ((RealCharacterComponents.fiberEquiv B ε).trans
      (RealSignStrata.coordinates B ε.val ε.property)))).contractibleSpace

theorem label_surjective (α : Type*) (B : κ → ι → ℤ) : Function.Surjective (label α B) := by
  intro ε
  obtain ⟨x,hx⟩ := RealCharacterComponents.label_surjective B ε
  exact ⟨(0,x),hx⟩

def componentsEquiv (α : Type*) (B : κ → ι → ℤ) :
    ConnectedComponents ((α → ℝ) × Negative B) ≃ Labels B := by
  apply DiscreteFiberComponents.componentsEquiv (label α B)
    ((label_continuous B).comp continuous_snd) _ (label_surjective α B)
  intro ε
  letI := fiber_contractible α B ε
  infer_instance

variable {V C : Type*} [Fintype V] [Fintype C]

def stratum (B : (V ⊕ C) → V → ℤ) (I : Finset V) :=
  (I → ℝ) × Negative (fun (a : AnticliqueSubcolumns.Rows (C := C) I) (i : I) => B a.val i.val)

instance stratumTopology (B : (V ⊕ C) → V → ℤ) (I : Finset V) : TopologicalSpace (stratum B I) :=
  inferInstanceAs (TopologicalSpace
    ((I → ℝ) × Negative (fun (a : AnticliqueSubcolumns.Rows (C := C) I) (i : I) => B a.val i.val)))

def stratumComponents (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    ConnectedComponents (stratum B I) ≃ ActualSignLabels.labels B I :=
  componentsEquiv I _

theorem card_stratum_components (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (h : AnticliqueSubcolumns.AS B I) :
    Nat.card (ConnectedComponents (stratum B I))=2^(Fintype.card V+Fintype.card C-2*I.card) :=
  (Nat.card_congr (stratumComponents B I)).trans (ActualSignLabels.card_labels B I h)

#print axioms label
#print axioms fiberEquiv
#print axioms fiber_contractible
#print axioms label_surjective
#print axioms componentsEquiv
#print axioms stratum
#print axioms stratumTopology
#print axioms stratumComponents
#print axioms card_stratum_components
end Verification.RealAffineComponents
