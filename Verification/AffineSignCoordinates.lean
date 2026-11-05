/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AffineFiberCoordinates
import Verification.MatrixSignLabels
import Verification.ActualSignLabels

/-!
# Affine Sign Coordinates

Actual affine encoders and decoders for the manuscript's F₂ labels,
including the rank derived from the primitive integral columns.
-/
noncomputable section
namespace Verification.AffineSignCoordinates
abbrev Bit := ZMod 2
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def linear (B : κ → ι → ℤ) : (κ → Bit) →ₗ[Bit] (ι → Bit) where
  toFun x i := ∑ a, (B a i:Bit)*x a
  map_add' x y := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring

def labels (B : κ → ι → ℤ) (u : ι → Bit) :=
  {x : κ → Bit // ∀ i, ∑ a, (B a i:Bit)*x a=u i}

def encode (B : κ → ι → ℤ) (u : ι → Bit) (p : labels B u) :
    (Fin (Module.finrank Bit (LinearMap.ker (linear B))) → Bit) →ᵃ[Bit] (κ → Bit) :=
  AffineFiberCoordinates.encode (linear B) p.val

def decode (B : κ → ι → ℤ) (u : ι → Bit) (p : labels B u) :
    (κ → Bit) →ᵃ[Bit] (Fin (Module.finrank Bit (LinearMap.ker (linear B))) → Bit) :=
  AffineFiberCoordinates.decode (linear B) p.val

omit [Fintype ι] in
theorem point_equation (B : κ → ι → ℤ) (u : ι → Bit) (p : labels B u) : linear B p.val=u :=
  funext p.property

def coordinates (B : κ → ι → ℤ) (u : ι → Bit) (p : labels B u) :
    labels B u ≃ (Fin (Module.finrank Bit (LinearMap.ker (linear B))) → Bit) :=
  (Equiv.subtypeEquivRight (fun x => by
    change (∀ i, linear B x i=u i) ↔ linear B x=linear B p.val
    rw [point_equation]
    exact funext_iff.symm)).trans (AffineFiberCoordinates.fiberEquiv (linear B) p.val)

omit [Fintype ι] in
theorem coordinates_apply (B : κ → ι → ℤ) (u : ι → Bit) (p x : labels B u) :
    coordinates B u p x=decode B u p x.val := rfl

omit [Fintype ι] in
theorem coordinates_symm_apply (B : κ → ι → ℤ) (u : ι → Bit) (p : labels B u)
    (x : Fin (Module.finrank Bit (LinearMap.ker (linear B))) → Bit) :
    ((coordinates B u p).symm x).val=encode B u p x := rfl

def columns (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ)) : κ → ι → ℤ :=
  fun a i => f (Finsupp.single i 1) a

theorem linear_surjective (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ))
    (hf : Function.Injective f) (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    Function.Surjective (linear (columns f)) := by
  intro u
  obtain ⟨p⟩ := MatrixSignLabels.nonempty_labels f u hf hs
  exact ⟨p.val,funext p.property⟩

theorem dimension (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ))
    (hf : Function.Injective f) (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    Module.finrank Bit (LinearMap.ker (linear (columns f)))=Fintype.card κ-Fintype.card ι := by
  have h := (linear (columns f)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (linear_surjective f hf hs),finrank_top,
    Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card] at h
  omega

variable {V C : Type*} [Fintype V] [Fintype C]

theorem actual_dimension (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (hAS : AnticliqueSubcolumns.AS B I) :
    Module.finrank Bit (LinearMap.ker (linear
      (fun (a : AnticliqueSubcolumns.Rows (C := C) I) (i : I) => B a.val i.val)))=
      Fintype.card V+Fintype.card C-2*I.card := by
  have he : columns (AnticliqueSubcolumns.selectedMap B I)=
      fun (a : AnticliqueSubcolumns.Rows (C := C) I) (i : I) => B a.val i.val := by
    funext a i
    exact ActualSignLabels.selected_single B I i a
  have h := dimension (AnticliqueSubcolumns.selectedMap B I) hAS.1 hAS.2
  rw [he,ActualSignLabels.residual_dimension] at h
  exact h

#print axioms Bit
#print axioms linear
#print axioms labels
#print axioms encode
#print axioms decode
#print axioms point_equation
#print axioms coordinates
#print axioms coordinates_apply
#print axioms coordinates_symm_apply
#print axioms columns
#print axioms linear_surjective
#print axioms dimension
#print axioms actual_dimension
end Verification.AffineSignCoordinates
