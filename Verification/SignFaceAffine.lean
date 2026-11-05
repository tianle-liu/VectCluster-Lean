/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignFaceRows
import Verification.ActualSignatureLattice

/-!
# Sign Face Affine

The actual two sign extensions are affine in the actual label
coordinates; the new normal bit is an independent input coordinate.
-/
noncomputable section
namespace Verification.SignFaceAffine
open Verification.AnticliqueSubcolumns Verification.ActualSignatureLattice
open Verification.AffineSignCoordinates Verification.SignatureLabelLattice
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V]

def labelExtension (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (ε : ActualSignLabels.labels B (insert j I)) (b : ZMod 2) : ActualSignLabels.labels B I :=
  ⟨SignFaceRows.extend I j hj (ε.val,b),by
    intro i
    rw [SignFaceRows.character_extension,hB i,Int.cast_zero,zero_mul,zero_add]
    exact ε.property ⟨i.val,Finset.mem_insert_of_mem i.property⟩⟩

def tail (α : Type*) : (Option α → ZMod 2) →ₗ[ZMod 2] (α → ZMod 2) where
  toFun x a := x (some a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pair {X Y Z : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup Z] [Module (ZMod 2) Z]
    (f : X →ᵃ[ZMod 2] Y) (g : X →ᵃ[ZMod 2] Z) : X →ᵃ[ZMod 2] (Y × Z) where
  toFun x := (f x,g x)
  linear := f.linear.prod g.linear
  map_vadd' p v := Prod.ext (f.map_vadd p v) (g.map_vadd p v)

def input (B : (V ⊕ C) → V → ℤ) (J : Finset V) (p : ActualSignLabels.labels B J) :
    (Option (Index (reduced B J)) → ZMod 2) →ᵃ[ZMod 2] ((Rows (C := C) J → ZMod 2) × ZMod 2) :=
  pair ((encode (reduced B J) (fun _ => 1) p).comp (tail _).toAffineMap)
    (LinearMap.proj none).toAffineMap

def face (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I)) :
    (Option (Index (reduced B (insert j I))) → ZMod 2) →ᵃ[ZMod 2] (Index (reduced B I) → ZMod 2) :=
  (decode (reduced B I) (fun _ => 1) p).comp
    ((SignFaceRows.extend I j hj).toAffineMap.comp (input B (insert j I) q))

theorem face_extension (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (x : Option (Index (reduced B (insert j I))) → ZMod 2) :
    (coordinates (reduced B I) (fun _ => 1) p).symm (face B I j hj p q x)=
      labelExtension B I j hj hB
        ((coordinates (reduced B (insert j I)) (fun _ => 1) q).symm (tail _ x)) (x none) := by
  apply (coordinates (reduced B I) (fun _ => 1) p).injective
  rw [Equiv.apply_symm_apply,coordinates_apply]
  change decode (reduced B I) (fun _ => 1) p
      (SignFaceRows.extend I j hj (encode (reduced B (insert j I)) (fun _ => 1) q (tail _ x),x none))=
    decode (reduced B I) (fun _ => 1) p
      (SignFaceRows.extend I j hj (((coordinates (reduced B (insert j I)) (fun _ => 1) q).symm (tail _ x)).val,x none))
  rw [coordinates_symm_apply]

#print axioms labelExtension
#print axioms tail
#print axioms pair
#print axioms input
#print axioms face
#print axioms face_extension
end Verification.SignFaceAffine
