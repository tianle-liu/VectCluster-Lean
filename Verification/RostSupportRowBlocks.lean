/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostSupportInput

/-!
# Rost Support Row Blocks

Canonical blocks of the ordinary Rost support-row differential.
They retain the actual row map and its supplied first-page coordinates.
Finite reconstruction and transport are proved here; no divisor formula,
coordinate multiplicity, or component-pullback formula is postulated.
-/
noncomputable section
namespace Verification.RostSupportRowBlocks
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open Classical
variable (T : RostAffineInput.Theory)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (s : ℤ)
variable (D : RostSupportInput.Data T A V x Allowed s)

abbrev Term (p : ℕ) (I : PrimeLayerCover.Index Allowed p) :=
  (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x I.val)))
    (s-p)).homology 0

/-- The actual row differential expressed in its stratum coordinates. -/
def differential (p : ℕ) : RostSupportInput.Layer T A V x Allowed s p 0 ⟶
    RostSupportInput.Layer T A V x Allowed s (p+1) 0 :=
  (D.rowTerm p).inv ≫ D.row.d p (p+1) ≫ (D.rowTerm (p+1)).hom

/-- Inclusion of one stratum into the finite row. -/
def inclusion (p : ℕ) (I : PrimeLayerCover.Index Allowed p) :
    Term T A V x Allowed s p I ⟶ RostSupportInput.Layer T A V x Allowed s p 0 := by
  classical
  exact AddCommGrp.ofHom (AddMonoidHom.single
    (fun J : PrimeLayerCover.Index Allowed p => Term T A V x Allowed s p J) I)

/-- Projection to one target stratum. -/
def projection (p : ℕ) (I : PrimeLayerCover.Index Allowed p) :
    RostSupportInput.Layer T A V x Allowed s p 0 ⟶ Term T A V x Allowed s p I :=
  AddCommGrp.ofHom (Pi.evalAddMonoidHom _ I)

def block (p : ℕ) (I : PrimeLayerCover.Index Allowed p)
    (J : PrimeLayerCover.Index Allowed (p+1)) :
    Term T A V x Allowed s p I ⟶ Term T A V x Allowed s (p+1) J :=
  inclusion T A V x Allowed s p I ≫ differential T A V x Allowed s D p ≫
    projection T A V x Allowed s (p+1) J

theorem row_square (p : ℕ) :
    D.row.d p (p+1) ≫ (D.rowTerm (p+1)).hom =
      (D.rowTerm p).hom ≫ differential T A V x Allowed s D p := by
  simp only [differential,Iso.hom_inv_id_assoc]

theorem differential_apply (p : ℕ)
    (a : RostSupportInput.Layer T A V x Allowed s p 0)
    (J : PrimeLayerCover.Index Allowed (p+1)) :
    differential T A V x Allowed s D p a J =
      ∑ I,block T A V x Allowed s D p I J (a I) := by
  classical
  have ha : a = ∑ I,Pi.single I (a I) := by
    apply funext
    intro I
    simp
  conv_lhs => rw [ha]
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

/-- A boundary formula on every ordinary stratum block determines the
whole row differential, without introducing a global comparison input. -/
theorem differential_ext (p : ℕ)
    (f : RostSupportInput.Layer T A V x Allowed s p 0 ⟶
      RostSupportInput.Layer T A V x Allowed s (p+1) 0)
    (hf : ∀ I J,inclusion T A V x Allowed s p I ≫ f ≫
      projection T A V x Allowed s (p+1) J = block T A V x Allowed s D p I J) :
    f = differential T A V x Allowed s D p := by
  classical
  apply ConcreteCategory.hom_ext
  intro a
  funext J
  change f a J = differential T A V x Allowed s D p a J
  rw [differential_apply]
  have ha : a = ∑ I,Pi.single I (a I) := by
    apply funext
    intro I
    simp
  conv_lhs => rw [ha]
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro I _
  exact congrArg (fun g => g (a I)) (hf I J)

#print axioms Term
#print axioms differential
#print axioms inclusion
#print axioms projection
#print axioms block
#print axioms row_square
#print axioms differential_apply
#print axioms differential_ext
end Verification.RostSupportRowBlocks
