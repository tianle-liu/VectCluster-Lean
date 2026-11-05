/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedSectionTotal

/-!
# Graded Direct Sum Split

Explicit distribution and integer reindexing of direct sums of abelian
groups. These are used to totalize the genuine Laurent sheaf splitting.
-/
noncomputable section
namespace Verification.GradedDirectSumSplit
open scoped DirectSum
variable {ι : Type*} [DecidableEq ι] (H K : ι → Type*) [∀ q,AddCommGroup (H q)] [∀ q,AddCommGroup (K q)]

def product : (⨁ q,H q × K q) ≃+ (⨁ q,H q) × (⨁ q,K q) where
  toFun a := (DFinsupp.mapRange (fun q (x : H q × K q) => x.1) (fun _ => rfl) a,
    DFinsupp.mapRange (fun q (x : H q × K q) => x.2) (fun _ => rfl) a)
  invFun a := DFinsupp.mapRange (fun _ x => (x,0)) (fun _ => rfl) a.1 +
    DFinsupp.mapRange (fun _ x => (0,x)) (fun _ => rfl) a.2
  left_inv a := by
    apply DFinsupp.ext
    intro q
    apply Prod.ext
    · change (a q).1+0=(a q).1
      exact add_zero _
    · change 0+(a q).2=(a q).2
      exact zero_add _
  right_inv a := by
    apply Prod.ext <;> apply DFinsupp.ext <;> intro q
    · change a.1 q+0=a.1 q
      exact add_zero _
    · change 0+a.2 q=a.2 q
      exact zero_add _
  map_add' a b := by ext q <;> simp [DirectSum.add_apply,DFinsupp.add_apply,DFinsupp.mapRange_apply]

theorem product_of (q : ι) (a : H q) (b : K q) :
    product H K (DirectSum.of (fun q=>H q×K q) q (a,b))=
      (DirectSum.of H q a,DirectSum.of K q b) := by
  classical
  apply Prod.ext <;> apply DFinsupp.ext <;> intro r
  · change DFinsupp.mapRange (fun q (x : H q × K q) => x.1) (fun _ => rfl) (DFinsupp.single q (a,b)) r=DFinsupp.single q a r
    rw [DFinsupp.mapRange_single]
  · change DFinsupp.mapRange (fun q (x : H q × K q) => x.2) (fun _ => rfl) (DFinsupp.single q (a,b)) r=DFinsupp.single q b r
    rw [DFinsupp.mapRange_single]

theorem congr_of (E : ∀ q,H q ≃+ K q) (q : ι) (a : H q) :
    DFinsupp.mapRange.addEquiv E (DirectSum.of H q a)=DirectSum.of K q (E q a) :=
  DFinsupp.mapRange_single (hf := fun i=>map_zero (E i))

variable (G : ℤ → Type*) [∀ q,AddCommGroup (G q)]

def degreeCast (q q' : ℤ) (h : q=q') : G q ≃+ G q' := by subst q'; exact AddEquiv.refl _

def shift : (⨁ q,G (q-1)) ≃+ ⨁ q,G q :=
  (DirectSum.equivCongrLeft (Equiv.addRight (-1 : ℤ))).trans
    (DFinsupp.mapRange.addEquiv (fun q => degreeCast G _ q (by simp)))

theorem shifted_of (q k : ℤ) (h : k=q) (a : G (q-1)) :
    degreeCast G (k-1) (q-1) (congrArg (fun t : ℤ => t-1) h)
      (DirectSum.of (fun q=>G (q-1)) q a k)=a := by
  subst k
  rw [DirectSum.of_eq_same]
  rfl

theorem shift_of (q : ℤ) (a : G (q-1)) :
    shift G (DirectSum.of (fun q=>G (q-1)) q a)=DirectSum.of G (q-1) a := by
  classical
  apply DFinsupp.ext
  intro r
  change degreeCast G (r+1-1) r (by omega)
    (DirectSum.of (fun q=>G (q-1)) q a (r+1)) = DirectSum.of G (q-1) a r
  by_cases h : r=q-1
  · subst r
    exact (shifted_of G q (q-1+1) (by omega) a).trans (DirectSum.of_eq_same (q-1) a).symm
  · have hr : r+1≠q := by omega
    rw [DirectSum.of_eq_of_ne (β := fun q=>G (q-1)) q (r+1) a hr.symm,map_zero,
      DirectSum.of_eq_of_ne (β := G) (q-1) r a (Ne.symm h)]

#print axioms product
#print axioms product_of
#print axioms congr_of
#print axioms degreeCast
#print axioms shift
#print axioms shifted_of
#print axioms shift_of
end Verification.GradedDirectSumSplit
