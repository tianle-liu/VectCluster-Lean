/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Cellular Sign Convention

Reversing all cellular differentials is an actual chain isomorphism,
with degree-q multiplier (-1)^q. This accounts explicitly for the positive
cone-boundary convention rather than silently identifying opposite signs.
-/
noncomputable section
namespace Verification.CellularSignConvention
open CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category A] [Preadditive A]

def signIso (X : A) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | n+1 => -(signIso X n)

theorem signIso_natural {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    (signIso X n).hom ≫ f = f ≫ (signIso Y n).hom := by
  induction n with
  | zero => simp only [signIso,Iso.refl_hom,Category.id_comp,Category.comp_id]
  | succ n ih => simp only [signIso,Preadditive.neg_iso_hom,Preadditive.neg_comp,Preadditive.comp_neg,ih]

def negative (K : ChainComplex A ℕ) : ChainComplex A ℕ where
  X := K.X
  d i j := -K.d i j
  shape i j h := by rw [K.shape i j h,neg_zero]
  d_comp_d' i j k _ _ := by simp only [Preadditive.neg_comp,Preadditive.comp_neg,neg_neg,K.d_comp_d]

def negativeIso (K : ChainComplex A ℕ) : K ≅ negative K :=
  HomologicalComplex.Hom.isoOfComponents (fun q => signIso (K.X q) q) (by
    intro i q h
    change q+1=i at h
    subst i
    change (signIso (K.X (q+1)) (q+1)).hom ≫ (-K.d (q+1) q) =
      K.d (q+1) q ≫ (signIso (K.X q) q).hom
    simp only [signIso,Preadditive.neg_iso_hom,Preadditive.neg_comp,Preadditive.comp_neg,neg_neg]
    exact signIso_natural _ q)

#print axioms signIso
#print axioms signIso_natural
#print axioms negative
#print axioms negativeIso
end Verification.CellularSignConvention
