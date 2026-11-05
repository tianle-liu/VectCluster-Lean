/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictTorusSymbolInput

/-!
# Strict Positive Column Assembly

Finite columns into positive strict summands assemble into a genuine arrow, keeping the integer summand separate.
-/
noncomputable section
namespace Verification.StrictPositiveColumnAssembly
open Classical CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type*} [Category A] [Abelian A]
variable (Z₀ : A) (M : ℤ → A) (r n : ℕ) {X Y : A}
variable (e : Y ≅ ⨁ (StrictTorusSymbolInput.summand Z₀ M r n))
variable (c : ∀ (i : Verification.BinaryWordCoordinates.Index n),
  StrictTorusSymbolInput.degree r n i≠0 → (X ⟶ M (StrictTorusSymbolInput.degree r n i)))

def arrow : X ⟶ Y :=
  biproduct.lift (fun i => if h : StrictTorusSymbolInput.degree r n i=0 then 0 else
    c i h ≫ eqToHom (show M (StrictTorusSymbolInput.degree r n i)=StrictTorusSymbolInput.summand Z₀ M r n i from (if_neg h).symm)) ≫ e.inv

theorem positive (i : Verification.BinaryWordCoordinates.Index n)
    (hi : StrictTorusSymbolInput.degree r n i≠0) :
    arrow Z₀ M r n e c ≫ e.hom ≫ biproduct.π _ i ≫ eqToHom (if_neg hi)=c i hi := by
  simp only [arrow,Category.assoc,Iso.inv_hom_id_assoc,biproduct.lift_π_assoc,dif_neg hi]
  simp only [Category.assoc,eqToHom_trans,eqToHom_refl,Category.comp_id]

theorem integer (i : Verification.BinaryWordCoordinates.Index n)
    (hi : StrictTorusSymbolInput.degree r n i=0) :
    arrow Z₀ M r n e c ≫ e.hom ≫ biproduct.π _ i=0 := by
  simp only [arrow,Category.assoc,Iso.inv_hom_id_assoc,biproduct.lift_π,dif_pos hi]

#print axioms arrow
#print axioms positive
#print axioms integer
end Verification.StrictPositiveColumnAssembly
