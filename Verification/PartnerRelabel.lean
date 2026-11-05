/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumPresentation
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Partner Relabel

Reindex the exchange partners in the literal presentation while leaving
the entire original-coordinate coefficient ring fixed.
-/
noncomputable section
namespace Verification.PartnerRelabel
open MvPolynomial Verification.StratumPresentation
variable {R α β γ δ : Type*} [CommRing R]
variable (e : (α ⊕ β) ≃ (γ ⊕ δ)) (x g : (α ⊕ β) → R)

theorem rename_relation (i : α ⊕ β) :
    rename e (exchangeRelation x g i) =
      exchangeRelation (fun j => x (e.symm j)) (fun j => g (e.symm j)) (e i) := by
  simp only [exchangeRelation, map_sub, map_mul, rename_C, rename_X, Equiv.symm_apply_apply]

theorem map_ideal :
    (exchangeIdeal x g).map (renameEquiv R e).toRingHom =
      exchangeIdeal (fun j => x (e.symm j)) (fun j => g (e.symm j)) := by
  rw [exchangeIdeal, Ideal.map_span, exchangeIdeal]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨e i, (rename_relation e x g i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨exchangeRelation x g (e.symm i), Set.mem_range_self _, ?_⟩
    simpa only [Equiv.apply_symm_apply] using rename_relation e x g (e.symm i)

def quotientEquiv : (MvPolynomial (α ⊕ β) R ⧸ exchangeIdeal x g) ≃ₐ[R]
    (MvPolynomial (γ ⊕ δ) R ⧸
      exchangeIdeal (fun j => x (e.symm j)) (fun j => g (e.symm j))) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv R e) (map_ideal e x g).symm

theorem quotientEquiv_variable (i : α ⊕ β) :
    quotientEquiv e x g (Ideal.Quotient.mk (exchangeIdeal x g) (X i)) =
      Ideal.Quotient.mk (exchangeIdeal (fun j => x (e.symm j)) (fun j => g (e.symm j)))
        (X (e i)) := by
  change Ideal.Quotient.mk _ (rename e (X i)) = _
  rw [rename_X]

#print axioms rename_relation
#print axioms map_ideal
#print axioms quotientEquiv
#print axioms quotientEquiv_variable
end Verification.PartnerRelabel
