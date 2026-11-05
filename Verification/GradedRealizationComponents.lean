/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedCoefficientRealization

/-!
# Graded Realization Components

Literal entries of the realized positive-weight differential. The
successor-weight casts are exhibited, so no action on the constant is used.
-/
noncomputable section
namespace Verification.GradedRealizationComponents
open Classical CategoryTheory CategoryTheory.Limits
open Verification.GradedCoefficientRealization Verification.GradedMatrixComplex
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {w : ι → ℕ} {v : κ → ℕ} {d : ι → ℤ}
variable (K : ℕ → C) (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d)

def entry (i j : {i // 0<w i}) : K (w i.val) ⟶ K (w j.val) :=
  eqToHom (congrArg K (Nat.sub_add_cancel i.property).symm) ≫
    A.act (w i.val-1) (w j.val-1)
      ⟨T.D j.val i.val,PositiveMatrixRestriction.degree w w T.D T.coefficientD j i⟩ ≫
    eqToHom (congrArg K (Nat.sub_add_cancel j.property))

theorem raw_component (p q : ℤ) (hpq : p+1=q)
    (i : sourceIndex w d p) (j : sourceIndex w d q) :
    biproduct.ι (fun i : sourceIndex w d p => K (w i.val.val-1+1)) i ≫
      (source K A T).d p q ≫
        biproduct.π (fun j : sourceIndex w d q => K (w j.val.val-1+1)) j=
    A.act (w i.val.val-1) (w j.val.val-1)
      ⟨T.D j.val.val i.val.val,PositiveMatrixRestriction.degree w w T.D T.coefficientD j.val i.val⟩ := by
  change _ ≫ (GradedCoefficientCategory.positiveRealization K A).map
    ((complex (PositiveGradedContraction.positiveSpace w) (fun i=>d i.val)
      (PositiveGradedContraction.differential T) (PositiveGradedContraction.differential_supported T)
      (PositiveGradedContraction.differential_square T)).d p q) ≫ _=_
  rw [complex_d_between _ _ _ _ _ p q hpq]
  exact PathGradedCoefficientAction.component _ A _ _ _ _ i j

theorem component (p q : ℤ) (hpq : p+1=q)
    (i : sourceIndex w d p) (j : sourceIndex w d q) :
    biproduct.ι (fun i : sourceIndex w d p => K (w i.val.val)) i ≫
      (sourceTermIso K A T p).inv ≫ (source K A T).d p q ≫
        (sourceTermIso K A T q).hom ≫
          biproduct.π (fun j : sourceIndex w d q => K (w j.val.val)) j=entry K A T i.val j.val := by
  simp only [sourceTermIso,id_eq,biproduct.mapIso_inv,biproduct.mapIso_hom,eqToIso,
    biproduct.ι_map_assoc,biproduct.map_π,Category.assoc]
  simpa only [entry,Category.assoc] using congrArg
    (fun f : K (w i.val.val-1+1) ⟶ K (w j.val.val-1+1) =>
      eqToHom (congrArg K (Nat.sub_add_cancel i.val.property).symm) ≫ f ≫
        eqToHom (congrArg K (Nat.sub_add_cancel j.val.property)))
    (raw_component K A T p q hpq i j)

#print axioms entry
#print axioms raw_component
#print axioms component
end Verification.GradedRealizationComponents
