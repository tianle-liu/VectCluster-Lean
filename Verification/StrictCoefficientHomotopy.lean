/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientCochains
import Verification.CoefficientHomSingle

/-!
# Strict Coefficient Homotopy

The actual Nat-indexed coefficient cohomology in positive degree is
the homology of the contravariant integer-indexed Hom complex. Consequently
an actual contraction to degree zero annihilates every positive coefficient.
-/
noncomputable section
namespace Verification.StrictCoefficientHomotopy
open CategoryTheory CategoryTheory.Limits
open Verification.StrictCoefficientCochains
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable (P : CochainComplex A ℤ) (M : A)

theorem differential_between (p q : ℕ) (hpq : p+1=q) (f : (complex P M).X p) :
    (complex P M).d p q f=P.d (-(q:ℤ)) (-(p:ℤ)) ≫ f := by
  subst q
  exact differential_apply P M p f

def shortIso (p : ℕ) (hp : 0<p) :
    (complex P M).sc' (p-1) p (p+1) ≅
    (HomotopyContravariant.homComplex M P).sc' (-((p-1:ℕ):ℤ)) (-(p:ℤ)) (-((p+1:ℕ):ℤ)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      apply AddCommGrp.hom_ext
      apply AddMonoidHom.ext
      intro f
      simpa only [Category.comp_id,Category.id_comp] using
        (differential_between P M (p-1) p (by omega) f).symm)
    (by
      apply AddCommGrp.hom_ext
      apply AddMonoidHom.ext
      intro f
      simpa only [Category.comp_id,Category.id_comp] using
        (differential_between P M p (p+1) rfl f).symm)

def homologyIso (p : ℕ) (hp : 0<p) :
    (complex P M).homology p ≅ (HomotopyContravariant.homComplex M P).homology (-(p:ℤ)) :=
  (complex P M).homologyIsoSc' (p-1) p (p+1)
    ((ComplexShape.up ℕ).prev_eq' (by change p-1+1=p;omega))
    ((ComplexShape.up ℕ).next_eq' rfl) ≪≫
      ShortComplex.homologyMapIso (shortIso P M p hp) ≪≫
      ((HomotopyContravariant.homComplex M P).homologyIsoSc' (-((p-1:ℕ):ℤ)) (-(p:ℤ)) (-((p+1:ℕ):ℤ))
        ((ComplexShape.up ℤ).symm.prev_eq' (by change -(p:ℤ)+1= -((p-1:ℕ):ℤ);omega))
        ((ComplexShape.up ℤ).symm.next_eq' (by change -((p+1:ℕ):ℤ)+1= -(p:ℤ);omega))).symm

variable [HasZeroObject A] {Q : A}
theorem vanishes (e : HomotopyEquiv P ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Q))
    (p : ℕ) (hp : 0<p) : IsZero ((complex P M).homology p) :=
  IsZero.of_iso (CoefficientHomSingle.homology_vanishes M e (-(p:ℤ)) (by omega))
    (homologyIso P M p hp)

#print axioms differential_between
#print axioms shortIso
#print axioms homologyIso
#print axioms vanishes
end Verification.StrictCoefficientHomotopy
