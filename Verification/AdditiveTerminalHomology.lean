/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Additive Terminal Homology

A terminal differential in an actual complex of abelian groups has
homology equal to the literal quotient by its incoming image.
-/
noncomputable section
namespace Verification.AdditiveTerminalHomology
open CategoryTheory CategoryTheory.Limits
variable (S : ShortComplex AddCommGrp) (hg : S.g=0)

def cokernelIso : S.homology ≅ cokernel S.f :=
  (ShortComplex.HomologyData.ofHasCokernel S hg).left.homologyIso

def quotientIso : S.homology ≅ AddCommGrp.of (S.X₂ ⧸ AddMonoidHom.range S.f.hom) :=
  cokernelIso S hg ≪≫ AddCommGrp.cokernelIsoQuotient S.f

def terminalIso (K : CochainComplex AddCommGrp ℕ) (p : ℕ) (hp : 0<p)
    (hd : K.d p (p+1)=0) :
    K.homology p ≅ AddCommGrp.of (K.X p ⧸ AddMonoidHom.range (K.d (p-1) p).hom) :=
  K.homologyIsoSc' (p-1) p (p+1)
    (ComplexShape.prev_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel (p-1) p by change p-1+1=p;omega))
    (ComplexShape.next_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel p (p+1) from rfl)) ≪≫
      quotientIso (K.sc' (p-1) p (p+1)) hd

#print axioms cokernelIso
#print axioms quotientIso
#print axioms terminalIso
end Verification.AdditiveTerminalHomology
