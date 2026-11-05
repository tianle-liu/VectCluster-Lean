/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Terminal Homology

A short complex with an actually zero outgoing map has categorical homology
equal to the literal cokernel of its incoming map.
-/

namespace Verification.TerminalHomology

open CategoryTheory

variable {R : Type} [CommRing R]

noncomputable def cycleProjection (S : ShortComplex (ModuleCat R)) :
    LinearMap.ker S.g.hom →ₗ[R] (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  (LinearMap.range S.f.hom).mkQ.comp (LinearMap.ker S.g.hom).subtype

theorem projection_surjective (S : ShortComplex (ModuleCat R)) (hg : S.g=0) :
    Function.Surjective (cycleProjection S) := by
  intro q
  obtain ⟨x,hx⟩ := (LinearMap.range S.f.hom).mkQ_surjective q
  refine ⟨⟨x,?_⟩,hx⟩
  change S.g x=0
  rw [hg]
  rfl

theorem projection_kernel (S : ShortComplex (ModuleCat R)) :
    LinearMap.ker (cycleProjection S)=LinearMap.range S.moduleCatToCycles := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨y,Subtype.ext hy⟩
  · rintro ⟨y,rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,rfl⟩

noncomputable def quotientEquiv (S : ShortComplex (ModuleCat R)) (hg : S.g=0) :
    S.moduleCatHomology ≃ₗ[R] (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel S).symm).trans
    ((cycleProjection S).quotKerEquivOfSurjective (projection_surjective S hg))

noncomputable def homologyIso (S : ShortComplex (ModuleCat R)) (hg : S.g=0) :
    S.homology ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.moduleCatHomologyIso ≪≫ (quotientEquiv S hg).toModuleIso

#print axioms cycleProjection
#print axioms projection_surjective
#print axioms projection_kernel
#print axioms quotientEquiv
#print axioms homologyIso

end Verification.TerminalHomology
