/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithComplexCoordinates
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Smith Complex

A simultaneous Smith chain isomorphism, constructed for any degreewise
finite free complex over a PID. The displayed normal differential is defined
independently by disjoint nonzero scalar pairs; unmatched cycle coordinates
are isolated one-term summands. No boundedness or TF homology is required.
-/

noncomputable section
namespace Verification.SmithComplex
open CategoryTheory CategoryTheory.Limits
open Verification.SmithComplexCoordinates

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

/-- The complex of the independently specified scalar Smith pairs. -/
def normalComplex : CochainComplex (ModuleCat.{0} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (NormalModule C n))
    (fun n => ModuleCat.ofHom (normalDifferential C n)) (by
      intro n
      exact congrArg (fun f : NormalModule C n →ₗ[R] NormalModule C (n+1+1) =>
        ModuleCat.ofHom f) (normalDifferential_square C n))

theorem normalComplex_d (n : ℤ) :
    (normalComplex C).d n (n+1) = ModuleCat.ofHom (normalDifferential C n) :=
  CochainComplex.of_d _ _ _ _

def componentIso (n : ℤ) : C.X n ≅ (normalComplex C).X n :=
  (coordinates C n).toModuleIso

/-- The full complex is actually isomorphic to its scalar-block normal form. -/
def smithIso : C ≅ normalComplex C :=
  HomologicalComplex.Hom.isoOfComponents (C₁ := C) (C₂ := normalComplex C)
    (componentIso C) (by
      intro n m hnm
      have hm : n+1=m := hnm
      subst m
      rw [normalComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (coordinates_differential C n x).symm)

/-- The construction preserves every vanishing degree, hence any bounded support. -/
theorem normalComplex_isZero (n : ℤ) (h : IsZero (C.X n)) :
    IsZero ((normalComplex C).X n) := h.of_iso (componentIso C n).symm

/-- Categorical homology transport along the actual simultaneous Smith isomorphism. -/
def homologyIso (n : ℤ) : C.homology n ≅ (normalComplex C).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) n).mapIso (smithIso C)

#print axioms normalComplex
#print axioms normalComplex_d
#print axioms componentIso
#print axioms smithIso
#print axioms normalComplex_isZero
#print axioms homologyIso

end Verification.SmithComplex
