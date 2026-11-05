/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentScalarModel

/-!
# Trivial Group Algebra

The group algebra of a trivial additive group is the ground algebra.
-/
noncomputable section
namespace Verification.TrivialGroupAlgebra
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Subsingleton M]
abbrev Ring := MonoidAlgebra R (Multiplicative M)
def forward : Ring R M →ₐ[R] R := MonoidAlgebra.lift R (Multiplicative M) R 1

theorem left : (Algebra.ofId R (Ring R M)).comp (forward R M)=AlgHom.id R _ := by
  apply MonoidAlgebra.algHom_ext
  intro m
  have hm : m=1 := Subsingleton.elim _ _
  subst m
  change ((Algebra.ofId R (Ring R M)).comp (forward R M)) 1=(1:Ring R M)
  rw [map_one]

omit [Subsingleton M] in
theorem right : (forward R M).comp (Algebra.ofId R (Ring R M))=AlgHom.id R _ := by
  apply AlgHom.ext
  intro r
  exact (forward R M).commutes r

def equiv : Ring R M ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (forward R M) (Algebra.ofId R _) (right R M) (left R M)

#print axioms Ring
#print axioms forward
#print axioms left
#print axioms right
#print axioms equiv
end Verification.TrivialGroupAlgebra
