/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Data.Finsupp.Fintype

/-!
# Torus Zero

The actual rank-zero split-torus coordinate algebra is the base ring.
-/
noncomputable section
namespace Verification.TorusZero
open CategoryTheory AlgebraicGeometry
variable (R : Type) [CommRing R]

def algebraEquiv : R ≃ₐ[R] MonoidAlgebra R (Multiplicative (Fin 0 →₀ ℤ)) := by
  apply AlgEquiv.ofBijective (MonoidAlgebra.singleOneAlgHom : R →ₐ[R] MonoidAlgebra R (Multiplicative (Fin 0 →₀ ℤ)))
  constructor
  · intro a b h
    change Finsupp.single 1 a=Finsupp.single 1 b at h
    exact Finsupp.single_injective 1 h
  · intro f
    refine ⟨f 1,?_⟩
    ext g
    have hg : g=1 := Subsingleton.elim _ _
    subst g
    simp [MonoidAlgebra.singleOneAlgHom]

def schemeIso : Spec (CommRingCat.of (MonoidAlgebra R (Multiplicative (Fin 0 →₀ ℤ)))) ≅
    Spec (CommRingCat.of R) :=
  Scheme.Spec.mapIso (algebraEquiv R).toRingEquiv.toCommRingCatIso.op

#print axioms algebraEquiv
#print axioms schemeIso
end Verification.TorusZero
