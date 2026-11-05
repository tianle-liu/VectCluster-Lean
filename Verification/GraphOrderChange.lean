/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphOrderCoordinates

/-!
# Graph Order Change

Changing the vertex order gives an explicit diagonal chain isomorphism on the
actual signed independence chains.  The diagonal units are the signs of the
actual simplex enumeration permutations; chain compatibility is proved through
the injective exterior realization and its order-independent contraction.
-/

set_option maxHeartbeats 400000

namespace Verification.GraphOrderChange

open Classical

open CategoryTheory Verification.GraphCover Verification.GraphSimplexChains
open Verification.OrientationWords Verification.EvenGraphBridge
open Verification.GraphChainMatrix Verification.GradedPerturbation

variable {R V : Type} [CommRing R] [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (T : Finset V)

/-- The actual adjacent differential is the displayed finite matrix restriction. -/
theorem complexFor_d (o : LinearOrder V) (p : ℤ) :
    (complexFor (R := R) G T o).d p (p+1)=
      ModuleCat.ofHom (matrixDegreeMap (Verification.GraphCoverGrading.degree G T)
        (matrixFor (R := R) G T o) 1 (@chainMatrix_degree R _ V _ o G T) p (p+1) rfl) := by
  have hde : (inferInstance : DecidableEq V)=o.toDecidableEq := Subsingleton.elim _ _
  cases hde
  letI := o
  exact Verification.PerturbedHomologyModel.matrixComplex_d (Verification.GraphCoverGrading.degree G T)
    (chainMatrix (R := R) G T) (chainMatrix_degree G T) (chainMatrix_square G T) p (p+1) rfl

/-- The degree component of the actual orientation isomorphism. -/
noncomputable def componentIso (o₁ o₂ : LinearOrder V) (p : ℤ) :
    (complexFor (R := R) G T o₁).X p ≅ (complexFor (R := R) G T o₂).X p := by
  change ModuleCat.of R (degreeModule (R := R) (Verification.GraphCoverGrading.degree G T) p) ≅
    ModuleCat.of R (degreeModule (R := R) (Verification.GraphCoverGrading.degree G T) p)
  exact (degreeEquiv (R := R) G T o₁ o₂ p).toModuleIso

/-- Actual chain isomorphism between the independently defined complexes for two orders. -/
noncomputable def orderIso (o₁ o₂ : LinearOrder V) : complexFor (R := R) G T o₁ ≅ complexFor G T o₂ :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := complexFor (R := R) G T o₁) (C₂ := complexFor (R := R) G T o₂)
    (componentIso (R := R) G T o₁ o₂) (by
    intro p q hpq
    have he : p+1=q := hpq
    subst q
    rw [complexFor_d, complexFor_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change (matrixFor G T o₂).mulVec (coefficientEquiv G T o₁ o₂ f.val)=
      coefficientEquiv G T o₁ o₂ ((matrixFor G T o₁).mulVec f.val)
    exact LinearMap.congr_fun (matrix_change (R := R) G T o₁ o₂) f.val)

/-- Homology is invariant under the explicit orientation change. -/
noncomputable def orderHomologyIso (o₁ o₂ : LinearOrder V) (p : ℤ) :
    (complexFor (R := R) G T o₁).homology p ≅ (complexFor G T o₂).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) p).mapIso (orderIso G T o₁ o₂)

#print axioms complexFor_d
#print axioms componentIso
#print axioms orderIso
#print axioms orderHomologyIso

end Verification.GraphOrderChange
