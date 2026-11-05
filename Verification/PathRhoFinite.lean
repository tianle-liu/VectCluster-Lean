/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoBraid
import Verification.PathRhoGrading
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Data.Fintype.Vector
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Path Rho Finite

Actual finite free modules of each word length, with restricted rho faces
and the all-vector (not only generator-wise) braid identity.
-/

namespace Verification.PathRhoFinite

open Classical Verification.PathRhoWords Verification.PathRhoBraid Verification.PathRhoGrading

variable {R : Type*} [CommRing R]

abbrev Word (n : ℕ) := {w : List Bool // w.length=n}

def wordFintype (n : ℕ) : Fintype (Word n) :=
  inferInstanceAs (Fintype (List.Vector Bool n))

def layer (n : ℕ) : Submodule R (List Bool →₀ R) :=
  Finsupp.supported R R {w | w.length=n}

noncomputable def layerEquiv (n : ℕ) : layer (R := R) n ≃ₗ[R] (Word n →₀ R) :=
  Finsupp.supportedEquivFinsupp (R := R) (M := R) {w : List Bool | w.length=n}

noncomputable def layerBasis (n : ℕ) : Basis (Word n) R (layer (R := R) n) :=
  Finsupp.basisSingleOne.map (layerEquiv n).symm

theorem layer_free (n : ℕ) : Module.Free R (layer (R := R) n) :=
  Module.Free.of_basis (layerBasis n)

theorem layer_finite (n : ℕ) : Module.Finite R (layer (R := R) n) := by
  letI := wordFintype n
  exact Module.Finite.of_basis (layerBasis n)

variable (ε ρ : R)

theorem column_mem_layer (i n : ℕ) (w : List Bool) (hw : w.length=n) :
    faceColumn ε ρ i w ∈ layer (R := R) (n-2) := by
  rcases column_length ε ρ i w with hz | ⟨c,v,hl,hf⟩
  · rw [hz]; exact (layer (n-2)).zero_mem
  · rw [hf]
    apply (layer (n-2)).smul_mem
    exact Finsupp.single_mem_supported R 1 (by change v.length=n-2; omega)

/-- The whole operator restricts to the stated finite free source and target. -/
theorem face_mem_layer (i n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    face ε ρ i x ∈ layer (R := R) (n-2) := by
  have hh : layer (R := R) n ≤ (layer (n-2)).comap (face ε ρ i) := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change face ε ρ i (Finsupp.single w 1) ∈ layer (R := R) (n-2)
    rw [face_single]
    exact column_mem_layer ε ρ i n w hw
  exact hh hx

noncomputable def layerFace (i n : ℕ) : layer (R := R) n →ₗ[R] layer (R := R) (n-2) :=
  LinearMap.codRestrict _ ((face ε ρ i).comp (layer n).subtype)
    (fun x => face_mem_layer ε ρ i n x.val x.property)

/-- The literal matrix on the original finite binary-word bases. -/
noncomputable def finiteFace (i n : ℕ) : (Word n →₀ R) →ₗ[R] (Word (n-2) →₀ R) :=
  (layerEquiv (n-2)).toLinearMap.comp ((layerFace ε ρ i n).comp (layerEquiv n).symm.toLinearMap)

/-- Universal two-face identity on every vector of the actual finite free module. -/
theorem layer_braid (hε : ε*ε=1) (hρ : ε*ρ=ρ) (i j n : ℕ)
    (hij : i+2 ≤ j) (hvalid : j+3 ≤ n) (x : layer (R := R) n) :
    face ε ρ (j-2) (face ε ρ i x.val)=ε • face ε ρ i (face ε ρ j x.val) := by
  let D := (face ε ρ (j-2)).comp (face ε ρ i)-ε • (face ε ρ i).comp (face ε ρ j)
  have hh : layer (R := R) n ≤ LinearMap.ker D := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change face ε ρ (j-2) (face ε ρ i (Finsupp.single w 1))-
      ε • face ε ρ i (face ε ρ j (Finsupp.single w 1))=0
    exact sub_eq_zero.mpr (face_braid ε ρ hε hρ i j w hij (by rw [hw]; exact hvalid))
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh x.property))

#print axioms Word
#print axioms wordFintype
#print axioms layer
#print axioms layerEquiv
#print axioms layerBasis
#print axioms layer_free
#print axioms layer_finite
#print axioms column_mem_layer
#print axioms face_mem_layer
#print axioms layerFace
#print axioms finiteFace
#print axioms layer_braid

end Verification.PathRhoFinite
