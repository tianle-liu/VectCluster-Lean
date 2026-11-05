/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerMatrixRank
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Integer Short Complex Rank

Rank balance for actual integer homology and its finite matrix
transpose. No freeness or torsion-free hypothesis on homology is needed.
-/
noncomputable section
namespace Verification.IntegerShortComplexRank
open CategoryTheory
open scoped Classical
attribute [local instance 2000] ModuleCat.isModule
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem range_kernel {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] [Module.Finite R X] (f : X →ₗ[R] Y) :
    Module.finrank R (LinearMap.range f)+Module.finrank R (LinearMap.ker f)=Module.finrank R X := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact (LinearMap.ker f).finrank_quotient_add_finrank

theorem balance (S : ShortComplex (ModuleCat.{0} R))
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] :
    Module.finrank R S.homology+Module.finrank R (LinearMap.range S.f.hom)+
      Module.finrank R (LinearMap.range S.g.hom)=Module.finrank R S.X₂ := by
  have hh := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have he := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank R S.homology=
    Module.finrank R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at he
  rw [← he] at hh
  have hf := range_kernel S.f.hom
  have hg := range_kernel S.g.hom
  have hc := range_kernel S.moduleCatToCycles
  have hk : LinearMap.ker S.moduleCatToCycles=LinearMap.ker S.f.hom := by
    ext x
    change (S.moduleCatToCycles x=0) ↔ (S.f.hom x=0)
    exact Subtype.ext_iff
  rw [hk] at hc
  omega

variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]

def matrix (a : Matrix κ ι R) (b : Matrix τ κ R) (h : b*a=0) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom (Matrix.toLin' a)) (ModuleCat.ofHom (Matrix.toLin' b)) (by
    apply ModuleCat.hom_ext
    change (Matrix.toLin' b).comp (Matrix.toLin' a)=0
    rw [← Matrix.toLin'_mul,h,map_zero])

omit [Fintype τ] in
theorem matrix_balance (a : Matrix κ ι R) (b : Matrix τ κ R) (h : b*a=0) :
    Module.finrank R (matrix a b h).homology+a.rank+b.rank=Fintype.card κ := by
  letI : Module.Finite R (matrix a b h).X₁ := inferInstanceAs (Module.Finite R (ι → R))
  letI : Module.Finite R (matrix a b h).X₂ := inferInstanceAs (Module.Finite R (κ → R))
  simpa only [matrix,Module.finrank_pi,Module.finrank_self,mul_one] using balance (matrix a b h)

theorem transpose (a : Matrix κ ι ℤ) (b : Matrix τ κ ℤ) (h : b*a=0) :
    Module.finrank ℤ (matrix a b h).homology=
      Module.finrank ℤ (matrix b.transpose a.transpose
        (by rw [← Matrix.transpose_mul,h,Matrix.transpose_zero])).homology := by
  have h₁ := matrix_balance a b h
  have h₂ := matrix_balance b.transpose a.transpose (by rw [← Matrix.transpose_mul,h,Matrix.transpose_zero])
  rw [IntegerMatrixRank.transpose,IntegerMatrixRank.transpose] at h₂
  omega

#print axioms range_kernel
#print axioms balance
#print axioms matrix
#print axioms matrix_balance
#print axioms transpose
end Verification.IntegerShortComplexRank
