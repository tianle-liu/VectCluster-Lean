/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.Abel

/-!
# Koszul Cone

The exactness induction for adjoining one equation to a Koszul
resolution. Both cone maps are the literal signed block maps. The only
extra condition at degree one is injectivity of the new equation on the
previous quotient, exactly the regular-sequence condition.
-/
noncomputable section
namespace Verification.KoszulCone
variable {R A B C D M : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]

def block (f : A →ₗ[R] B) (g : B →ₗ[R] C) (x : R) : (A × B) →ₗ[R] (B × C) where
  toFun z := (f z.1+x • z.2, -g z.2)
  map_add' z w := by apply Prod.ext <;> simp [map_add,smul_add] <;> abel
  map_smul' r z := by simp [map_smul,smul_add,smul_neg,smul_smul,mul_comm]

def first (f : A →ₗ[R] B) (x : R) : (A × B) →ₗ[R] B where
  toFun z := f z.1+x • z.2
  map_add' z w := by simp [map_add,smul_add]; abel
  map_smul' r z := by simp [map_smul,smul_add,smul_smul,mul_comm]

theorem block_squared (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D) (x : R)
    (hgf : g.comp f=0) (hhg : h.comp g=0) :
    (block g h x).comp (block f g x)=0 := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change g (f z.1+x • z.2)+x • -g z.2=0
    have hzero : g (f z.1)=0 := LinearMap.congr_fun hgf z.1
    simp only [map_add,map_smul,hzero,smul_neg,zero_add,add_neg_cancel]
  · change -h (-g z.2)=0
    rw [map_neg,neg_neg]
    exact LinearMap.congr_fun hhg z.2

theorem first_squared (f : A →ₗ[R] B) (g : B →ₗ[R] C) (x : R)
    (hgf : g.comp f=0) : (first g x).comp (block f g x)=0 := by
  apply LinearMap.ext
  intro z
  change g (f z.1+x • z.2)+x • -g z.2=0
  have hzero : g (f z.1)=0 := LinearMap.congr_fun hgf z.1
  simp only [map_add,map_smul,hzero,smul_neg,zero_add,add_neg_cancel]

theorem block_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : C →ₗ[R] D) (x : R)
    (hfg : LinearMap.range f=LinearMap.ker g)
    (hgh : LinearMap.range g=LinearMap.ker h) :
    LinearMap.range (block f g x)=LinearMap.ker (block g h x) := by
  have hgf : g.comp f=0 := LinearMap.range_le_ker_iff.mp hfg.le
  have hhg : h.comp g=0 := LinearMap.range_le_ker_iff.mp hgh.le
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (block_squared f g h x hgf hhg)
  · rintro ⟨b,c⟩ hz
    have he : g b+x • c=0 ∧ h c=0 := by
      simpa [LinearMap.mem_ker,block,Prod.ext_iff] using hz
    obtain ⟨a,ha⟩ := hgh.symm ▸ (show c ∈ LinearMap.ker h from he.2)
    have hz' : b+x • a ∈ LinearMap.ker g := by
      change g (b+x • a)=0
      rw [map_add,map_smul,ha]
      exact he.1
    obtain ⟨z,hz⟩ := hfg.symm ▸ hz'
    refine ⟨(z,-a),?_⟩
    apply Prod.ext
    · change f z+x • -a=b
      rw [hz,smul_neg,add_neg_cancel_right]
    · change -g (-a)=c
      rw [map_neg,neg_neg,ha]

theorem first_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) (e : C →ₗ[R] M) (x : R)
    (hfg : LinearMap.range f=LinearMap.ker g)
    (hge : LinearMap.range g=LinearMap.ker e) (hx : IsSMulRegular M x) :
    LinearMap.range (block f g x)=LinearMap.ker (first g x) := by
  have hgf : g.comp f=0 := LinearMap.range_le_ker_iff.mp hfg.le
  have heg : e.comp g=0 := LinearMap.range_le_ker_iff.mp hge.le
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (first_squared f g x hgf)
  · rintro ⟨b,c⟩ hz
    have he : g b+x • c=0 := hz
    have hec : e c=0 := by
      have hh := congrArg e he
      have hzero : e (g b)=0 := LinearMap.congr_fun heg b
      rw [map_add,map_smul,hzero,map_zero,zero_add] at hh
      exact hx (by simpa using hh)
    obtain ⟨a,ha⟩ := hge.symm ▸ (show c ∈ LinearMap.ker e from hec)
    have hz' : b+x • a ∈ LinearMap.ker g := by
      change g (b+x • a)=0
      rw [map_add,map_smul,ha]
      exact he
    obtain ⟨z,hz⟩ := hfg.symm ▸ hz'
    refine ⟨(z,-a),?_⟩
    apply Prod.ext
    · change f z+x • -a=b
      rw [hz,smul_neg,add_neg_cancel_right]
    · change -g (-a)=c
      rw [map_neg,neg_neg,ha]

#print axioms block
#print axioms first
#print axioms block_squared
#print axioms first_squared
#print axioms block_exact
#print axioms first_exact
end Verification.KoszulCone
