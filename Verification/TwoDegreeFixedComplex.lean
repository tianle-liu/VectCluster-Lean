/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TerminalHomology
import Verification.PerturbedHomologyModel
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Two Degree Fixed Complex

The actual residual fixed-module complex concentrated in degrees -1 and
zero: its zeroth homology is a literal cokernel, and an injective first map
annihilates every other homology group.
-/

namespace Verification.TwoDegreeFixedComplex

open Classical CategoryTheory CategoryTheory.Limits Verification.GradedPerturbation
  Verification.PerturbedHomologyModel

variable {R ι : Type} [CommRing R] [Fintype ι]
variable (d : ι → ℤ) (P S : Matrix ι ι R)
variable (hd : Homogeneous d 1 S) (hPS : P*S=S) (hSS : S*S=0)
variable (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)

include hP in
theorem component_zero (p : ℤ) (hp : p ≠ -1) (hp0 : p ≠ 0)
    (x : fixedModule d P p) : x=0 := by
  apply Subtype.ext
  funext i
  by_cases hi : d i=p
  · have hh := congrFun x.property.2 i
    change (∑ j,P i j*x.val j)=x.val i at hh
    have hz : (∑ j,P i j*x.val j)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hP i j (by omega) (by omega),zero_mul]
    exact hh.symm.trans hz
  · exact x.property.1 i hi

noncomputable def firstMap : fixedModule d P (-1) →ₗ[R] fixedModule d P 0 :=
  fixedDifferential d P S hd hPS (-1)

theorem first_d : (fixedComplex d P S hd hPS hSS).d (-1) 0=ModuleCat.ofHom (firstMap d P S hd hPS) :=
  CochainComplex.of_d _ _ _ (-1)

include hP in
theorem outgoing_zero : (fixedComplex d P S hd hPS hSS).d 0 1=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact component_zero d P hP 1 (by omega) (by omega) _

noncomputable def homologyZeroIso :
    (fixedComplex d P S hd hPS hSS).homology 0 ≅
      ModuleCat.of R (fixedModule d P 0 ⧸ LinearMap.range (firstMap d P S hd hPS)) := by
  let K := fixedComplex d P S hd hPS hSS
  let E := Verification.TerminalHomology.homologyIso (K.sc' (-1) 0 1) (outgoing_zero d P S hd hPS hSS hP)
  have hf : (K.sc' (-1) 0 1).f.hom=firstMap d P S hd hPS := by
    change (K.d (-1) 0).hom=_
    rw [first_d]
    rfl
  exact K.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫ E ≪≫
    (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range hf)).toModuleIso

include hP in
theorem homology_zero (hinj : Function.Injective (firstMap d P S hd hPS)) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((fixedComplex d P S hd hPS hSS).homology p) := by
  let K := fixedComplex d P S hd hPS hSS
  by_cases he : p = -1
  · subst p
    have he : (K.sc' (-2) (-1) 0).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      have hx0 : x=0 := hinj (by
        have ht : (K.d (-1) 0).hom=firstMap d P S hd hPS := by rw [first_d]; rfl
        change (K.d (-1) 0) x=0 at hx
        simpa only [← ht,map_zero] using hx)
      exact ⟨0,by rw [map_zero,hx0]⟩
    have hz := (ShortComplex.exact_iff_isZero_homology _).mp he
    exact (K.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp)).isZero_iff.mpr hz
  · letI : Subsingleton (fixedModule d P p) := ⟨fun x y =>
      (component_zero d P hP p he hp x).trans (component_zero d P hP p he hp y).symm⟩
    apply HomologicalComplex.ExactAt.isZero_homology
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (ModuleCat.of R (fixedModule d P p))
    exact ModuleCat.isZero_of_subsingleton _

#print axioms component_zero
#print axioms firstMap
#print axioms first_d
#print axioms outgoing_zero
#print axioms homologyZeroIso
#print axioms homology_zero

end Verification.TwoDegreeFixedComplex
