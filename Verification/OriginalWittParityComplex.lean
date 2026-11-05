/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittParityChange

/-!
# Original Witt Parity Complex

Entrywise parity congruence gives a chain isomorphism of the literal
integer Witt complexes, preserving their independent-set family and all
quotient-coordinate residue maps.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.OriginalWittParityComplex
open CategoryTheory Verification.OriginalWittQuotient
open Verification.OriginalWittIntegerDifferential Verification.OriginalWittIntegerComplex
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (B B' : (V ⊕ C) → V → ℤ)
variable (h : ∀ a i, (B a i : ZMod 2) = (B' a i : ZMod 2))
variable (F : Finset V → Prop) (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)
variable (indep' : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B' (Sum.inl j) i=0)

omit [Fintype V] [Fintype C] [LinearOrder V] in
def cochainsEquiv : Cochains B F ≃ₗ[ℤ] Cochains B' F :=
  LinearEquiv.piCongrRight (fun I => (OriginalWittParityChange.equiv B B' h I.val).toLinearEquiv)

omit [Fintype V] [Fintype C] [LinearOrder V] in
def degreeEquiv (p : ℕ) : degree B F p ≃ₗ[ℤ] degree B' F p where
  toFun f := ⟨cochainsEquiv B B' h F f.val,by
    intro I hI
    change OriginalWittParityChange.equiv B B' h I.val (f.val I) = 0
    rw [f.property I hI,map_zero]⟩
  invFun f := ⟨(cochainsEquiv B B' h F).symm f.val,by
    intro I hI
    change (OriginalWittParityChange.equiv B B' h I.val).symm (f.val I) = 0
    rw [f.property I hI,map_zero]⟩
  left_inv f := by apply Subtype.ext; exact (cochainsEquiv B B' h F).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (cochainsEquiv B B' h F).apply_symm_apply f.val
  map_add' f g := by
    apply Subtype.ext
    exact map_add (cochainsEquiv B B' h F) f.val g.val
  map_smul' r f := by
    apply Subtype.ext
    exact map_smul (cochainsEquiv B B' h F) r f.val

omit [Fintype V] [Fintype C] in
theorem differential (f : Cochains B F) :
    OriginalWittIntegerDifferential.differential B' F down indep' (cochainsEquiv B B' h F f) =
      cochainsEquiv B B' h F (OriginalWittIntegerDifferential.differential B F down indep f) := by
  funext J
  change (∑ i : J.val, _) = OriginalWittParityChange.equiv B B' h J.val (∑ i : J.val, _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact (OriginalWittParityChange.residue B B' h _ _ _ _ _ _ _ _).symm

omit [Fintype V] [Fintype C] in
theorem degree_differential (p : ℕ) (f : degree B F p) :
    OriginalWittIntegerComplex.differential B' F down indep' p (degreeEquiv B B' h F p f) =
      degreeEquiv B B' h F (p+1) (OriginalWittIntegerComplex.differential B F down indep p f) := by
  apply Subtype.ext
  exact differential B B' h F down indep indep' f.val

def iso : OriginalWittIntegerComplex.complex B F down indep ≅
    OriginalWittIntegerComplex.complex B' F down indep' :=
  HomologicalComplex.Hom.isoOfComponents (fun p => (degreeEquiv B B' h F p).toModuleIso) (by
    intro p q hpq
    have hq : p+1=q := hpq
    subst q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simpa only [OriginalWittIntegerComplex.complex,CochainComplex.of_d,
      ModuleCat.hom_comp,LinearMap.comp_apply,LinearEquiv.toModuleIso_hom,ModuleCat.hom_ofHom] using
      degree_differential B B' h F down indep indep' p f)

#print axioms cochainsEquiv
#print axioms degreeEquiv
#print axioms differential
#print axioms degree_differential
#print axioms iso
end Verification.OriginalWittParityComplex
