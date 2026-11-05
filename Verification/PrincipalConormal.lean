/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConormalFrame
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Regular.SMul

/-!
# Principal Conormal

A regular principal equation has its own residue class as a basis of
its actual conormal module. No smoothness or conormal freeness is assumed.
-/
noncomputable section
universe u
namespace Verification.PrincipalConormal
variable {A : Type u} [CommRing A] (x : A)

def ideal : Ideal A := Ideal.span {x}
def coordinate : (ideal x).Cotangent :=
  (ideal x).toCotangent ⟨x,Ideal.subset_span (Set.mem_singleton x)⟩

theorem smul_coordinate_eq_zero_iff (hx : IsSMulRegular A x) (r : A ⧸ ideal x) :
    r • coordinate x = 0 ↔ r = 0 := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective r
  constructor
  · intro hh
    change a • (ideal x).toCotangent ⟨x,_⟩ = 0 at hh
    rw [← map_smul,Ideal.toCotangent_eq_zero] at hh
    change a * x ∈ Ideal.span {x} ^ 2 at hh
    rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton] at hh
    obtain ⟨b,hb⟩ := hh
    have ha : a = x * b := hx (by
      change x * a = x * (x * b)
      simpa only [pow_two,mul_assoc,mul_comm a x] using hb)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [ideal,Ideal.mem_span_singleton]
    exact ⟨b,ha⟩
  · intro hh
    rw [hh,zero_smul]

theorem independent (hx : IsSMulRegular A x) :
    LinearIndependent (A ⧸ ideal x) (fun _ : PUnit.{u+1} => coordinate x) := by
  rw [linearIndependent_iff]
  intro l hl
  rw [Finsupp.linearCombination_unique] at hl
  have hz := (smul_coordinate_eq_zero_iff x hx (l default)).mp hl
  exact Finsupp.unique_ext hz

theorem spanning : Submodule.span (A ⧸ ideal x) (Set.range (fun _ : PUnit.{u+1} => coordinate x)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨⟨a,ha⟩,rfl⟩ := (ideal x).toCotangent_surjective z
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact Submodule.subset_span ⟨PUnit.unit,rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b ha hb ia ib => exact Submodule.add_mem _ ia ib
  | smul r a ha ia => exact Submodule.smul_mem _ (Ideal.Quotient.mk (ideal x) r) ia

def basis (hx : IsSMulRegular A x) : Basis PUnit.{u+1} (A ⧸ ideal x) (ideal x).Cotangent :=
  Basis.mk (independent x hx) (by rw [spanning])

theorem basis_apply (hx : IsSMulRegular A x) (i : PUnit.{u+1}) : basis x hx i = coordinate x :=
  Basis.mk_apply _ _ _

#print axioms ideal
#print axioms coordinate
#print axioms smul_coordinate_eq_zero_iff
#print axioms independent
#print axioms spanning
#print axioms basis
#print axioms basis_apply
end Verification.PrincipalConormal
