/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarInitialTorus

/-!
# Scalar Initial Units

The actual initial coordinates give units of the initial Laurent
ring. Their integral powers define an explicit map from the free abelian
boundary lattice into this unit group.
-/
noncomputable section
namespace Verification.ScalarInitialUnits
open Verification.ScalarFrozenGlobal Verification.ScalarIndependentBasicOpen
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)

abbrev Torus := OriginalTorus.Torus R (IndependentChartIndex.Other n ∅ ⊕ κ)

def localizedUnit (i : Fin n) : (BasicOpen R κ n ∅ B a b)ˣ :=
  (complement_units R κ n ∅ B a b (Sum.inl ⟨i,Finset.not_mem_empty i⟩)).unit

theorem localizedUnit_val (i : Fin n) : (localizedUnit R κ n B a b i : BasicOpen R κ n ∅ B a b) =
    algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)
      (initial R κ n B a b (Sum.inl i)) :=
  (complement_units R κ n ∅ B a b (Sum.inl ⟨i,Finset.not_mem_empty i⟩)).unit_spec

def initialUnit (i : Fin n) : (Torus R κ n)ˣ :=
  Units.map (ScalarInitialTorus.initialTorusEquiv R κ n B a b).toRingHom.toMonoidHom
    (localizedUnit R κ n B a b i)

theorem initialUnit_val (i : Fin n) : (initialUnit R κ n B a b i : Torus R κ n) =
    ScalarInitialTorus.initialTorusEquiv R κ n B a b
      (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)
        (initial R κ n B a b (Sum.inl i))) := by
  change ScalarInitialTorus.initialTorusEquiv R κ n B a b (localizedUnit R κ n B a b i) = _
  rw [localizedUnit_val]

def unitSection : (Fin n →₀ ℤ) →ₗ[ℤ] Additive ((Torus R κ n)ˣ) :=
  Finsupp.linearCombination ℤ (fun i => Additive.ofMul (initialUnit R κ n B a b i))

theorem unitSection_single (i : Fin n) : unitSection R κ n B a b (Finsupp.single i 1) =
    Additive.ofMul (initialUnit R κ n B a b i) := by
  rw [unitSection,Finsupp.linearCombination_single,one_smul]

theorem section_of_generator_images
    (d : Additive ((Torus R κ n)ˣ) →+ (Fin n →₀ ℤ))
    (hd : ∀ i, d (Additive.ofMul (initialUnit R κ n B a b i)) = Finsupp.single i 1) :
    ∀ z, d (unitSection R κ n B a b z) = z := by
  have he : d.toIntLinearMap.comp (unitSection R κ n B a b) = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    change d (unitSection R κ n B a b (Finsupp.single i 1)) = Finsupp.single i 1
    rw [unitSection_single,hd]
  exact fun z => LinearMap.congr_fun he z

#print axioms Torus
#print axioms localizedUnit
#print axioms localizedUnit_val
#print axioms initialUnit
#print axioms initialUnit_val
#print axioms unitSection
#print axioms unitSection_single
#print axioms section_of_generator_images
end Verification.ScalarInitialUnits
