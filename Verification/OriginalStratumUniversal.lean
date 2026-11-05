/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalGlobalGenerators
import Verification.IndependentStratumCoordinates

/-!
# Original Stratum Universal

Universal maps from the actual localized zero strata. The only
conditions are invertibility of the actual complementary product and
vanishing of the actual selected original coordinates.
-/
noncomputable section
namespace Verification.OriginalStratumUniversal
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
open Verification.GlobalNormalFrame
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "A" => Global R κ n B
local notation "O" => BasicOpen R κ n I B
local notation "Q" => ZeroLayer R κ n I B

def baseMap : A →+* Q :=
  (Ideal.Quotient.mk (zeroIdeal R κ n I B)).comp (algebraMap A O)

theorem base_scalar (a : R) : baseMap R κ n I B (algebraMap R A a) = algebraMap R Q a := rfl

def baseAlgMap : A →ₐ[R] Q where
  __ := baseMap R κ n I B
  commutes' := base_scalar R κ n I B

theorem chart_unit : IsUnit (baseMap R κ n I B (chartValue R κ n I B)) :=
  (IsLocalization.Away.algebraMap_isUnit (S := O) (chartValue R κ n I B)).map
    (Ideal.Quotient.mk (zeroIdeal R κ n I B))

theorem selected_zero (i : Selected n I) : baseMap R κ n I B (initial R κ n B (Sum.inl i.val)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

variable {S : Type} [CommRing S] (g : Global R κ n B →+* S)
variable (hg : IsUnit (g (chartValue R κ n I B)))
variable (hz : ∀ i : Selected n I, g (initial R κ n B (Sum.inl i.val)) = 0)

def lift : Q →+* S :=
  Ideal.Quotient.lift _ (IsLocalization.Away.lift (S := O) (chartValue R κ n I B) hg) (by
    have hker : zeroIdeal R κ n I B ≤ RingHom.ker
        (IsLocalization.Away.lift (S := O) (chartValue R κ n I B) hg) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change IsLocalization.Away.lift (chartValue R κ n I B) hg
        (algebraMap A O (initial R κ n B (Sum.inl i.val))) = 0
      rw [IsLocalization.Away.lift_eq]
      exact hz i
    exact fun a ha => hker ha)

theorem lift_base (a : A) : lift R κ n I B g hg hz (baseMap R κ n I B a) = g a :=
  IsLocalization.Away.lift_eq (chartValue R κ n I B) hg a

theorem hom_ext (f h : Q →+* S)
    (heq : f.comp (baseMap R κ n I B) = h.comp (baseMap R κ n I B)) : f = h := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (chartValue R κ n I B))
  exact heq

theorem hom_ext_generators (f h : Q →+* S)
    (hs : ∀ a : R, f (algebraMap R Q a) = h (algebraMap R Q a))
    (hx : ∀ a, f (baseMap R κ n I B (initial R κ n B a)) = h (baseMap R κ n I B (initial R κ n B a)))
    (hy : ∀ i, f (baseMap R κ n I B (mutated R κ n B i)) = h (baseMap R κ n I B (mutated R κ n B i))) : f = h := by
  apply hom_ext R κ n I B
  apply OriginalGlobalGenerators.hom_ext R κ n B
  · exact hs
  · exact hx
  · exact hy

#print axioms baseMap
#print axioms base_scalar
#print axioms baseAlgMap
#print axioms chart_unit
#print axioms selected_zero
#print axioms lift
#print axioms lift_base
#print axioms hom_ext
#print axioms hom_ext_generators
end Verification.OriginalStratumUniversal
