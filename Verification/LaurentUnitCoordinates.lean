/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinsuppLaurentUnits

/-!
# Laurent Unit Coordinates

Unique Laurent-unit coordinates over a domain, including the actual
integer exponent homomorphism and its monomial section. This supplies the
independent exponents in the last Milnor differential, without assuming
the unit-expression assertion of the manuscript.
-/
noncomputable section
namespace Verification.LaurentUnitCoordinates
open scoped BigOperators
variable (R κ : Type) [CommRing R] [IsDomain R] [Fintype κ]

def monomial (c : Rˣ) (a : κ →₀ ℤ) : (OriginalTorus.Torus R κ)ˣ :=
  Units.map (algebraMap R (OriginalTorus.Torus R κ)).toMonoidHom c *
    (MonoidAlgebra.of R (Multiplicative (κ→₀ℤ))).toHomUnits (Multiplicative.ofAdd a)

omit [IsDomain R] [Fintype κ] in
theorem monomial_val (c : Rˣ) (a : κ→₀ℤ) :
    (monomial R κ c a : OriginalTorus.Torus R κ)=
      Finsupp.single (Multiplicative.ofAdd a) (c:R) := by
  change (MonoidAlgebra.single 1 (c:R) : OriginalTorus.Torus R κ)*
    MonoidAlgebra.single (Multiplicative.ofAdd a) (1:R)=_
  rw [MonoidAlgebra.single_mul_single,one_mul,mul_one]

omit [Fintype κ] in
theorem monomial_injective : Function.Injective
    (fun z : Rˣ × (κ→₀ℤ) => monomial R κ z.1 z.2) := by
  rintro ⟨c,a⟩ ⟨d,b⟩ h
  have he := congrArg Units.val h
  rw [monomial_val,monomial_val] at he
  have hh := (Finsupp.single_eq_single_iff _ _ _ _).mp he
  have hh := hh.resolve_right (fun h => c.ne_zero h.1)
  exact Prod.ext (Units.ext hh.2) hh.1

theorem monomial_surjective : Function.Surjective
    (fun z : Rˣ × (κ→₀ℤ) => monomial R κ z.1 z.2) := by
  intro u
  obtain ⟨a,c,h⟩ := FinsuppLaurentUnits.unit_monomial R κ u
  exact ⟨⟨c,a⟩,Units.ext ((monomial_val R κ c a).trans h.symm)⟩

def coordinateEquiv : Rˣ × Multiplicative (κ→₀ℤ) ≃*
    (OriginalTorus.Torus R κ)ˣ := by
  let f : Rˣ × Multiplicative (κ→₀ℤ) →* (OriginalTorus.Torus R κ)ˣ :=
    { toFun := fun z => monomial R κ z.1 z.2.toAdd
      map_one' := by simp [monomial]
      map_mul' := by
        rintro ⟨c,a⟩ ⟨d,b⟩
        simp only [monomial,Prod.fst_mul,Prod.snd_mul,toAdd_mul,
          ofAdd_add,map_mul]
        ac_rfl }
  exact MulEquiv.ofBijective f
    ⟨fun _ _ h => monomial_injective R κ h,fun u => monomial_surjective R κ u⟩

def exponent : (OriginalTorus.Torus R κ)ˣ →* Multiplicative (κ→₀ℤ) :=
  (MonoidHom.snd Rˣ (Multiplicative (κ→₀ℤ))).comp (coordinateEquiv R κ).symm.toMonoidHom

theorem exponent_monomial (c : Rˣ) (a : κ→₀ℤ) :
    exponent R κ (monomial R κ c a)=Multiplicative.ofAdd a :=
  congrArg Prod.snd ((coordinateEquiv R κ).symm_apply_apply (c,Multiplicative.ofAdd a))

theorem exponent_surjective : Function.Surjective (exponent R κ) := by
  intro a
  exact ⟨monomial R κ 1 a.toAdd,exponent_monomial R κ 1 a.toAdd⟩

theorem unique_expression (u : (OriginalTorus.Torus R κ)ˣ) :
    ∃! z : Rˣ × (κ→₀ℤ),u=monomial R κ z.1 z.2 := by
  obtain ⟨z,hz⟩ := monomial_surjective R κ u
  exact ⟨z,hz.symm,fun y hy => monomial_injective R κ (hy.symm.trans hz.symm)⟩

theorem exponent_variable (i : κ) :
    exponent R κ (ScalarGlobalUnits.laurentVariable R κ i)=
      Multiplicative.ofAdd (Finsupp.single i 1) := by
  have h := exponent_monomial R κ 1 (Finsupp.single i 1)
  simpa [monomial,ScalarGlobalUnits.laurentVariable] using h

#print axioms monomial
#print axioms monomial_val
#print axioms monomial_injective
#print axioms monomial_surjective
#print axioms coordinateEquiv
#print axioms exponent
#print axioms exponent_monomial
#print axioms exponent_surjective
#print axioms unique_expression
#print axioms exponent_variable
end Verification.LaurentUnitCoordinates
