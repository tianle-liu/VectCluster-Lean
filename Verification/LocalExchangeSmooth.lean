/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CharacterMapSmooth

/-!
# Local Exchange Smooth

The literal local exchange-equation quotient is smooth. The proof
lifts its coordinates and coefficients across square-zero ideals; it does
not assume an identification with a fiber product. The chosen x-lifts can
be prescribed, which is the algebraic input for transverse x-parameters.
-/

noncomputable section
universe u
namespace Verification.LocalExchangeSmooth
open MvPolynomial
variable {R S κ : Type u} [CommRing R] [CommRing S] [Algebra R S]

def relation (χ : κ → Sˣ) (k : κ) : MvPolynomial (κ ⊕ κ) S :=
  X (Sum.inl k) * X (Sum.inr k) - 1 - C (χ k : S)

def relations (χ : κ → Sˣ) : Ideal (MvPolynomial (κ ⊕ κ) S) :=
  Ideal.span (Set.range (relation χ))

abbrev LocalAlgebra (χ : κ → Sˣ) := MvPolynomial (κ ⊕ κ) S ⧸ relations χ

def x (χ : κ → Sˣ) (k : κ) : LocalAlgebra χ := Ideal.Quotient.mk (relations χ) (X (Sum.inl k))
def y (χ : κ → Sˣ) (k : κ) : LocalAlgebra χ := Ideal.Quotient.mk (relations χ) (X (Sum.inr k))

theorem equation (χ : κ → Sˣ) (k : κ) :
    x χ k * y χ k - 1 = algebraMap S (LocalAlgebra χ) (χ k : S) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self k) : relation χ k ∈ relations χ)
  simpa only [relation, map_sub, map_mul, map_one, sub_eq_zero] using h

def lift {B : Type u} [CommRing B] [Algebra R B]
    (χ : κ → Sˣ) (s : S →ₐ[R] B) (a b : κ → B)
    (h : ∀ k, a k * b k - 1 = s (χ k : S)) : LocalAlgebra χ →ₐ[R] B :=
  Ideal.Quotient.liftₐ (relations χ) (aevalTower s (Sum.elim a b)) (by
    change relations χ ≤ RingHom.ker (aevalTower s (Sum.elim a b)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨k,rfl⟩
    change aevalTower s (Sum.elim a b) (relation χ k) = 0
    simp [relation, h])

theorem lift_x {B : Type u} [CommRing B] [Algebra R B]
    (χ : κ → Sˣ) (s : S →ₐ[R] B) (a b : κ → B)
    (h : ∀ k, a k * b k - 1 = s (χ k : S)) (k : κ) :
    lift χ s a b h (x χ k) = a k := by simp [lift, x]

theorem lift_y {B : Type u} [CommRing B] [Algebra R B]
    (χ : κ → Sˣ) (s : S →ₐ[R] B) (a b : κ → B)
    (h : ∀ k, a k * b k - 1 = s (χ k : S)) (k : κ) :
    lift χ s a b h (y χ k) = b k := by simp [lift, y]

theorem lift_coefficient {B : Type u} [CommRing B] [Algebra R B]
    (χ : κ → Sˣ) (s : S →ₐ[R] B) (a b : κ → B)
    (h : ∀ k, a k * b k - 1 = s (χ k : S)) (z : S) :
    lift χ s a b h (algebraMap S (LocalAlgebra χ) z) = s z := by
  change aevalTower s (Sum.elim a b) (C z) = s z
  exact aevalTower_C _ _ _

theorem hom_ext {B : Type u} [CommRing B] [Algebra R B]
    (χ : κ → Sˣ) (f g : LocalAlgebra χ →ₐ[R] B)
    (hS : ∀ z, f (algebraMap S (LocalAlgebra χ) z) = g (algebraMap S (LocalAlgebra χ) z))
    (hx : ∀ k, f (x χ k) = g (x χ k)) (hy : ∀ k, f (y χ k) = g (y χ k)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · exact hS
  · intro v
    cases v with
    | inl k => exact hx k
    | inr k => exact hy k

abbrev Target (R κ : Type u) [CommRing R] := DiagonalPowerFibers.Laurent R κ

section CharacterAlgebra
variable [Algebra (Target R κ) S] [IsScalarTower R (Target R κ) S]
variable (χ : κ → Sˣ)
variable (hχ : ∀ k, algebraMap (Target R κ) S (DiagonalPowerFibers.laurentCoordinate R κ k) = χ k)
include hχ

theorem lift_with_coordinates [Algebra.FormallySmooth (Target R κ) S]
    {B : Type u} [CommRing B] [Algebra R B] (J : Ideal B) (hJ : J ^ 2 = ⊥)
    (f : LocalAlgebra χ →ₐ[R] B ⧸ J) (a b : κ → B)
    (ha : ∀ k, Ideal.Quotient.mk J (a k) = f (x χ k))
    (hb : ∀ k, Ideal.Quotient.mk J (b k) = f (y χ k)) :
    ∃ g : LocalAlgebra χ →ₐ[R] B,
      (Ideal.Quotient.mkₐ R J).comp g = f ∧ (∀ k, g (x χ k) = a k) ∧ (∀ k, g (y χ k) = b k) := by
  have hJnil : IsNilpotent J := ⟨2,hJ⟩
  have hwmod (k : κ) : Ideal.Quotient.mk J (a k * b k - 1) =
      f (algebraMap S (LocalAlgebra χ) (χ k : S)) := by
    rw [map_sub, map_mul, map_one, ha, hb, ← map_mul, ← map_one f, ← map_sub, equation]
  have hwu (k : κ) : IsUnit (a k * b k - 1) := by
    apply hJnil.isUnit_quotient_mk_iff.mp
    rw [hwmod]
    exact ((χ k).isUnit.map (algebraMap S (LocalAlgebra χ))).map f.toRingHom
  let w : κ → Bˣ := fun k => (hwu k).unit
  let tB : Target R κ →ₐ[R] B := PartialPowerSmooth.evaluateUnits w
  letI := tB.toRingHom.toAlgebra
  have ht (k : κ) : algebraMap (Target R κ) B (DiagonalPowerFibers.laurentCoordinate R κ k) =
      a k * b k - 1 := by
    change tB (DiagonalPowerFibers.laurentCoordinate R κ k) = _
    rw [show tB (DiagonalPowerFibers.laurentCoordinate R κ k) = (w k : B) from
      PartialPowerSmooth.evaluateUnits_coordinate w k]
    exact (hwu k).unit_spec
  let c : S →ₐ[R] B ⧸ J := f.comp (IsScalarTower.toAlgHom R S (LocalAlgebra χ))
  have hc : c.comp (IsScalarTower.toAlgHom R (Target R κ) S) =
      (Ideal.Quotient.mkₐ R J).comp tB := by
    apply DiagonalPowerFibers.laurent_hom_ext
    intro k
    change f (algebraMap S (LocalAlgebra χ)
      (algebraMap (Target R κ) S (DiagonalPowerFibers.laurentCoordinate R κ k))) =
      Ideal.Quotient.mk J (tB (DiagonalPowerFibers.laurentCoordinate R κ k))
    rw [hχ, show tB (DiagonalPowerFibers.laurentCoordinate R κ k) = a k * b k - 1 from ht k]
    exact (hwmod k).symm
  let cT : S →ₐ[Target R κ] B ⧸ J :=
    { c.toRingHom with commutes' := fun t => AlgHom.congr_fun hc t }
  obtain ⟨g,hg⟩ := (Algebra.FormallySmooth.comp_surjective (R := Target R κ) (A := S) J hJ) cT
  have hrel (k : κ) : a k * b k - 1 = g (χ k : S) := by
    rw [← hχ, AlgHom.commutes]
    exact (ht k).symm
  refine ⟨lift χ (g.restrictScalars R) a b hrel, ?_, lift_x χ _ a b hrel, lift_y χ _ a b hrel⟩
  apply hom_ext χ
  · intro z
    rw [AlgHom.comp_apply, lift_coefficient]
    exact AlgHom.congr_fun hg z
  · intro k
    rw [AlgHom.comp_apply, lift_x]
    exact ha k
  · intro k
    rw [AlgHom.comp_apply, lift_y]
    exact hb k

theorem local_formallySmooth [Algebra.FormallySmooth (Target R κ) S] :
    Algebra.FormallySmooth R (LocalAlgebra χ) := by
  constructor
  intro B _ _ J hJ f
  choose a ha using (fun k => Ideal.Quotient.mk_surjective (f (x χ k)))
  choose b hb using (fun k => Ideal.Quotient.mk_surjective (f (y χ k)))
  obtain ⟨g,hg,_,_⟩ := lift_with_coordinates χ hχ J hJ f a b ha hb
  exact ⟨g,hg⟩

omit hχ [Algebra (Target R κ) S] [IsScalarTower R (Target R κ) S] in
theorem local_finitePresentation [Finite κ] [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R (LocalAlgebra χ) := by
  letI := Algebra.FinitePresentation.trans R S (MvPolynomial (κ ⊕ κ) S)
  exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range (relation χ)))

theorem local_smooth [Fintype κ] [Algebra.Smooth (Target R κ) S] :
    Algebra.Smooth R (LocalAlgebra χ) := by
  letI := TorusSmooth.torus_smooth R κ
  letI := Algebra.Smooth.comp R (Target R κ) S
  exact {
    formallySmooth := local_formallySmooth χ hχ
    finitePresentation := local_finitePresentation χ }

end CharacterAlgebra

def characterUnits {M : Type u} [AddCommGroup M]
    (R : Type u) [CommRing R] (f : (κ →₀ ℤ) →ₗ[ℤ] M) (k : κ) :
    (CharacterMapSmooth.Torus R M)ˣ :=
  (MonoidAlgebra.of R (Multiplicative M)).toHomUnits
    (Multiplicative.ofAdd (f (Finsupp.single k 1)))

theorem local_character_smooth {M ι : Type u} [AddCommGroup M] [Fintype κ] [Fintype ι]
    (f : (κ →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f)
    {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)
    (he : ∀ i, IsUnit ((s.a i).natAbs : R)) :
    Algebra.Smooth R (LocalAlgebra (characterUnits R f)) := by
  letI := (CharacterMapSmooth.characterMap (R := R) f).toRingHom.toAlgebra
  letI := CharacterMapSmooth.characterMap_smooth f hf Finsupp.basisSingleOne s he
  apply local_smooth (characterUnits R f)
  intro k
  exact CharacterMapSmooth.characterMap_monomial f (Finsupp.single k 1)

theorem local_character_smooth_charZero {k M ι : Type u} [Field k] [CharZero k]
    [AddCommGroup M] [Fintype κ] [Fintype ι]
    (bM : Basis ι ℤ M) (f : (κ →₀ ℤ) →ₗ[ℤ] M) (hf : Function.Injective f) :
    Algebra.Smooth k (LocalAlgebra (characterUnits k f)) := by
  letI := (CharacterMapSmooth.characterMap (R := k) f).toRingHom.toAlgebra
  letI := CharacterMapSmooth.characterMap_smooth_charZero (k := k) bM f hf Finsupp.basisSingleOne
  apply local_smooth (characterUnits k f)
  intro i
  exact CharacterMapSmooth.characterMap_monomial f (Finsupp.single i 1)

#print axioms relation
#print axioms relations
#print axioms LocalAlgebra
#print axioms x
#print axioms y
#print axioms equation
#print axioms lift
#print axioms lift_x
#print axioms lift_y
#print axioms lift_coefficient
#print axioms hom_ext
#print axioms Target
#print axioms lift_with_coordinates
#print axioms local_formallySmooth
#print axioms local_finitePresentation
#print axioms local_smooth
#print axioms characterUnits
#print axioms local_character_smooth
#print axioms local_character_smooth_charZero
end Verification.LocalExchangeSmooth
