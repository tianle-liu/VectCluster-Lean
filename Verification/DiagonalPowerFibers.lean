/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmoothPowerChart
import Verification.PrimitiveCharacters
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.FinitePresentation

/-!
# Diagonal Power Fibers

Simultaneous power equations, with their actual quotient algebra.
Integral coordinate generators prove finiteness; coordinatewise unique
square-zero lifting proves formal etaleness. Laurent coordinates are
identified by explicit maps, since all the quotient coordinates are units.
-/

noncomputable section
universe u
namespace Verification.DiagonalPowerFibers
open MvPolynomial
variable {R ι : Type u} [CommRing R]

def relation (e : ι → ℕ) (b : ι → Rˣ) (i : ι) : MvPolynomial ι R :=
  X i ^ e i - C (b i : R)

def relations (e : ι → ℕ) (b : ι → Rˣ) : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (relation e b))

abbrev PowerAlgebra (e : ι → ℕ) (b : ι → Rˣ) := MvPolynomial ι R ⧸ relations e b

def coordinate (e : ι → ℕ) (b : ι → Rˣ) (i : ι) : PowerAlgebra e b :=
  Ideal.Quotient.mk (relations e b) (X i)

theorem coordinate_power (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    coordinate e b i ^ e i = algebraMap R (PowerAlgebra e b) (b i : R) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self i) : relation e b i ∈ relations e b)
  simpa only [relation, map_sub, map_pow, sub_eq_zero] using h

def lift {S : Type u} [CommRing S] [Algebra R S]
    (e : ι → ℕ) (b : ι → Rˣ) (x : ι → S)
    (hx : ∀ i, x i ^ e i = algebraMap R S (b i : R)) : PowerAlgebra e b →ₐ[R] S :=
  Ideal.Quotient.liftₐ (relations e b) (aeval x) (by
    change relations e b ≤ RingHom.ker (aeval x).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval x (relation e b i) = 0
    simp [relation, hx])

theorem lift_coordinate {S : Type u} [CommRing S] [Algebra R S]
    (e : ι → ℕ) (b : ι → Rˣ) (x : ι → S)
    (hx : ∀ i, x i ^ e i = algebraMap R S (b i : R)) (i : ι) :
    lift e b x hx (coordinate e b i) = x i := by
  simp [lift, coordinate]

theorem hom_ext {S : Type u} [CommRing S] [Algebra R S]
    (e : ι → ℕ) (b : ι → Rˣ) (f g : PowerAlgebra e b →ₐ[R] S)
    (h : ∀ i, f (coordinate e b i) = g (coordinate e b i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

theorem coordinate_aeval (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    Polynomial.aeval (coordinate e b i) (SmoothPowerChart.powerPolynomial R (e i) (b i)) = 0 := by
  simp [SmoothPowerChart.powerPolynomial, coordinate_power]

theorem coordinate_integral (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) (i : ι) :
    IsIntegral R (coordinate e b i) :=
  ⟨SmoothPowerChart.powerPolynomial R (e i) (b i),
    SmoothPowerChart.power_monic R (e i) (b i) (he i), coordinate_aeval e b i⟩

theorem adjoin_coordinates (e : ι → ℕ) (b : ι → Rˣ) :
    Algebra.adjoin R (Set.range (coordinate e b)) = ⊤ := by
  have h := congrArg (fun A : Subalgebra R (MvPolynomial ι R) =>
    A.map (Ideal.Quotient.mkₐ R (relations e b))) (MvPolynomial.adjoin_range_X (σ := ι) (R := R))
  dsimp only at h
  rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top] at h
  change Algebra.adjoin R (Set.range (coordinate e b)) =
    (Ideal.Quotient.mkₐ R (relations e b)).range at h
  rw [h, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

theorem power_finite [Finite ι] (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    Module.Finite R (PowerAlgebra e b) := by
  constructor
  have hfg := fg_adjoin_of_finite (R := R) (Set.finite_range (coordinate e b))
    (by rintro _ ⟨i, rfl⟩; exact coordinate_integral e b he i)
  simpa [adjoin_coordinates] using hfg

theorem power_finitePresentation [Finite ι] (e : ι → ℕ) (b : ι → Rˣ) :
    Algebra.FinitePresentation R (PowerAlgebra e b) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range (relation e b)))

def factorMap (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    SmoothPowerChart.PowerAlgebra R (e i) (b i) →ₐ[R] PowerAlgebra e b :=
  AdjoinRoot.liftHom _ (coordinate e b i) (coordinate_aeval e b i)

theorem factorMap_root (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    factorMap e b i (SmoothPowerChart.root R (e i) (b i)) = coordinate e b i := by
  exact AdjoinRoot.liftHom_root _ _

theorem power_formallyEtale (e : ι → ℕ) (b : ι → Rˣ)
    (he : ∀ i, IsUnit (e i : R)) : Algebra.FormallyEtale R (PowerAlgebra e b) := by
  constructor
  intro B _ _ J hJ
  constructor
  · intro g h hgh
    apply hom_ext e b
    intro i
    letI := SmoothPowerChart.power_etale R (e i) (b i) (he i)
    have heq : g.comp (factorMap e b i) = h.comp (factorMap e b i) := by
      apply (Algebra.FormallyEtale.comp_bijective (R := R)
        (A := SmoothPowerChart.PowerAlgebra R (e i) (b i)) J hJ).injective
      exact congrArg (fun f : PowerAlgebra e b →ₐ[R] B ⧸ J => f.comp (factorMap e b i)) hgh
    simpa only [AlgHom.comp_apply, factorMap_root] using
      AlgHom.congr_fun heq (SmoothPowerChart.root R (e i) (b i))
  · intro f
    have hex (i : ι) : ∃ g : SmoothPowerChart.PowerAlgebra R (e i) (b i) →ₐ[R] B,
        (Ideal.Quotient.mkₐ R J).comp g = f.comp (factorMap e b i) := by
      letI := SmoothPowerChart.power_etale R (e i) (b i) (he i)
      exact (Algebra.FormallyEtale.comp_bijective (R := R)
        (A := SmoothPowerChart.PowerAlgebra R (e i) (b i)) J hJ).surjective _
    choose g hg using hex
    let x : ι → B := fun i => g i (SmoothPowerChart.root R (e i) (b i))
    have hx (i : ι) : x i ^ e i = algebraMap R B (b i : R) := by
      dsimp [x]
      rw [← map_pow, SmoothPowerChart.root_power, AlgHom.commutes]
    refine ⟨lift e b x hx, ?_⟩
    apply hom_ext e b
    intro i
    rw [AlgHom.comp_apply, lift_coordinate]
    simpa only [AlgHom.comp_apply, factorMap_root] using
      AlgHom.congr_fun (hg i) (SmoothPowerChart.root R (e i) (b i))

theorem power_etale [Finite ι] (e : ι → ℕ) (b : ι → Rˣ)
    (he : ∀ i, IsUnit (e i : R)) : Algebra.Etale R (PowerAlgebra e b) where
  formallyEtale := power_formallyEtale e b he
  finitePresentation := power_finitePresentation e b

theorem power_finite_etale [Finite ι] (e : ι → ℕ) (b : ι → Rˣ)
    (hpos : ∀ i, 0 < e i) (he : ∀ i, IsUnit (e i : R)) :
    Module.Finite R (PowerAlgebra e b) ∧ Algebra.Etale R (PowerAlgebra e b) :=
  ⟨power_finite e b hpos, power_etale e b he⟩

theorem coordinate_unit (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) (i : ι) :
    IsUnit (coordinate e b i) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt (he i))).mp
  rw [coordinate_power]
  exact (b i).isUnit.map (algebraMap R (PowerAlgebra e b))

abbrev Laurent (R ι : Type u) [CommRing R] :=
  MonoidAlgebra R (Multiplicative (ι →₀ ℤ))

def laurentCoordinate (R ι : Type u) [CommRing R] (i : ι) : Laurent R ι :=
  MonoidAlgebra.of R _ (Multiplicative.ofAdd (Finsupp.single i 1))

def laurentRelations (e : ι → ℕ) (b : ι → Rˣ) : Ideal (Laurent R ι) :=
  Ideal.span (Set.range (fun i => laurentCoordinate R ι i ^ e i -
    algebraMap R (Laurent R ι) (b i : R)))

abbrev LaurentPowerAlgebra (e : ι → ℕ) (b : ι → Rˣ) := Laurent R ι ⧸ laurentRelations e b

def laurentQuotientCoordinate (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    LaurentPowerAlgebra e b := Ideal.Quotient.mk (laurentRelations e b) (laurentCoordinate R ι i)

theorem laurentQuotientCoordinate_power (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    laurentQuotientCoordinate e b i ^ e i = algebraMap R (LaurentPowerAlgebra e b) (b i : R) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self i) :
      laurentCoordinate R ι i ^ e i - algebraMap R _ (b i : R) ∈ laurentRelations e b)
  simpa only [map_sub, map_pow, sub_eq_zero] using h

theorem laurent_hom_ext {S : Type u} [CommRing S] [Algebra R S]
    (f g : Laurent R ι →ₐ[R] S) (h : ∀ i, f (laurentCoordinate R ι i) =
      g (laurentCoordinate R ι i)) : f = g := by
  apply MonoidAlgebra.algHom_ext'
  apply MonoidHom.eq_of_eqOn_dense
    (Verification.PrimitiveCharacters.basis_generates
      (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)))
  rintro _ ⟨i, rfl⟩
  exact h i

theorem laurent_quotient_hom_ext {S : Type u} [CommRing S] [Algebra R S]
    (e : ι → ℕ) (b : ι → Rˣ) (f g : LaurentPowerAlgebra e b →ₐ[R] S)
    (h : ∀ i, f (laurentQuotientCoordinate e b i) = g (laurentQuotientCoordinate e b i)) :
    f = g := by
  apply Ideal.Quotient.algHom_ext
  exact laurent_hom_ext _ _ h

def coordinateUnits (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) (i : ι) :
    (PowerAlgebra e b)ˣ := (coordinate_unit e b he i).unit

def evaluateLaurent (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    Laurent R ι →ₐ[R] PowerAlgebra e b :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom (PowerAlgebra e b)).comp
    (Verification.PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne (coordinateUnits e b he)))

theorem evaluateLaurent_coordinate (e : ι → ℕ) (b : ι → Rˣ)
    (he : ∀ i, 0 < e i) (i : ι) :
    evaluateLaurent e b he (laurentCoordinate R ι i) = coordinate e b i := by
  rw [evaluateLaurent, laurentCoordinate, MonoidAlgebra.lift_of]
  change ((Verification.PrimitiveCharacters.basisCharacter
    (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)) (coordinateUnits e b he))
      (Multiplicative.ofAdd (Finsupp.single i 1)) : PowerAlgebra e b) = _
  have h := Verification.PrimitiveCharacters.basisCharacter_apply
    (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)) (coordinateUnits e b he) i
  simpa [Finsupp.coe_basisSingleOne, coordinateUnits] using congrArg Units.val h

def toPolynomial (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    LaurentPowerAlgebra e b →ₐ[R] PowerAlgebra e b :=
  Ideal.Quotient.liftₐ (laurentRelations e b) (evaluateLaurent e b he) (by
    change laurentRelations e b ≤ RingHom.ker (evaluateLaurent e b he).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change evaluateLaurent e b he
      (laurentCoordinate R ι i ^ e i - algebraMap R _ (b i : R)) = 0
    rw [map_sub, map_pow, evaluateLaurent_coordinate, AlgHom.commutes,
      coordinate_power, sub_self])

theorem toPolynomial_coordinate (e : ι → ℕ) (b : ι → Rˣ)
    (he : ∀ i, 0 < e i) (i : ι) :
    toPolynomial e b he (laurentQuotientCoordinate e b i) = coordinate e b i :=
  evaluateLaurent_coordinate e b he i

def toLaurent (e : ι → ℕ) (b : ι → Rˣ) : PowerAlgebra e b →ₐ[R] LaurentPowerAlgebra e b :=
  lift e b (laurentQuotientCoordinate e b) (laurentQuotientCoordinate_power e b)

theorem toLaurent_coordinate (e : ι → ℕ) (b : ι → Rˣ) (i : ι) :
    toLaurent e b (coordinate e b i) = laurentQuotientCoordinate e b i :=
  lift_coordinate e b _ _ i

theorem toPolynomial_toLaurent (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    (toPolynomial e b he).comp (toLaurent e b) = AlgHom.id R _ := by
  apply hom_ext e b
  intro i
  simp only [AlgHom.comp_apply, toLaurent_coordinate, toPolynomial_coordinate, AlgHom.id_apply]

theorem toLaurent_toPolynomial (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    (toLaurent e b).comp (toPolynomial e b he) = AlgHom.id R _ := by
  apply laurent_quotient_hom_ext e b
  intro i
  simp only [AlgHom.comp_apply, toLaurent_coordinate, toPolynomial_coordinate, AlgHom.id_apply]

def laurentPowerEquiv (e : ι → ℕ) (b : ι → Rˣ) (he : ∀ i, 0 < e i) :
    LaurentPowerAlgebra e b ≃ₐ[R] PowerAlgebra e b :=
  AlgEquiv.ofAlgHom (toPolynomial e b he) (toLaurent e b)
    (toPolynomial_toLaurent e b he) (toLaurent_toPolynomial e b he)

theorem laurent_finite_etale [Finite ι] (e : ι → ℕ) (b : ι → Rˣ)
    (hpos : ∀ i, 0 < e i) (he : ∀ i, IsUnit (e i : R)) :
    Module.Finite R (LaurentPowerAlgebra e b) ∧ Algebra.Etale R (LaurentPowerAlgebra e b) := by
  letI := power_finite e b hpos
  letI := power_etale e b he
  exact ⟨Module.Finite.equiv (laurentPowerEquiv e b hpos).symm.toLinearEquiv,
    Algebra.Etale.of_equiv (laurentPowerEquiv e b hpos).symm⟩

theorem laurent_finite_separable_product {k : Type u} [Field k] [Finite ι]
    (e : ι → ℕ) (b : ι → kˣ) (hpos : ∀ i, 0 < e i) (he : ∀ i, (e i : k) ≠ 0) :
    ∃ (κ : Type u) (_ : Finite κ) (L : κ → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra k (L i)) (_ : LaurentPowerAlgebra e b ≃ₐ[k] ∀ i, L i),
      ∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i) :=
  (Algebra.Etale.iff_exists_algEquiv_prod k _).mp
    (laurent_finite_etale e b hpos (fun i => isUnit_iff_ne_zero.mpr (he i))).2

#print axioms relation
#print axioms relations
#print axioms PowerAlgebra
#print axioms coordinate
#print axioms coordinate_power
#print axioms lift
#print axioms lift_coordinate
#print axioms hom_ext
#print axioms coordinate_aeval
#print axioms coordinate_integral
#print axioms adjoin_coordinates
#print axioms power_finite
#print axioms power_finitePresentation
#print axioms factorMap
#print axioms factorMap_root
#print axioms power_formallyEtale
#print axioms power_etale
#print axioms power_finite_etale
#print axioms coordinate_unit
#print axioms Laurent
#print axioms laurentCoordinate
#print axioms laurentRelations
#print axioms LaurentPowerAlgebra
#print axioms laurentQuotientCoordinate
#print axioms laurentQuotientCoordinate_power
#print axioms laurent_hom_ext
#print axioms laurent_quotient_hom_ext
#print axioms coordinateUnits
#print axioms evaluateLaurent
#print axioms evaluateLaurent_coordinate
#print axioms toPolynomial
#print axioms toPolynomial_coordinate
#print axioms toLaurent
#print axioms toLaurent_coordinate
#print axioms toPolynomial_toLaurent
#print axioms toLaurent_toPolynomial
#print axioms laurentPowerEquiv
#print axioms laurent_finite_etale
#print axioms laurent_finite_separable_product
end Verification.DiagonalPowerFibers
