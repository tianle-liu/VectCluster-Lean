/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DiagonalPowerFibers
import Verification.SmithCharacters

/-!
# Partial Power Smooth

Smoothness of the actual partial power-equation quotient of a Laurent
algebra. Independent constrained coordinates lift by separable root lifting;
the remaining coordinates lift as units. No product decomposition or
smoothness of the quotient is assumed.
-/

noncomputable section
universe u v
namespace Verification.PartialPowerSmooth
open DiagonalPowerFibers
variable {R ι : Type u} {κ : Type v} [CommRing R]

def relations (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) : Ideal (Laurent R ι) :=
  Ideal.span (Set.range (fun k => laurentCoordinate R ι (j k) ^ e k -
    algebraMap R (Laurent R ι) (b k : R)))

abbrev PartialAlgebra (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :=
  Laurent R ι ⧸ relations j e b

def coordinate (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (i : ι) : PartialAlgebra j e b :=
  Ideal.Quotient.mk (relations j e b) (laurentCoordinate R ι i)

theorem coordinate_power (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (k : κ) :
    coordinate j e b (j k) ^ e k = algebraMap R (PartialAlgebra j e b) (b k : R) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self k) :
      laurentCoordinate R ι (j k) ^ e k - algebraMap R _ (b k : R) ∈ relations j e b)
  simpa only [map_sub, map_pow, sub_eq_zero] using h

def coordinateUnit (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (i : ι) :
    (PartialAlgebra j e b)ˣ :=
  Units.map (Ideal.Quotient.mk (relations j e b)).toMonoidHom
    ((MonoidAlgebra.of R (Multiplicative (ι →₀ ℤ))).toHomUnits
      (Multiplicative.ofAdd (Finsupp.single i 1)))

theorem coordinateUnit_val (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (i : ι) :
    (coordinateUnit j e b i : PartialAlgebra j e b) = coordinate j e b i := rfl

theorem hom_ext {S : Type u} [CommRing S] [Algebra R S]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (f g : PartialAlgebra j e b →ₐ[R] S)
    (h : ∀ i, f (coordinate j e b i) = g (coordinate j e b i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  exact DiagonalPowerFibers.laurent_hom_ext _ _ h

def evaluateUnits {S : Type u} [CommRing S] [Algebra R S] (x : ι → Sˣ) :
    Laurent R ι →ₐ[R] S :=
  MonoidAlgebra.lift R _ _ ((Units.coeHom S).comp
    (Verification.PrimitiveCharacters.basisCharacter Finsupp.basisSingleOne x))

theorem evaluateUnits_coordinate {S : Type u} [CommRing S] [Algebra R S]
    (x : ι → Sˣ) (i : ι) : evaluateUnits x (laurentCoordinate R ι i) = x i := by
  rw [evaluateUnits, laurentCoordinate, MonoidAlgebra.lift_of]
  change ((Verification.PrimitiveCharacters.basisCharacter
    (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)) x)
      (Multiplicative.ofAdd (Finsupp.single i 1)) : S) = _
  have h := Verification.PrimitiveCharacters.basisCharacter_apply
    (Finsupp.basisSingleOne : Basis ι ℤ (ι →₀ ℤ)) x i
  simpa [Finsupp.coe_basisSingleOne] using congrArg Units.val h

def lift {S : Type u} [CommRing S] [Algebra R S]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (x : ι → Sˣ)
    (hx : ∀ k, (x (j k) : S) ^ e k = algebraMap R S (b k : R)) :
    PartialAlgebra j e b →ₐ[R] S :=
  Ideal.Quotient.liftₐ (relations j e b) (evaluateUnits x) (by
    change relations j e b ≤ RingHom.ker (evaluateUnits x).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change evaluateUnits x
      (laurentCoordinate R ι (j k) ^ e k - algebraMap R _ (b k : R)) = 0
    rw [map_sub, map_pow, evaluateUnits_coordinate, AlgHom.commutes, hx, sub_self])

theorem lift_coordinate {S : Type u} [CommRing S] [Algebra R S]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (x : ι → Sˣ)
    (hx : ∀ k, (x (j k) : S) ^ e k = algebraMap R S (b k : R)) (i : ι) :
    lift j e b x hx (coordinate j e b i) = x i := evaluateUnits_coordinate x i

def factorMap (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (k : κ) :
    SmoothPowerChart.PowerAlgebra R (e k) (b k) →ₐ[R] PartialAlgebra j e b :=
  AdjoinRoot.liftHom _ (coordinate j e b (j k)) (by
    simp [SmoothPowerChart.powerPolynomial, coordinate_power])

theorem factorMap_root (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (k : κ) :
    factorMap j e b k (SmoothPowerChart.root R (e k) (b k)) = coordinate j e b (j k) :=
  AdjoinRoot.liftHom_root _ _

theorem lift_unit_mod_nilpotent {B : Type u} [CommRing B] (J : Ideal B)
    (hJ : IsNilpotent J) (v : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = v := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : B ⧸ J)
  have hau : IsUnit a := hJ.isUnit_quotient_mk_iff.mp (ha ▸ v.isUnit)
  exact ⟨hau.unit, by simpa using ha⟩

theorem partial_formallySmooth (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (hpos : ∀ k, 0 < e k) (he : ∀ k, IsUnit (e k : R)) :
    Algebra.FormallySmooth R (PartialAlgebra j e b) := by
  constructor
  intro B _ _ J hJ f
  have hJnil : IsNilpotent J := ⟨2, hJ⟩
  have hfree (i : ι) : ∃ w : Bˣ,
      Ideal.Quotient.mk J (w : B) = f (coordinate j e b i) :=
    lift_unit_mod_nilpotent J hJnil (Units.map f.toMonoidHom (coordinateUnit j e b i))
  choose free hfree using hfree
  have hfactor (k : κ) : ∃ g : SmoothPowerChart.PowerAlgebra R (e k) (b k) →ₐ[R] B,
      (Ideal.Quotient.mkₐ R J).comp g = f.comp (factorMap j e b k) := by
    letI := SmoothPowerChart.power_etale R (e k) (b k) (he k)
    exact (Algebra.FormallyEtale.comp_bijective (R := R)
      (A := SmoothPowerChart.PowerAlgebra R (e k) (b k)) J hJ).surjective _
  choose g hg using hfactor
  let selected : κ → Bˣ := fun k => Units.map (g k).toMonoidHom
    (SmoothPowerChart.root_isUnit R (e k) (b k) (hpos k)).unit
  have hselected (k : κ) : (selected k : B) =
      g k (SmoothPowerChart.root R (e k) (b k)) := by simp [selected]
  have hselected_mod (k : κ) : Ideal.Quotient.mk J (selected k : B) =
      f (coordinate j e b (j k)) := by
    rw [hselected]
    simpa only [AlgHom.comp_apply, factorMap_root] using
      AlgHom.congr_fun (hg k) (SmoothPowerChart.root R (e k) (b k))
  let x : ι → Bˣ := Function.extend j selected free
  have hx (k : κ) : (x (j k) : B) ^ e k = algebraMap R B (b k : R) := by
    rw [show x (j k) = selected k from j.injective.extend_apply selected free k,
      hselected, ← map_pow, SmoothPowerChart.root_power, AlgHom.commutes]
  have hxmod (i : ι) : Ideal.Quotient.mk J (x i : B) = f (coordinate j e b i) := by
    by_cases hi : ∃ k, j k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [show x (j k) = selected k from j.injective.extend_apply selected free k]
      exact hselected_mod k
    · rw [show x i = free i from Function.extend_apply' selected free i hi]
      exact hfree i
  refine ⟨lift j e b x hx, ?_⟩
  apply hom_ext j e b
  intro i
  rw [AlgHom.comp_apply, lift_coordinate]
  exact hxmod i

theorem partial_finitePresentation [Finite κ] [Algebra.FinitePresentation R (Laurent R ι)]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) :
    Algebra.FinitePresentation R (PartialAlgebra j e b) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

theorem partial_smooth [Finite κ] [Algebra.FinitePresentation R (Laurent R ι)]
    (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ)
    (hpos : ∀ k, 0 < e k) (he : ∀ k, IsUnit (e k : R)) :
    Algebra.Smooth R (PartialAlgebra j e b) where
  formallySmooth := partial_formallySmooth j e b hpos he
  finitePresentation := partial_finitePresentation j e b

theorem relations_eq_positiveIdeal {n : ℕ} (j : Fin n ↪ ι) (e : Fin n → ℕ)
    (b : Fin n → Rˣ) : relations j e b = SmithCharacters.positiveIdeal j e b := rfl

#print axioms relations
#print axioms PartialAlgebra
#print axioms coordinate
#print axioms coordinate_power
#print axioms coordinateUnit
#print axioms coordinateUnit_val
#print axioms hom_ext
#print axioms evaluateUnits
#print axioms evaluateUnits_coordinate
#print axioms lift
#print axioms lift_coordinate
#print axioms factorMap
#print axioms factorMap_root
#print axioms lift_unit_mod_nilpotent
#print axioms partial_formallySmooth
#print axioms partial_finitePresentation
#print axioms partial_smooth
#print axioms relations_eq_positiveIdeal
end Verification.PartialPowerSmooth
