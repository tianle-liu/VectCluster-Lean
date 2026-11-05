/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRostUnitTerms
import Verification.RostComponentZero
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Rost Canonical Coefficients

Ordinary generic evaluation of K^M_0, together with the canonical
normalizations of the already chosen K^M_1, K^M_0 and finite-disjoint-union
comparisons. The input is uniform in rings and their actual prime spectra.
It contains no coordinate filtration or prescribed residue value.
-/
noncomputable section
namespace Verification.RostCanonicalCoefficients
open CategoryTheory AlgebraicGeometry
variable (T : RostAffineInput.Theory)

abbrev Sections (A : Type) [CommRing A] (s : ℤ) :=
  (T.cycles (Spec (CommRingCat.of A)) s).homology 0

def transport {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (s : ℤ) :
    Sections T A s ≃+ Sections T B s :=
  (T.iso (Scheme.Spec.mapIso e.toCommRingCatIso.symm.op) s 0).addCommGroupIsoToAddEquiv

def domainPoint (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum A :=
  ⟨⊥,Ideal.bot_prime⟩

theorem domainPoint_minimal (A : Type) [CommRing A] [IsDomain A] :
    (domainPoint A).asIdeal ∈ minimalPrimes A := by
  exact ⟨⟨Ideal.bot_prime,bot_le⟩,fun _ _ _ => bot_le⟩

def productPoint {J : Type} (R : J → Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
    (j : J) : PrimeSpectrum (∀ j,R j) :=
  PrimeSpectrum.comap (Pi.evalRingHom R j) (domainPoint (R j))

theorem productPoint_minimal {J : Type} (R : J → Type)
    [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)] (j : J) :
    (productPoint R j).asIdeal ∈ minimalPrimes (∀ j,R j) := by
  classical
  refine ⟨⟨(productPoint R j).isPrime,bot_le⟩,?_⟩
  intro Q hQ hle a ha
  change a j = 0 at ha
  have he : (Pi.single j (1 : R j)) ∉ Q := by
    intro h
    have h' := hle h
    change (Pi.single j (1 : R j)) j = 0 at h'
    simp only [Pi.single_eq_same,one_ne_zero] at h'
  have hm : a * Pi.single j (1 : R j) = 0 := by
    ext l
    by_cases h : l=j
    · subst l; simp [ha]
    · simp [Pi.single_eq_of_ne h]
  exact (hQ.1.mem_or_mem (hm ▸ Q.zero_mem)).resolve_right he

theorem transportPoint_minimal {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : PrimeSpectrum B) (hq : q.asIdeal ∈ minimalPrimes B) :
    (PrimeSpectrum.comap e.toRingHom q).asIdeal ∈ minimalPrimes A := by
  have h := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom) e.surjective hq
  have hb : Ideal.comap e.toRingHom (⊥ : Ideal B) = ⊥ := by
    ext a
    change e a = 0 ↔ a = 0
    exact e.map_eq_zero_iff
  change _ ∈ (Ideal.comap e.toRingHom (⊥ : Ideal B)).minimalPrimes at h
  rw [hb] at h
  exact h

variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)

/-- Ordinary values at the actual generic points, compatible with the
chosen ring-isomorphism and product comparisons. The hypotheses identifying
minimal primes are geometric obligations, not free component labels. -/
structure GenericZeroEvaluation where
  value : ∀ (A : Type) [CommRing A] (q : PrimeSpectrum A),
    q.asIdeal ∈ minimalPrimes A → (Sections T A 0 →+ ℤ)
  integral : ∀ (A : Type) [CommRing A] [IsDomain A] (a : Sections T A 0),
    value A (domainPoint A) (domainPoint_minimal A) a = (Z.zero A).hom a
  iso : ∀ (A B : Type) [CommRing A] [CommRing B] (e : A ≃+* B)
    (q : PrimeSpectrum B) (hq : q.asIdeal ∈ minimalPrimes B)
    (hp : (PrimeSpectrum.comap e.toRingHom q).asIdeal ∈ minimalPrimes A)
    (a : Sections T A 0),
    value B q hq (transport T e 0 a) = value A (PrimeSpectrum.comap e.toRingHom q) hp a
  product : ∀ (J : Type) [Fintype J] (R : J → Type)
    [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)] (j : J)
    (hq : (productPoint R j).asIdeal ∈ minimalPrimes (∀ j,R j))
    (a : Sections T (∀ j,R j) 0),
    value (∀ j,R j) (productPoint R j) hq a =
      (Z.zero (R j)).hom (F.product J R 0 0 a j)

variable (U : OriginalRostUnitTerms.UnitsConvention T)

/-- The usual K^M_1=units comparison respects actual ring isomorphisms
and projections of a finite product. It is not an arbitrary choice of bases. -/
structure UnitsNaturality : Prop where
  iso : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.Smooth k A] [Algebra.Smooth k B]
    (e : A ≃+* B) (a : Sections T A 1),
    (U.units k B).hom (transport T e 1 a) =
      Additive.ofMul (Units.map e.toMonoidHom (Additive.toMul ((U.units k A).hom a)))
  product : ∀ (k J : Type) [Field k] [Fintype J] (R : J → Type)
    [∀ j,CommRing (R j)] [∀ j,Algebra k (R j)] [∀ j,Algebra.Smooth k (R j)]
    [Algebra.Smooth k (∀ j,R j)] (a : Sections T (∀ j,R j) 1) (j : J),
    Units.map (Pi.evalRingHom R j).toMonoidHom
      (Additive.toMul ((U.units k (∀ j,R j)).hom a)) =
        Additive.toMul ((U.units k (R j)).hom (F.product J R 1 0 a j))

variable (E : GenericZeroEvaluation T F Z)

/-- The generic value of the transported product decomposition is fixed by
the ordinary inputs, rather than supplied as a paper-specific formula. -/
theorem transported_product_value {J : Type} [Fintype J]
    (R : J → Type) [∀ j,CommRing (R j)] [∀ j,IsDomain (R j)]
    {A : Type} [CommRing A] (e : A ≃+* ∀ j,R j) (j : J)
    (hq : (productPoint R j).asIdeal ∈ minimalPrimes (∀ j,R j))
    (hp : (PrimeSpectrum.comap e.toRingHom (productPoint R j)).asIdeal ∈ minimalPrimes A)
    (a : Sections T A 0) :
    E.value A (PrimeSpectrum.comap e.toRingHom (productPoint R j)) hp a =
      (Z.zero (R j)).hom (F.product J R 0 0 (transport T e 0 a) j) := by
  rw [← E.iso A (∀ j,R j) e (productPoint R j) hq hp a]
  exact E.product J R j hq _

#print axioms Sections
#print axioms transport
#print axioms domainPoint
#print axioms domainPoint_minimal
#print axioms productPoint
#print axioms productPoint_minimal
#print axioms transportPoint_minimal
#print axioms GenericZeroEvaluation
#print axioms UnitsNaturality
#print axioms transported_product_value
end Verification.RostCanonicalCoefficients
