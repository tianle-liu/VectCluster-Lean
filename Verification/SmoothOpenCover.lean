/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeOpenCover
import Mathlib.RingTheory.Smooth.Locus

/-!
# Smooth Open Cover

Smoothness descends from the proved independent-set basic-open cover.
The conclusion is mathlib's actual Algebra.Smooth; the proof uses its
smooth locus, not the differently defined scheme standard-smooth predicate.
-/
noncomputable section
universe u
namespace Verification.SmoothOpenCover
open Verification.ExchangeOpenCover Verification.ExchangeGeometry
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FinitePresentation R A]

theorem smooth_of_basicOpen_cover {ι : Type*} (f : ι → A)
    (hcover : (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤)
    (hsmooth : ∀ i, Algebra.Smooth R (Localization.Away (f i))) : Algebra.Smooth R A := by
  have hlocal : Algebra.smoothLocus R A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    have hp : p ∈ (⨆ i, PrimeSpectrum.basicOpen (f i)) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr (hsmooth i)) hi
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hlocal, inferInstance⟩

theorem smooth_of_independent_charts {n : ℕ}
    (v : Fin n → Fin n → ℕ) (x : Fin n → A)
    (hunit : ∀ i j, ExchangeRing.Adjacent v i j → Ideal.span ({x i, x j} : Set A) = ⊤)
    (hsmooth : ∀ I : {I : Finset (Fin n) // Independent v I},
      Algebra.Smooth R (Localization.Away (chartElement x I.1))) : Algebra.Smooth R A :=
  smooth_of_basicOpen_cover R A (fun I : {I : Finset (Fin n) // Independent v I} => chartElement x I.1)
    (independent_charts_cover v x hunit) hsmooth

theorem exchange_smooth_of_charts {n : ℕ}
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → A)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, IsUnit (c i)) (he : ExchangeEquations u v x y c d)
    (hsmooth : ∀ I : {I : Finset (Fin n) // Independent v I},
      Algebra.Smooth R (Localization.Away (chartElement x I.1))) : Algebra.Smooth R A :=
  smooth_of_basicOpen_cover R A (fun I : {I : Finset (Fin n) // Independent v I} => chartElement x I.1)
    (exchange_charts_cover u v x y c d hsupport hc he) hsmooth

#print axioms smooth_of_basicOpen_cover
#print axioms smooth_of_independent_charts
#print axioms exchange_smooth_of_charts
end Verification.SmoothOpenCover
