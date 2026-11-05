/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DiagonalHomology
import Verification.SeparatedHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Scalar Block Complex

A genuine complex of independent scalar blocks, with its actual degreewise
categorical homology. Incoming cokernels are in degree n; outgoing kernels
are indexed by the pairs whose targets are in degree n+1.
-/

noncomputable section
namespace Verification.ScalarBlockComplex
open CategoryTheory
open Verification.DiagonalHomology

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable {I K : ℤ → Type} (e : ∀ n, I n ↪ K n)
variable (a : ∀ n, I n → Module.End R M)

abbrev Term (n : ℤ) := (K n → M) × (I (n+1) → M)

def differential (n : ℤ) : Term (M := M) (I := I) (K := K) n →ₗ[R]
    Term (M := M) (I := I) (K := K) (n+1) :=
  ((diagonal (e (n+1)) (a (n+1))).comp (LinearMap.snd R _ _)).prod 0

theorem differential_apply (n : ℤ) (z : Term (M := M) (I := I) (K := K) n) :
    differential e a n z = (diagonal (e (n+1)) (a (n+1)) z.2,0) := rfl

theorem differential_square (n : ℤ) :
    (differential e a (n+1)).comp (differential e a n) = 0 := by
  ext z j <;> simp [differential_apply]

def complex : CochainComplex (ModuleCat.{0} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (Term (M := M) (I := I) (K := K) n))
    (fun n => ModuleCat.ofHom (differential e a n)) (by
      intro n
      exact ModuleCat.hom_ext (differential_square e a n))

theorem complex_d (n : ℤ) : (complex e a).d n (n+1) = ModuleCat.ofHom (differential e a n) :=
  CochainComplex.of_d _ _ _ _

def degreeShortComplex (n : ℤ) : ShortComplex (ModuleCat R) :=
  (complex e a).sc' (n-1) n (n+1)

theorem cycle_outgoing (n : ℤ) (z : LinearMap.ker (degreeShortComplex e a n).g.hom) :
    diagonal (e (n+1)) (a (n+1)) z.val.2 = 0 := by
  have h := z.property
  change (complex e a).d n (n+1) z.val = 0 at h
  rw [complex_d] at h
  exact congrArg Prod.fst h

def cycleProjection (n : ℤ) : LinearMap.ker (degreeShortComplex e a n).g.hom →ₗ[R]
    ((K n → M) ⧸ LinearMap.range (diagonal (e n) (a n))) ×
      LinearMap.ker (diagonal (e (n+1)) (a (n+1))) where
  toFun z := ((LinearMap.range (diagonal (e n) (a n))).mkQ z.val.1,
    ⟨z.val.2,cycle_outgoing e a n z⟩)
  map_add' x y := by
    apply Prod.ext
    · exact map_add (LinearMap.range (diagonal (e n) (a n))).mkQ x.val.1 y.val.1
    · apply Subtype.ext; rfl
  map_smul' r x := by
    apply Prod.ext
    · exact map_smul (LinearMap.range (diagonal (e n) (a n))).mkQ r x.val.1
    · apply Subtype.ext; rfl

theorem cycleProjection_surjective (n : ℤ) : Function.Surjective (cycleProjection e a n) := by
  rintro ⟨x,y⟩
  obtain ⟨x,hx⟩ := (LinearMap.range (diagonal (e n) (a n))).mkQ_surjective x
  refine ⟨⟨(x,y.val),?_⟩, Prod.ext hx rfl⟩
  change (complex e a).d n (n+1) (x,y.val)=0
  rw [complex_d]
  exact Prod.ext y.property rfl

theorem incoming_range (n : ℤ) (x : (degreeShortComplex e a n).X₂) :
    (∃ y, (degreeShortComplex e a n).f y=x) ↔
      x.1 ∈ LinearMap.range (diagonal (e n) (a n)) ∧ x.2=0 := by
  change (∃ y : Term (M := M) (I := I) (K := K) (n-1),
    (complex e a).d (n-1) n y=x) ↔ _
  generalize hk : n-1 = m
  have hn : m+1=n := by omega
  subst n
  constructor
  · rintro ⟨y,hy⟩
    rw [complex_d] at hy
    exact ⟨⟨y.2, congrArg Prod.fst hy⟩, (congrArg Prod.snd hy).symm⟩
  · rintro ⟨⟨y,hy⟩,hz⟩
    refine ⟨(0,y),?_⟩
    rw [complex_d]
    exact Prod.ext hy hz.symm

theorem cycleProjection_kernel (n : ℤ) :
    LinearMap.ker (cycleProjection e a n) =
      LinearMap.range (degreeShortComplex e a n).moduleCatToCycles := by
  ext z
  constructor
  · intro hz
    have h1 := (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.fst hz)
    have h2 : z.val.2=0 := congrArg (fun x => x.2.val) hz
    obtain ⟨y,hy⟩ := (incoming_range e a n z.val).mpr ⟨h1,h2⟩
    exact ⟨y,Subtype.ext hy⟩
  · rintro ⟨y,rfl⟩
    have h := (incoming_range e a n ((degreeShortComplex e a n).f y)).mp ⟨y,rfl⟩
    apply Prod.ext
    · exact (Submodule.Quotient.mk_eq_zero _).mpr h.1
    · exact Subtype.ext h.2

def separatedEquiv (n : ℤ) : (degreeShortComplex e a n).moduleCatHomology ≃ₗ[R]
    ((K n → M) ⧸ LinearMap.range (diagonal (e n) (a n))) ×
      LinearMap.ker (diagonal (e (n+1)) (a (n+1))) :=
  (Submodule.quotEquivOfEq _ _ (cycleProjection_kernel e a n).symm).trans
    ((cycleProjection e a n).quotKerEquivOfSurjective (cycleProjection_surjective e a n))

abbrev HomologyTerms (n : ℤ) :=
  ((Unmatched (e n) → M) × (∀ i : I n, M ⧸ LinearMap.range (a n i))) ×
    (∀ i : I (n+1), LinearMap.ker (a (n+1) i))

/-- Actual degreewise homology: singletons, incoming cokernels, outgoing kernels. -/
def homologyIso (n : ℤ) : (complex e a).homology n ≅ ModuleCat.of R (HomologyTerms e a n) :=
  (complex e a).homologyIsoSc' (n-1) n (n+1) (by simp) (by simp) ≪≫
    (degreeShortComplex e a n).moduleCatHomologyIso ≪≫
    ((separatedEquiv e a n).trans
      (LinearEquiv.prodCongr (cokernelEquiv (e n) (a n))
        (kernelEquiv (e (n+1)) (a (n+1))))).toModuleIso

#print axioms Term
#print axioms differential
#print axioms differential_apply
#print axioms differential_square
#print axioms complex
#print axioms complex_d
#print axioms degreeShortComplex
#print axioms cycle_outgoing
#print axioms cycleProjection
#print axioms cycleProjection_surjective
#print axioms incoming_range
#print axioms cycleProjection_kernel
#print axioms separatedEquiv
#print axioms HomologyTerms
#print axioms homologyIso

end Verification.ScalarBlockComplex
