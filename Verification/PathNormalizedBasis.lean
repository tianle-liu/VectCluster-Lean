/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointComplex
import Verification.PathEndpointWords

/-!
# Path Normalized Basis

A finite basis for the actual endpoint images, obtained from literal
normalized words rather than from projectivity of an idempotent image.
-/

namespace Verification.PathNormalizedBasis

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoFinite

variable {R : Type*} [CommRing R]

abbrev NormalWord (B : List Bool → Prop) (n : ℕ) := {w : List Bool // w.length=n ∧ B w}

noncomputable instance normalWordFintype (B : List Bool → Prop) (n : ℕ) : Fintype (NormalWord B n) := by
  letI := wordFintype n
  exact Fintype.ofInjective (fun w : NormalWord B n => (⟨w.val,w.property.1⟩ : Word n))
    (fun _ _ h => Subtype.ext (congrArg (fun z : Word n => z.val) h))

def normalLayer (B : List Bool → Prop) (n : ℕ) : Submodule R (List Bool →₀ R) :=
  Finsupp.supported R R {w | w.length=n ∧ B w}

abbrev NormalTotal (B : List Bool → Prop) (n : ℕ) :=
  ∀ I : Config n, normalLayer (R := R) B (available I.val (n+2)).card

abbrev NormalIndex (B : List Bool → Prop) (n : ℕ) :=
  Σ I : Config n, NormalWord B (available I.val (n+2)).card

noncomputable def normalCoordinates (B : List Bool → Prop) (n : ℕ) :
    NormalTotal (R := R) B n ≃ₗ[R] (NormalIndex B n → R) :=
  (LinearEquiv.piCongrRight (fun I : Config n =>
    (Finsupp.supportedEquivFinsupp (R := R) (M := R)
      {w : List Bool | w.length=(available I.val (n+2)).card ∧ B w}).trans
        (Finsupp.linearEquivFunOnFinite R R (NormalWord B (available I.val (n+2)).card)))).trans
          (LinearEquiv.piCurry R (fun (_ : Config n) (_ : NormalWord B _) => R)).symm

noncomputable def normalBasis (B : List Bool → Prop) (n : ℕ) :
    Basis (NormalIndex B n) R (NormalTotal (R := R) B n) :=
  (Pi.basisFun R (NormalIndex B n)).map (normalCoordinates B n).symm

theorem normalLayer_le (B : List Bool → Prop) (n : ℕ) :
    normalLayer (R := R) B n ≤ layer n := by
  apply Finsupp.supported_mono
  intro w hw
  exact hw.1

noncomputable def normalInclusion (B : List Bool → Prop) (n : ℕ) :
    NormalTotal (R := R) B n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun I => (Submodule.inclusion (normalLayer_le B (available I.val (n+2)).card)).comp
    (LinearMap.proj I))

variable (B : List Bool → Prop) (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))

/-- Columnwise support proves support for every vector in a source layer. -/
theorem normal_map (hmap : ∀ w, P (Finsupp.single w 1) ∈ normalLayer (R := R) B w.length)
    (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ layer (R := R) n) :
    P x ∈ normalLayer (R := R) B n := by
  have hh : layer (R := R) n ≤ (normalLayer B n).comap P := by
    rw [layer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change P (Finsupp.single w 1) ∈ normalLayer (R := R) B n
    change w.length=n at hw
    simpa only [hw] using hmap w
  exact hh hx

/-- Every normalized vector is fixed, proved from its actual word basis. -/
theorem normal_fixed (hfix : ∀ w, B w → P (Finsupp.single w 1)=Finsupp.single w 1)
    (n : ℕ) (x : List Bool →₀ R) (hx : x ∈ normalLayer (R := R) B n) : P x=x := by
  have hh : normalLayer (R := R) B n ≤ LinearMap.ker (P-LinearMap.id) := by
    rw [normalLayer,Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change P (Finsupp.single w 1)-Finsupp.single w 1=0
    exact sub_eq_zero.mpr (hfix w hw.2)
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hh hx))

/-- A coordinatewise literal projector has exactly the normalized finite basis. -/
noncomputable def rangeEquiv
    (hmap : ∀ w, P (Finsupp.single w 1) ∈ normalLayer (R := R) B w.length)
    (hfix : ∀ w, B w → P (Finsupp.single w 1)=Finsupp.single w 1)
    (n : ℕ) (T : Total (R := R) n →ₗ[R] Total (R := R) n)
    (ht : ∀ x I, (T x I).val=P (x I).val) :
    LinearMap.range T ≃ₗ[R] NormalTotal (R := R) B n where
  toFun x I := ⟨(x.val I).val,by
    obtain ⟨y,hy⟩ := x.property
    have he : (x.val I).val=P (y I).val := by rw [← hy]; exact ht y I
    rw [he]
    exact normal_map B P hmap _ _ (y I).property⟩
  invFun y := ⟨normalInclusion B n y,⟨normalInclusion B n y,by
    funext I
    apply Subtype.ext
    rw [ht]
    exact normal_fixed B P hfix _ (y I).val (y I).property⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext I
    rfl
  right_inv y := by
    funext I
    rfl
  map_add' x y := by
    funext I
    rfl
  map_smul' r x := by
    funext I
    rfl

noncomputable def rangeBasis
    (hmap : ∀ w, P (Finsupp.single w 1) ∈ normalLayer (R := R) B w.length)
    (hfix : ∀ w, B w → P (Finsupp.single w 1)=Finsupp.single w 1)
    (n : ℕ) (T : Total (R := R) n →ₗ[R] Total (R := R) n)
    (ht : ∀ x I, (T x I).val=P (x I).val) :
    Basis (NormalIndex B n) R (LinearMap.range T) :=
  (normalBasis B n).map (rangeEquiv B P hmap hfix n T ht).symm

#print axioms NormalWord
#print axioms normalWordFintype
#print axioms normalLayer
#print axioms NormalTotal
#print axioms NormalIndex
#print axioms normalCoordinates
#print axioms normalBasis
#print axioms normalLayer_le
#print axioms normalInclusion
#print axioms normal_map
#print axioms normal_fixed
#print axioms rangeEquiv
#print axioms rangeBasis

end Verification.PathNormalizedBasis
