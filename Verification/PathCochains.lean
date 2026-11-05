/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoConfiguration
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis

/-!
# Path Cochains

Actual finite free cochain modules indexed by independent zero sets and
minimal-coordinate binary words, with the full rho differential. Both outer
coordinates are retained here; constant-endpoint quotients are a further step.
-/

namespace Verification.PathCochains

open Classical Verification.PathCompression Verification.PathRhoWords
  Verification.PathRhoFinite Verification.PathRhoConfiguration

/-- Downward closure is proved directly from the literal path condition. -/
theorem admissible_mono {n : ℕ} {I J : Finset ℕ} (hI : Admissible n I) (hJ : J ⊆ I) :
    Admissible n J := ⟨hJ.trans hI.1,fun i hi hm => hI.2 i (hJ hi) (hJ hm)⟩

abbrev Config (n : ℕ) := {I : Finset ℕ // Admissible n I}

noncomputable instance configFintype (n : ℕ) : Fintype (Config n) :=
  Fintype.ofInjective (fun I : Config n =>
    (⟨I.val,Finset.mem_powerset.mpr I.property.1⟩ : ↥(Finset.Icc 1 n).powerset))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ↥(Finset.Icc 1 n).powerset => z.val) h))

def eraseConfig {n : ℕ} (I : Config n) (i : ℕ) : Config n :=
  ⟨I.val.erase i,admissible_mono I.property (Finset.erase_subset _ _)⟩

theorem eraseConfig_comm {n : ℕ} (I : Config n) (i j : ℕ) :
    eraseConfig (eraseConfig I i) j=eraseConfig (eraseConfig I j) i := by
  apply Subtype.ext
  ext k
  simp only [eraseConfig,Finset.mem_erase]
  tauto

noncomputable instance configWordFintype (n : ℕ) (I : Config n) :
    Fintype (Word (available I.val (n+2)).card) := wordFintype _

abbrev BasisIndex (n : ℕ) := Σ I : Config n, Word (available I.val (n+2)).card

variable {R : Type*} [CommRing R]

abbrev Total (n : ℕ) := ∀ I : Config n, layer (R := R) (available I.val (n+2)).card

abbrev Ambient (n : ℕ) := Config n → (List Bool →₀ R)

noncomputable def totalCoordinates (n : ℕ) : Total (R := R) n ≃ₗ[R] (BasisIndex n → R) :=
  (LinearEquiv.piCongrRight (fun I : Config n => (layerEquiv _).trans
    (Finsupp.linearEquivFunOnFinite R R (Word (available I.val (n+2)).card)))).trans
      (LinearEquiv.piCurry R (fun (_ : Config n) (_ : Word _) => R)).symm

noncomputable def totalBasis (n : ℕ) : Basis (BasisIndex n) R (Total (R := R) n) :=
  (Pi.basisFun R (BasisIndex n)).map (totalCoordinates n).symm

theorem total_free (n : ℕ) : Module.Free R (Total (R := R) n) :=
  Module.Free.of_basis (totalBasis n)

theorem total_finite (n : ℕ) : Module.Finite R (Total (R := R) n) :=
  Module.Finite.of_basis (totalBasis n)

noncomputable def inclusion (n : ℕ) : Total (R := R) n →ₗ[R] Ambient (R := R) n :=
  LinearMap.pi (fun I => (layer (available I.val (n+2)).card).subtype.comp (LinearMap.proj I))

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion (R := R) n) := by
  intro x y h
  funext I
  apply Subtype.ext
  exact congrFun h I

/-- Sum of the literal rho faces with the original zero-set normal-order incidence. -/
noncomputable def ambientDifferential (g ρ : R) (n : ℕ) : Ambient (R := R) n →ₗ[R] Ambient (R := R) n :=
  LinearMap.pi (fun J => ∑ j ∈ J.val,
    (faceMap g ρ (eraseConfig J j).val j).comp (LinearMap.proj (eraseConfig J j)))

theorem ambientDifferential_apply (g ρ : R) (n : ℕ) (x : Ambient (R := R) n) (J : Config n) :
    ambientDifferential g ρ n x J=∑ j ∈ J.val,faceMap g ρ (eraseConfig J j).val j (x (eraseConfig J j)) := by
  simp only [ambientDifferential,LinearMap.pi_apply,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply]

/-- The full differential really maps the specified minimal-coordinate finite free modules. -/
theorem differential_mem (g ρ : R) (n : ℕ) (x : Total (R := R) n) (J : Config n) :
    ambientDifferential g ρ n (inclusion n x) J ∈ layer (R := R) (available J.val (n+2)).card := by
  rw [ambientDifferential_apply]
  apply Submodule.sum_mem
  intro j hj
  have hsub : insert j (eraseConfig J j).val=J.val := Finset.insert_erase hj
  have hA : Admissible n (insert j (eraseConfig J j).val) := hsub.symm ▸ J.property
  have ha := addable_of_insert hA (Finset.not_mem_erase _ _)
  have hh := faceMap_mem_layer g ρ j (J.property.1 hj) ha (x (eraseConfig J j))
  rw [hsub] at hh
  exact hh

/-- The assembled original independent-zero-set rho operator on a genuine finite free module. -/
noncomputable def differential (g ρ : R) (n : ℕ) : Total (R := R) n →ₗ[R] Total (R := R) n :=
  LinearMap.pi (fun J => LinearMap.codRestrict _
    ((LinearMap.proj J).comp ((ambientDifferential g ρ n).comp (inclusion n)))
      (fun x => differential_mem g ρ n x J))

theorem differential_inclusion (g ρ : R) (n : ℕ) :
    (inclusion n).comp (differential g ρ n)=(ambientDifferential g ρ n).comp (inclusion n) := rfl

#print axioms admissible_mono
#print axioms Config
#print axioms configFintype
#print axioms eraseConfig
#print axioms eraseConfig_comm
#print axioms configWordFintype
#print axioms BasisIndex
#print axioms Total
#print axioms Ambient
#print axioms totalCoordinates
#print axioms totalBasis
#print axioms total_free
#print axioms total_finite
#print axioms inclusion
#print axioms inclusion_injective
#print axioms ambientDifferential
#print axioms ambientDifferential_apply
#print axioms differential_mem
#print axioms differential
#print axioms differential_inclusion

end Verification.PathCochains
