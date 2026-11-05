/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCompression
import Verification.PathRhoFinite
import Mathlib.Tactic.LinearCombination

/-!
# Path Rho Configuration

The original independent zero-set incidence factor combined with the
proved compressed-coordinate rho faces.
-/

namespace Verification.PathRhoConfiguration

open Classical Verification.PathCompression Verification.PathRhoFaces
  Verification.PathRhoWords Verification.PathRhoFinite

variable {R : Type*} [CommRing R]

def rank (I : Finset ℕ) (j : ℕ) : ℕ := (I.filter (· < j)).card

def incidence (g : R) (I : Finset ℕ) (j : ℕ) : R := g^(rank I j)

theorem incidence_insert (g : R) (I : Finset ℕ) (i j : ℕ) (hj : j ∉ I) :
    incidence g (insert j I) i=if j < i then g*incidence g I i else incidence g I i := by
  by_cases hji : j < i
  · have hn : j ∉ I.filter (· < i) := by simp [hj]
    simp only [incidence,rank,Finset.filter_insert,hji,↓reduceIte,
      Finset.card_insert_of_not_mem hn,pow_succ]
    exact mul_comm _ _
  · simp only [incidence,rank,Finset.filter_insert,hji,↓reduceIte]

/-- The actual cochain face attached to adjoining zero vertex j to I. -/
noncomputable def faceMap (g ρ : R) (I : Finset ℕ) (j : ℕ) :
    (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  incidence g I j • face (-g) ρ (faceIndex I j)

theorem faceMap_mem_layer (g ρ : R) {n : ℕ} {I : Finset ℕ}
    (j : ℕ) (hj : j ∈ Finset.Icc 1 n) (ha : Addable I j)
    (x : layer (R := R) (available I (n+2)).card) :
    faceMap g ρ I j x.val ∈ layer (R := R) (available (insert j I) (n+2)).card := by
  have hcount := available_insert_card I j (n+2) ha (by have hh:=Finset.mem_Icc.mp hj; omega)
  have hh := face_mem_layer (-g) ρ (faceIndex I j) (available I (n+2)).card x.val x.property
  have he : (available I (n+2)).card-2=(available (insert j I) (n+2)).card := by omega
  rw [he] at hh
  exact (layer _).smul_mem (incidence g I j) hh

/-- Two arbitrary original independent zero vertices cancel after incidence and rho are included. -/
theorem configuration_pair_cancellation (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (i j : ℕ)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    (ha : Addable I i) (hb : Addable I j) (hij : i+2 ≤ j)
    (x : layer (R := R) (available I (n+2)).card) :
    faceMap g ρ (insert i I) j (faceMap g ρ I i x.val)+
      faceMap g ρ (insert j I) i (faceMap g ρ I j x.val)=0 := by
  obtain ⟨hε,hρ⟩ := epsilon_relations ρ g hg hr
  have hip : 0<coordinate I i := coordinate_positive hI (by have hh:=Finset.mem_Icc.mp hi; omega)
  have hsep := faceIndex_separated I i j ha hij hip
  have hvalid := faceIndex_valid hI j hj hb
  have hbraid := layer_braid (-g) ρ hε hρ (faceIndex I i) (faceIndex I j)
    (available I (n+2)).card hsep hvalid x
  have hiI : i ∉ I := fun h => ha.1 (Finset.mem_union_left _ h)
  have hjI : j ∉ I := fun h => hb.1 (Finset.mem_union_left _ h)
  simp only [faceMap,LinearMap.smul_apply,map_smul,smul_smul]
  rw [faceIndex_insert_after I i j ha hij,faceIndex_insert_before I j i (by omega),
    incidence_insert g I j i hiI,incidence_insert g I i j hjI]
  simp only [show i < j by omega,show ¬(j < i) by omega,↓reduceIte]
  rw [hbraid,smul_smul,← add_smul]
  have hs : (incidence g I i*(g*incidence g I j))*(-g)+incidence g I j*incidence g I i=0 := by
    linear_combination -(incidence g I i*incidence g I j)*hg
  rw [hs,zero_smul]

#print axioms rank
#print axioms incidence
#print axioms incidence_insert
#print axioms faceMap
#print axioms faceMap_mem_layer
#print axioms configuration_pair_cancellation

end Verification.PathRhoConfiguration
