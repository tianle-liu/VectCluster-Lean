/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstCofaces
import Verification.PathNormalBasisCoefficients
import Verification.PathZeroEndpointCoefficients

/-!
# Path Actual First Entries

Literal entries of the actual Y/Z first chain boundary at rho=0.
The matrices were defined from the full independent-stratum differential.
-/

namespace Verification.PathActualFirstEntries

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoFinite
  Verification.PathRhoWords Verification.PathRhoConfiguration Verification.PathFirstCofaces
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathEndpointCoordinates
  Verification.PathNormalBasisCoefficients Verification.PathZeroEndpointCoefficients

variable {R : Type*} [CommRing R]

def zeroConfig (n : ℕ) : Config n := ⟨∅,by simp [Admissible]⟩

def oneConfig (n j : ℕ) (hj : j ∈ Finset.Icc 1 n) : Config n :=
  ⟨{j},admissible_insert (zeroConfig n).property j hj (by simp [Addable,deleted,zeroConfig])⟩

theorem erase_one (n j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
    eraseConfig (oneConfig n j hj) j=zeroConfig n := by
  apply Subtype.ext
  simp only [eraseConfig,oneConfig,zeroConfig,Finset.erase_singleton]

theorem faceMap_empty (g ρ : R) (j : ℕ) : faceMap g ρ ∅ j=face (-g) ρ (j-1) := by
  simp [faceMap,incidence,rank,faceIndex,coordinate,available,deleted]

theorem differential_one (g ρ : R) (n j : ℕ) (hj : j ∈ Finset.Icc 1 n)
    (x : Total (R := R) n) :
    ((differential g ρ n x) (oneConfig n j hj)).val=
      face (-g) ρ (j-1) (x (zeroConfig n)).val := by
  change ambientDifferential g ρ n (inclusion n x) (oneConfig n j hj)=_
  rw [ambientDifferential_apply]
  change (∑ k ∈ ({j} : Finset ℕ),faceMap g ρ (eraseConfig (oneConfig n j hj) k).val k
    (x (eraseConfig (oneConfig n j hj) k)).val)=_
  rw [Finset.sum_singleton,erase_one]
  change faceMap g ρ ∅ j (x (zeroConfig n)).val=_
  rw [faceMap_empty]

theorem zero_length (n : ℕ) : (available (zeroConfig n).val (n+2)).card=n+2 := by
  simp [zeroConfig,available,deleted]

theorem one_length (n j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
    (available (oneConfig n j hj).val (n+2)).card=n := by
  have hh := available_card (oneConfig n j hj).property
  have hc : (oneConfig n j hj).val.card=1 := Finset.card_singleton j
  rw [hc] at hh
  omega

/-- This is an entry of the literal first chain matrix, expressed by its computed transpose column. -/
theorem z_first_entry (g : R) (n j : ℕ) (hj : j ∈ Finset.Icc 1 n)
    (u : NormalWord RightNormal (available (zeroConfig n).val (n+2)).card)
    (v : NormalWord RightNormal (available (oneConfig n j hj).val (n+2)).card) :
    zMatrix g 0 n ⟨oneConfig n j hj,v⟩ ⟨zeroConfig n,u⟩=
      cofaceColumn (-g) 0 (j-1) v.val u.val := by
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=⟨zeroConfig n,u⟩ then (1 : R) else 0)=
    Pi.single ⟨zeroConfig n,u⟩ 1 by funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply]
  change Verification.PathRightEndpoint.projection (Verification.PathEndpointComplex.endpointConstant 0 n)
    ((differential g 0 n ((zCoefficients 0 n).symm (Pi.single ⟨zeroConfig n,u⟩ 1)).val)
      (oneConfig n j hj)).val v.val=_
  rw [endpointConstant_zero,right_zero_coefficient v.val v.property.2,differential_one,
    zCoefficients_inverse_word,face_single]
  exact coface_adjoint (-g) 0 (j-1) u.val v.val

theorem y_first_entry (g : R) (a j : ℕ) (hj : j ∈ Finset.Icc 1 (2*a))
    (u : NormalWord BothNormal (available (zeroConfig (2*a)).val (2*a+2)).card)
    (v : NormalWord BothNormal (available (oneConfig (2*a) j hj).val (2*a+2)).card) :
    yMatrix g 0 a ⟨oneConfig (2*a) j hj,v⟩ ⟨zeroConfig (2*a),u⟩=
      cofaceColumn (-g) 0 (j-1) v.val u.val := by
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=⟨zeroConfig (2*a),u⟩ then (1 : R) else 0)=
    Pi.single ⟨zeroConfig (2*a),u⟩ 1 by funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply]
  change Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (Verification.PathEndpointComplex.endpointConstant 0 (2*a))
      ((differential g 0 (2*a) ((yCoefficients 0 a).symm (Pi.single ⟨zeroConfig (2*a),u⟩ 1)).val)
        (oneConfig (2*a) j hj)).val) v.val=_
  rw [endpointConstant_zero,left_zero_coefficient v.val v.property.2.1,
    right_zero_coefficient v.val v.property.2.2,differential_one,yCoefficients_inverse_word,face_single]
  exact coface_adjoint (-g) 0 (j-1) u.val v.val

#print axioms zeroConfig
#print axioms oneConfig
#print axioms erase_one
#print axioms faceMap_empty
#print axioms differential_one
#print axioms zero_length
#print axioms one_length
#print axioms z_first_entry
#print axioms y_first_entry

end Verification.PathActualFirstEntries
