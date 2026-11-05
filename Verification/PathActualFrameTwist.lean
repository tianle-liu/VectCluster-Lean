/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualNormalWordFaces
import Verification.PathNormalSignTwist

/-!
# Path Actual Frame Twist

The original-normal sign is removed on actual section vectors by the
explicit four-periodic stratum change of basis, retaining the full rho terms.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathActualFrameTwist
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedFaceUnits
open Verification.PathMilnorWittCoefficients Verification.PathNormalizedBasis Verification.PathEndpointWords
open Verification.MilnorWittSymbolRelations

variable {A : Type*} [Ring A] (D : Coefficients A)

def factor (I : Finset ℕ) : A :=
  realize D (PathNormalSignTwist.factor PathCoefficientRing.g (fun j => j/2) I)

theorem factor_square (I : Finset ℕ) : factor D I*factor D I=1 := by
  rw [factor,←map_mul,PathNormalSignTwist.factor_square _ _ PathCoefficientRing.g_square,map_one]

def twist {ι : Type*} (I : Finset ℕ) : (ι → A) ≃+ (ι → A) where
  toFun f i := factor D I*f i
  invFun f i := factor D I*f i
  left_inv f := by funext i;simp only [←mul_assoc,factor_square,one_mul]
  right_inv f := by funext i;simp only [←mul_assoc,factor_square,one_mul]
  map_add' f g := by funext i;exact mul_add _ _ _

theorem adjacent (I : Finset ℕ) (j : ℕ) (hj : j∉I) (c : PathCoefficientRing.Coeff) (x : A) :
    factor D (insert j I)*(D.g^(j/2)*realize D c*(factor D I*x))=realize D c*x := by
  let g := PathCoefficientRing.g
  let w := fun j : ℕ => j/2
  have hg : g^(j/2)*g^(j/2)=1 := by rw [←mul_pow];simp only [g,PathCoefficientRing.g_square,one_pow]
  have he : PathNormalSignTwist.factor g w (insert j I)*g^(j/2)*c*PathNormalSignTwist.factor g w I=c := by
    rw [PathNormalSignTwist.factor_insert g w I j hj]
    dsimp only [w]
    calc
      _ = (g^(j/2)*g^(j/2))*(PathNormalSignTwist.factor g w I*PathNormalSignTwist.factor g w I)*c := by ring
      _ = c := by rw [hg,PathNormalSignTwist.factor_square _ _ PathCoefficientRing.g_square];simp only [one_mul]
  have hh := congrArg (fun a => realize D a*x) he
  simpa only [factor,map_mul,map_pow,realize_g,mul_assoc,g,w] using hh

section Actual
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N W K)
local notation "DR" => W.symbols (CommRingCat.of R)
include P

theorem y_face {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
    (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
    (f : NormalWord BothNormal (available I (2*d+2)).card → W.Total (CommRingCat.of R))
    (k : NormalWord BothNormal (available (insert j I) (2*d+2)).card) :
    twist (DR).toCoefficients (insert j I)
      (PathActualNormalWordFaces.yFace R hI j hj ha site N W K (twist (DR).toCoefficients I f)) k=
      ∑ i:NormalWord BothNormal (available I (2*d+2)).card,
        realize (DR).toCoefficients
          ((PathLeftEndpoint.projection 0
            (PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho (2*d)
              (faceIndex I j) i.val)) k.val)*f i := by
  change factor (DR).toCoefficients (insert j I)*
    (PathActualNormalWordFaces.yFace R hI j hj ha site N W K (fun i => factor (DR).toCoefficients I*f i) k)=_
  rw [PathActualNormalWordFaces.y_apply R hI j hj ha site N W K P,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => adjacent (DR).toCoefficients I j
    (fun hh => ha.1 (Finset.mem_union_left _ hh)) _ (f i))

theorem z_face {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
    (f : NormalWord RightNormal (available I (n+2)).card → W.Total (CommRingCat.of R))
    (k : NormalWord RightNormal (available (insert j I) (n+2)).card) :
    twist (DR).toCoefficients (insert j I)
      (PathActualNormalWordFaces.zFace R hI j hj ha site N W K (twist (DR).toCoefficients I f)) k=
      ∑ i:NormalWord RightNormal (available I (n+2)).card,
        realize (DR).toCoefficients
          ((PathLiteralEntries.projectedFace PathCoefficientRing.g PathCoefficientRing.rho n
            (faceIndex I j) i.val) k.val)*f i := by
  change factor (DR).toCoefficients (insert j I)*
    (PathActualNormalWordFaces.zFace R hI j hj ha site N W K (fun i => factor (DR).toCoefficients I*f i) k)=_
  rw [PathActualNormalWordFaces.z_apply R hI j hj ha site N W K P,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => adjacent (DR).toCoefficients I j
    (fun hh => ha.1 (Finset.mem_union_left _ hh)) _ (f i))
end Actual

#print axioms factor
#print axioms factor_square
#print axioms twist
#print axioms adjacent
#print axioms y_face
#print axioms z_face
end Verification.PathActualFrameTwist
