/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PureDegreeSurvivors

/-!
# Contraction Projection Support

Vanishing actual homology forces the actual normalized survivor projector
to have zero coefficients in that degree.
-/

namespace Verification.ContractionProjectionSupport

open CategoryTheory CategoryTheory.Limits Verification.FinitePerturbation
  Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.PureDegreeSurvivors

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem projection_row_zero (d : ι → ℤ) (D H : Matrix ι ι R)
    (hd : Homogeneous d 1 D) (hh : Homogeneous d (-1) H)
    (hD : D*D=0) (hH : H*H=0) (hHDH : H*D*H=H) (hDHD : D*H*D=D)
    (p : ℤ) (hz : IsZero ((matrixComplex d D hd hD).homology p))
    (i j : ι) (hi : d i=p) : pureProjection D H i j=0 := by
  let P := pureProjection D H
  have hp : Homogeneous d 0 P := projection_degree d D H hd hh
  by_cases hj : d j=p
  · have hv : Pi.single j (1:R) ∈ degreeModule d p := by
      intro k hk
      have hkj : k ≠ j := by intro he; apply hk; rw [he]; exact hj
      exact Pi.single_eq_of_ne hkj 1
    let x : fixedModule d P p := ⟨P.mulVec (Pi.single j 1),
      (matrixDegreeMap d P 0 hp p p (by omega) ⟨Pi.single j 1,hv⟩).property,by
        rw [Matrix.mulVec_mulVec,pureProjection_square D H hD hH hHDH hDHD]⟩
    have hxz : IsZero (ModuleCat.of R (fixedModule d P p)) :=
      (pureHomologyIso d D H hd hh hD hH hHDH hDHD p).isZero_iff.mp hz
    have hx : x=0 := congrArg (fun f : ModuleCat.of R (fixedModule d P p) ⟶
        ModuleCat.of R (fixedModule d P p) => f x) (hxz.eq_of_src (𝟙 _) 0)
    have he := congrArg (fun z : fixedModule d P p => z.val i) hx
    change (P.mulVec (Pi.single j 1)) i=0 at he
    rw [Matrix.mulVec_single_one] at he
    exact he
  · exact hp i j (by omega)

#print axioms projection_row_zero

end Verification.ContractionProjectionSupport
