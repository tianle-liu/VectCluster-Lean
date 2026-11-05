/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ContractionProjectionSupport
import Verification.PathFirstHomology

/-!
# Path Pure Contraction Data

Data maintained by the path induction: an actual normalized finite
contraction whose survivor projector is supported at chain degree zero.
The degree-zero basis comes from the previously proved original first boundary.
-/

namespace Verification.PathPureContractionData

open CategoryTheory Verification.FinitePerturbation Verification.GradedPerturbation
  Verification.PerturbedHomologyModel Verification.GradedIntegralSplitting
  Verification.PathFullComplex Verification.PathEndpointCoordinates Verification.PathStratumGrading

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

structure Data (d : ι → ℤ) (D : Matrix ι ι R) where
  differential_degree : Homogeneous d 1 D
  differential_square : D*D=0
  homotopy : Matrix ι ι R
  homotopy_degree : Homogeneous d (-1) homotopy
  homotopy_square : homotopy*homotopy=0
  homotopy_regular : homotopy*D*homotopy=homotopy
  generalized : D*homotopy*D=D
  supported : ∀ i j,d i ≠ 0 → pureProjection D homotopy i j=0

noncomputable def ofGeneralized (d : ι → ℤ) (D G : Matrix ι ι R)
    (hd : Homogeneous d 1 D) (hD : D*D=0) (hG : D*G*D=D)
    (hz : ∀ p : ℤ,p ≠ 0 → Limits.IsZero ((matrixComplex d D hd hD).homology p)) : Data d D := by
  have hW : Homogeneous (fun _ : ι => (0:ℤ)) 0 D := by intro i j hij; exact (hij rfl).elim
  let F := component d (fun _ => (0:ℤ)) (-1) G
  have hF : D*F*D=D := component_generalized d (fun _ => 0) D G hd hW hG
  let H := normalize D F
  have hH : H*H=0 := normalize_square D F hF
  have hHDH : H*D*H=H := normalize_regular D F hD hF
  have hDHD : D*H*D=D := normalize_generalized D F hD hF
  have hhd : Homogeneous d (-1) H := normalize_degree d D F hd (component_degree d (fun _ => 0) (-1) G)
  exact {
    differential_degree := hd
    differential_square := hD
    homotopy := H
    homotopy_degree := hhd
    homotopy_square := hH
    homotopy_regular := hHDH
    generalized := hDHD
    supported := fun i j hi => Verification.ContractionProjectionSupport.projection_row_zero
      d D H hd hhd hD hH hHDH hDHD (d i) (hz (d i) hi) i j rfl }

noncomputable def homologyBasis (d : ι → ℤ) (D : Matrix ι ι R) (T : Data d D)
    {α : Type} (b : Basis α R ((matrixComplex d D T.differential_degree T.differential_square).homology 0)) :
    Basis α R (fixedModule d (pureProjection D T.homotopy) 0) :=
  b.map (Verification.PureDegreeSurvivors.pureHomologyIso d D T.homotopy T.differential_degree
    T.homotopy_degree T.differential_square T.homotopy_square T.homotopy_regular T.generalized 0).toLinearEquiv

noncomputable def zBasis (g : R) (hg : g*g=1) (n : ℕ)
    (T : Data (fun x => -degree x) (zMatrix g 0 n).transpose) :
    Basis (Fin (n+2)) R (fixedModule (fun x => -degree x)
      (pureProjection (zMatrix g 0 n).transpose T.homotopy) 0) :=
  homologyBasis _ _ T (Verification.PathFirstHomology.zHomologyBasis g hg n)

noncomputable def yBasis (g : R) (hg : g*g=1) (m : ℕ)
    (T : Data (fun x => -degree x) (yMatrix g 0 m).transpose) :
    Basis (Fin (m+1)) R (fixedModule (fun x => -degree x)
      (pureProjection (yMatrix g 0 m).transpose T.homotopy) 0) :=
  homologyBasis _ _ T (Verification.PathFirstHomology.yHomologyBasis g hg m)

#print axioms Data
#print axioms ofGeneralized
#print axioms homologyBasis
#print axioms zBasis
#print axioms yBasis

end Verification.PathPureContractionData
