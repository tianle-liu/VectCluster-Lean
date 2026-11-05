/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOnePureBasis
import Verification.TwoDegreeInitialContraction

/-!
# Path One Pure Base

The genuine length-one Z initial complex contracts by its literal first
boundary, the proved rank-one/rank-four degree bases, and its rank-three H0.
-/

namespace Verification.PathOnePureBase

open Classical Verification.PathPureContractionData Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathFullComplex

variable {R : Type} [CommRing R]

noncomputable def zOne (g : R) (hg : g*g=1) :
    Data (fun x => -degree x) (zMatrix g 0 1).transpose :=
  Verification.TwoDegreeInitialContraction.initial _ _
    (transpose_degree _ _ (zMatrix_degree g 0 1))
    (transpose_square _ (zMatrix_squared g 0 1 hg (by simp)))
    Verification.PathOnePureBasis.degree_range Verification.PathOnePureBasis.firstBasis
    Verification.PathOnePureBasis.zeroBasis (Verification.PathFirstHomology.zHomologyBasis g hg 1) (by omega)

#print axioms zOne

end Verification.PathOnePureBase
