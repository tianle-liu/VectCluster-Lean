/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AmbientPostnikovStages
import Verification.BundleCohomologicalRange

/-!
# Strict Model Bundle Range

The bundle-range conclusion from an actual strict model. Cited
Postnikov data concerns ambient mapping groups; all passage to the
article's coefficient cochains and their dimension bound is internal.
-/
noncomputable section
namespace Verification.StrictModelBundleRange
open CategoryTheory Verification.ActualProjectiveSplitting
universe w v u v' u'
variable {R : Type} [CommRing R] [IsDomain R]
variable (Det : DeterminantStandardInput.Standard R) (N : OrientedLineStabilization.Naturality Det)
variable (k : Type) [Field k] [Algebra R k]
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
variable {J : DerivedCategory A ⥤ D} [J.Additive] {X : D}
variable (H : StrictCoefficientComparison.StandardHomology (A := A))
variable (P : StrictProjectiveModel.Model J X) (hp : P.complex.IsStrictlyLE 0)
variable {h : ℕ} (hb : P.complex.IsStrictlyGE (-(h : ℤ)))
variable (S : ∀ r,2≤r → AmbientPostnikovStages.StabilizationStages Det N J X r)
variable (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))

include H hp hb S hk in
theorem free_above (E : Bundle R) {r : ℕ} (hr : HasRank E r) (hh : h<r) : Trivial E :=
  BundleCohomologicalRange.free_above Det N k A (StrictCoefficientCochains.complex P.complex)
    (fun r hr => AmbientPostnikovStages.stabilizationForModel Det N H P hp r (S r hr))
    hk (AmbientPostnikovStages.above P hb) E hr hh

include H hp hb S hk in
theorem one_line_stable (hh : h≤2) (E : Bundle R) (hr : HasRank E 2) :
    Nonempty ((E.object × R) ≃ₗ[R] (Fin 3 → R)) :=
  BundleCohomologicalRange.one_line_stable Det N k A (StrictCoefficientCochains.complex P.complex)
    (fun r hr => AmbientPostnikovStages.stabilizationForModel Det N H P hp r (S r hr))
    hk (AmbientPostnikovStages.above P hb) hh E hr

include H hp hb S hk in
theorem all_free (hh : h≤1) (E : Bundle R) : Trivial E :=
  BundleCohomologicalRange.all_free Det N k A (StrictCoefficientCochains.complex P.complex)
    (fun r hr => AmbientPostnikovStages.stabilizationForModel Det N H P hp r (S r hr))
    hk (AmbientPostnikovStages.above P hb) hh E

#print axioms free_above
#print axioms one_line_stable
#print axioms all_free
end Verification.StrictModelBundleRange
