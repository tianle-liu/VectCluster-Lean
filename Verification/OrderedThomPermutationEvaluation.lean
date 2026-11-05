/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedThomEvaluation
import Verification.ThomPermutationInput

/-!
# Ordered Thom Permutation Evaluation

The ordinary permutation degree formula transported to the explicit
integer degree used by numbered coefficient tests.
-/
noncomputable section
namespace Verification.OrderedThomPermutationEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]
variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (S : Type) [CommRing S] [Algebra R S] (r : ℕ)

omit [J.Additive] [L.Additive] in
theorem degree_permutation (ι : Type) [Fintype ι] [DecidableEq ι] (hr : Fintype.card ι = r)
    (hs : Algebra.Smooth R S) (e : Equiv.Perm ι) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S ι) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomEvaluation.degreeEvaluation J L G R site M N V S r ι hr hs j
      (L.map (ThomPermutationInput.permutationIso G S ι e).hom ≫ a) =
    O.orientation S (j-r) (Equiv.Perm.sign e)
      (OrderedThomEvaluation.degreeEvaluation J L G R site M N V S r ι hr hs j a) := by
  cases hr
  exact O.permutation S ι hs e j a

omit [J.Additive] [L.Additive] in
theorem fin_permutation (hs : Algebra.Smooth R S) (e : Equiv.Perm (Fin r)) (j : ℤ)
    (a : L.obj (LocalizedThomSections.thom G S (Fin r)) ⟶
      J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(r : ℤ)) (M j)))) :
    OrderedThomEvaluation.finEvaluate J L G R site M N V S r hs j
      (L.map (ThomPermutationInput.permutationIso G S (Fin r) e).hom ≫ a) =
    O.orientation S (j-r) (Equiv.Perm.sign e)
      (OrderedThomEvaluation.finEvaluate J L G R site M N V S r hs j a) := by
  simp only [OrderedThomEvaluation.finEvaluate,OrderedThomEvaluation.rewrite_eq_degree]
  exact degree_permutation J L G R site M N V O S r (Fin r) (Fintype.card_fin r) hs e j a

#print axioms degree_permutation
#print axioms fin_permutation
end Verification.OrderedThomPermutationEvaluation
