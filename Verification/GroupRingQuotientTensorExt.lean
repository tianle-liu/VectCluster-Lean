/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittSectionCoordinates

/-!
# Group Ring Quotient Tensor Ext

Additive maps out of an integral group-ring quotient tensor product
are determined by the actual monomials with arbitrary coefficients.
-/
noncomputable section
open scoped TensorProduct
namespace Verification.GroupRingQuotientTensorExt
variable {G A M : Type*} [CommMonoid G] [AddCommGroup A] [AddCommGroup M]
variable (I : Ideal (MonoidAlgebra ℤ G))

theorem ext (f g : ((MonoidAlgebra ℤ G ⧸ I) ⊗[ℤ] A) →+ M)
    (h : ∀ (m : G) (a : A),
      f (Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G m) ⊗ₜ[ℤ] a)=
      g (Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G m) ⊗ₜ[ℤ] a)) : f=g := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x a =>
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add,TensorProduct.add_tmul,hx,hy]
    | single m z =>
      have hz : Finsupp.single m z = z • MonoidAlgebra.of ℤ G m := by
        simp [MonoidAlgebra.of_apply]
      rw [hz,map_zsmul,← TensorProduct.smul_tmul',map_zsmul,map_zsmul,h]

#print axioms ext
end Verification.GroupRingQuotientTensorExt
