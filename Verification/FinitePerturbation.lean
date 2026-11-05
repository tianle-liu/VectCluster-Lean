/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ChainCancellation
import Verification.ComplexCancellation
import Mathlib.Tactic.NoncommRing

/-!
# Finite Perturbation

Finite perturbation of an explicitly split pure differential.  The identities
below construct the corrected maps; they do not assume a residual complex or
its homotopy equivalence.  Finite weight increase supplies the required inverses.
-/

namespace Verification.FinitePerturbation

section RingIdentities

variable {A : Type*} [Ring A]
variable (u h v : A)

theorem square_zero_suffix (a : A) (ha : a*a = 0) (b : A) : a*(a*b) = 0 := by
  rw [← mul_assoc, ha, zero_mul]

/-- Projection onto the zero-differential part of a chosen unit-pair splitting. -/
def pureProjection : A := 1 - u*h - h*u

variable (hu : u*u = 0) (hh : h*h = 0) (huh : h*u*h = h) (uhu : u*h*u = u)

include hu hh huh uhu in
theorem pureProjection_square : pureProjection u h * pureProjection u h = pureProjection u h := by
  have huh' : h*(u*h) = h := by simpa [mul_assoc] using huh
  have uhu' : u*(h*u) = u := by simpa [mul_assoc] using uhu
  noncomm_ring [pureProjection, hu, hh, huh', uhu', square_zero_suffix u hu, square_zero_suffix h hh]

include hu uhu in
theorem pureProjection_u : pureProjection u h * u = 0 := by
  noncomm_ring [pureProjection, hu, uhu]

include hu uhu in
theorem u_pureProjection : u * pureProjection u h = 0 := by
  have uhu' : u*(h*u) = u := by simpa [mul_assoc] using uhu
  noncomm_ring [pureProjection, hu, uhu', square_zero_suffix u hu]

include hh huh in
theorem pureProjection_h : pureProjection u h * h = 0 := by
  have huh' : h*(u*h) = h := by simpa [mul_assoc] using huh
  noncomm_ring [pureProjection, hh, huh', square_zero_suffix h hh]

include hh huh in
theorem h_pureProjection : h * pureProjection u h = 0 := by
  have huh' : h*(u*h) = h := by simpa [mul_assoc] using huh
  noncomm_ring [pureProjection, hh, huh', square_zero_suffix h hh]

variable (q l : Aˣ) (hq : (q : A) = 1 + v*h) (hl : (l : A) = 1 + h*v)

/-- The finite perturbation series, expressed by its constructed inverse. -/
def correction : A := q.inv * v

theorem correction_left : (q : A) * correction v q = v := by
  simp [correction, ← mul_assoc]

include hq hl in
theorem correction_right : correction v q * (l : A) = v := by
  have hv : (q : A)*v = v*(l : A) := by rw [hq, hl]; noncomm_ring
  rw [correction, mul_assoc, ← hv, ← mul_assoc, q.inv_val, one_mul]

include hq in
theorem correction_left_equation : correction v q = v - v*h*correction v q := by
  have he := correction_left v q
  rw [hq, add_mul, one_mul] at he
  exact (eq_sub_iff_add_eq).mpr he

include hq hl in
theorem correction_right_equation : correction v q = v - correction v q*h*v := by
  have he := correction_right h v q l hq hl
  rw [hl, mul_add, mul_one, ← mul_assoc] at he
  exact (eq_sub_iff_add_eq).mpr he

include hu hq hl in
/-- The perturbed square-zero identity rewritten on the chosen pure homology. -/
theorem correction_twisting (hd : (u+v)*(u+v) = 0) :
    u*correction v q + correction v q*u +
      correction v q*pureProjection u h*correction v q = 0 := by
  have hcL := correction_left v q
  have hcR := correction_right h v q l hq hl
  apply (Units.mul_right_inj q).mp
  apply (Units.mul_left_inj l).mp
  simp only [mul_zero, zero_mul]
  calc
    (q : A) * (u*correction v q + correction v q*u +
        correction v q*pureProjection u h*correction v q) * (l : A) =
        (q : A)*u*v + v*u*(l : A) + v*pureProjection u h*v := by
      simp only [mul_add, add_mul, mul_assoc]
      rw [hcR, ← mul_assoc (q : A) (correction v q), hcL]
      simp only [← mul_assoc]
      rw [hcL]
    _ = (u+v)*(u+v) - u*u := by rw [hq, hl]; noncomm_ring [pureProjection]
    _ = 0 := by rw [hd, hu, sub_self]

/-- Corrected degree-reversing contraction. -/
def correctedHomotopy : A := h - h*correction v q*h

/-- Corrected inclusion of the old pure-homology summand. -/
def correctedInclusion : A := pureProjection u h - h*correction v q*pureProjection u h

/-- Corrected retraction onto the old pure-homology summand. -/
def correctedRetraction : A := pureProjection u h - pureProjection u h*correction v q*h

/-- Residual boundary on the old pure-homology summand. -/
def residualDifferential : A := pureProjection u h*correction v q*pureProjection u h

theorem zero_mul_suffix (a b : A) (hab : a*b = 0) (x : A) : a*(b*x) = 0 := by
  rw [← mul_assoc, hab, zero_mul]

theorem idempotent_suffix (a : A) (ha : a*a = a) (x : A) : a*(a*x) = a*x := by
  rw [← mul_assoc, ha]

include hu hh huh uhu in
/-- The corrected retraction and inclusion cancel exactly on pure homology. -/
theorem corrected_retraction_inclusion :
    correctedRetraction u h v q * correctedInclusion u h v q = pureProjection u h := by
  have hpp := pureProjection_square u h hu hh huh uhu
  have hph := pureProjection_h u h hh huh
  have hhp := h_pureProjection u h hh huh
  noncomm_ring [correctedRetraction, correctedInclusion, hpp,
    idempotent_suffix _ hpp, hhp, zero_mul_suffix _ _ hph, zero_mul_suffix _ _ hhp,
    square_zero_suffix h hh]

include hu hh huh uhu in
/-- Product of the constructed maps, before applying the perturbation identity. -/
theorem corrected_inclusion_retraction_expansion :
    correctedInclusion u h v q * correctedRetraction u h v q =
      pureProjection u h - pureProjection u h*correction v q*h -
      h*correction v q*pureProjection u h +
      h*correction v q*pureProjection u h*correction v q*h := by
  have hpp := pureProjection_square u h hu hh huh uhu
  noncomm_ring [correctedRetraction, correctedInclusion, hpp, idempotent_suffix _ hpp]

include hu hh huh uhu hq hl in
/-- The constructed cancellation is witnessed by the explicit corrected homotopy. -/
theorem corrected_homotopy_identity (hd : (u+v)*(u+v) = 0) :
    correctedInclusion u h v q * correctedRetraction u h v q =
      1 - (u+v)*correctedHomotopy h v q - correctedHomotopy h v q*(u+v) := by
  have ht := correction_twisting u h v hu q l hq hl hd
  have hL : correction v q-v+v*h*correction v q = 0 := by
    calc
      correction v q-v+v*h*correction v q = correction v q-(v-v*h*correction v q) := by abel
      _ = 0 := sub_eq_zero.mpr (correction_left_equation h v q hq)
  have hR : correction v q-v+correction v q*h*v = 0 := by
    calc
      correction v q-v+correction v q*h*v = correction v q-(v-correction v q*h*v) := by abel
      _ = 0 := sub_eq_zero.mpr (correction_right_equation h v q l hq hl)
  apply sub_eq_zero.mp
  calc
    correctedInclusion u h v q * correctedRetraction u h v q -
        (1-(u+v)*correctedHomotopy h v q-correctedHomotopy h v q*(u+v)) =
        h*(u*correction v q+correction v q*u+
          correction v q*pureProjection u h*correction v q)*h -
        (correction v q-v+v*h*correction v q)*h -
        h*(correction v q-v+correction v q*h*v) := by
      rw [corrected_inclusion_retraction_expansion u h v hu hh huh uhu q]
      noncomm_ring [correctedHomotopy, pureProjection]
    _ = 0 := by rw [ht, hL, hR]; simp

include hu hh huh uhu hq hl in
/-- The independently constructed residual boundary squares to zero. -/
theorem residual_square (hd : (u+v)*(u+v) = 0) :
    residualDifferential u h v q * residualDifferential u h v q = 0 := by
  have hpp := pureProjection_square u h hu hh huh uhu
  have hpu := pureProjection_u u h hu uhu
  have hup := u_pureProjection u h hu uhu
  have ht := correction_twisting u h v hu q l hq hl hd
  calc
    residualDifferential u h v q * residualDifferential u h v q =
        pureProjection u h * (u*correction v q + correction v q*u +
          correction v q*pureProjection u h*correction v q) * pureProjection u h := by
      noncomm_ring [residualDifferential, hpp, idempotent_suffix _ hpp,
        hpu, hup, zero_mul_suffix _ _ hpu, zero_mul_suffix _ _ hup]
    _ = 0 := by rw [ht]; simp

include hu hh huh uhu hq hl in
/-- Corrected inclusion is a chain map for the actual residual differential. -/
theorem corrected_inclusion_chain (hd : (u+v)*(u+v) = 0) :
    (u+v)*correctedInclusion u h v q =
      correctedInclusion u h v q*residualDifferential u h v q := by
  let p := pureProjection u h
  let a := correction v q
  have hpp : p*p = p := pureProjection_square u h hu hh huh uhu
  have hup : u*p = 0 := u_pureProjection u h hu uhu
  have ht : u*a+a*u+a*p*a = 0 := correction_twisting u h v hu q l hq hl hd
  have hL : a = v-v*h*a := correction_left_equation h v q hq
  have he : h*u*a*p = -(h*a*p*a*p) := by
    apply eq_neg_of_add_eq_zero_left
    have hz := congrArg (fun x => h*x*p) ht
    simpa only [mul_add, add_mul, mul_assoc, hup, mul_zero, zero_mul, add_zero] using hz
  have ha : a-u*h*a = p*a+h*u*a := by dsimp [p]; noncomm_ring [pureProjection]
  calc
    (u+v)*correctedInclusion u h v q = (v-v*h*a-u*h*a)*p := by
      change (u+v)*(p-h*a*p) = _
      noncomm_ring [hup]
    _ = (a-u*h*a)*p := by rw [← hL]
    _ = p*a*p+h*u*a*p := by rw [ha, add_mul]
    _ = p*a*p-h*a*p*a*p := by rw [he, sub_eq_add_neg]
    _ = correctedInclusion u h v q*residualDifferential u h v q := by
      change _ = (p-h*a*p)*(p*a*p)
      noncomm_ring [hpp, idempotent_suffix p hpp]

include hu hh huh uhu hq hl in
/-- Corrected retraction is a chain map in every degree. -/
theorem corrected_retraction_chain (hd : (u+v)*(u+v) = 0) :
    correctedRetraction u h v q*(u+v) =
      residualDifferential u h v q*correctedRetraction u h v q := by
  let p := pureProjection u h
  let a := correction v q
  have hpp : p*p = p := pureProjection_square u h hu hh huh uhu
  have hpu : p*u = 0 := pureProjection_u u h hu uhu
  have ht : u*a+a*u+a*p*a = 0 := correction_twisting u h v hu q l hq hl hd
  have hR : a = v-a*h*v := correction_right_equation h v q l hq hl
  have he : p*a*u*h = -(p*a*p*a*h) := by
    apply eq_neg_of_add_eq_zero_left
    have hz := congrArg (fun x => p*x*h) ht
    simpa only [mul_add, add_mul, mul_assoc, zero_mul_suffix _ _ hpu, zero_add, zero_mul, mul_zero] using hz
  have ha : a-a*h*u = a*p+a*u*h := by dsimp [p]; noncomm_ring [pureProjection]
  calc
    correctedRetraction u h v q*(u+v) = p*(v-a*h*v-a*h*u) := by
      change (p-p*a*h)*(u+v) = _
      noncomm_ring [hpu]
    _ = p*(a-a*h*u) := by rw [← hR]
    _ = p*a*p+p*a*u*h := by rw [ha, mul_add]; simp only [mul_assoc]
    _ = p*a*p-p*a*p*a*h := by rw [he, sub_eq_add_neg]
    _ = residualDifferential u h v q*correctedRetraction u h v q := by
      change _ = (p*a*p)*(p-p*a*h)
      noncomm_ring [hpp, idempotent_suffix p hpp]

include hh in
theorem corrected_homotopy_square : correctedHomotopy h v q*correctedHomotopy h v q = 0 := by
  noncomm_ring [correctedHomotopy, hh, square_zero_suffix h hh]

include hh huh in
theorem corrected_homotopy_inclusion : correctedHomotopy h v q*correctedInclusion u h v q = 0 := by
  have hhp := h_pureProjection u h hh huh
  noncomm_ring [correctedHomotopy, correctedInclusion,
    hhp, zero_mul_suffix _ _ hhp, square_zero_suffix h hh]

include hu hh huh uhu hq hl in
/-- The constructed homotopy is regular for the perturbed differential. -/
theorem corrected_homotopy_regular (hd : (u+v)*(u+v) = 0) :
    correctedHomotopy h v q*(u+v)*correctedHomotopy h v q = correctedHomotopy h v q := by
  have he := congrArg (fun x => correctedHomotopy h v q*x)
    (corrected_homotopy_identity u h v hu hh huh uhu q l hq hl hd)
  dsimp only at he
  rw [← mul_assoc, corrected_homotopy_inclusion u h v hh huh q, zero_mul] at he
  have hH := corrected_homotopy_square h v hh q
  simp only [mul_sub, mul_one, mul_assoc, square_zero_suffix _ hH, sub_zero] at he
  simpa only [mul_assoc] using (sub_eq_zero.mp he.symm).symm

end RingIdentities

section FiniteMatrices

open Finset

variable {R : Type*} [Ring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Both products of a weight-preserving contraction and a raising perturbation raise weight. -/
theorem preserving_raising_products (H V : Matrix ι ι R) (w : ι → ℕ)
    (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    (∀ i j, w i ≤ w j → (V*H) i j = 0) ∧
    (∀ i j, w i ≤ w j → (H*V) i j = 0) := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    apply sum_eq_zero
    intro k _
    by_cases hk : w k = w j
    · rw [hV i k (by omega), zero_mul]
    · rw [hH k j hk, mul_zero]
  · intro i j hij
    rw [Matrix.mul_apply]
    apply sum_eq_zero
    intro k _
    by_cases hk : w i = w k
    · rw [hV k j (by omega), mul_zero]
    · rw [hH i k hk, zero_mul]

/-- The inverse is the explicitly bounded finite geometric sum. -/
def finiteUnit (N : Matrix ι ι R) (n : ℕ) (hn : N^n = 0) : (Matrix ι ι R)ˣ where
  val := 1+N
  inv := ∑ k ∈ range n, (-N)^k
  val_inv := by
    have hneg : (-N)^n = 0 := by rw [neg_pow, hn, mul_zero]
    simpa [hneg] using mul_neg_geom_sum (-N) n
  inv_val := by
    have hneg : (-N)^n = 0 := by rw [neg_pow, hn, mul_zero]
    simpa [hneg] using geom_sum_mul_neg (-N) n

/-- Frozen weight bounded by `b` fixes the inverse length at exactly `b+1` terms. -/
def weightUnit (N : Matrix ι ι R) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hN : ∀ i j, w i ≤ w j → N i j = 0) : (Matrix ι ι R)ˣ :=
  finiteUnit N (b+1) (Verification.ChainCancellation.raising_matrix_nilpotent N w b hw hN)

/-- No invertibility assumption is supplied to this construction. -/
def leftWeightUnit (H V : Matrix ι ι R) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) : (Matrix ι ι R)ˣ :=
  weightUnit (V*H) w b hw (preserving_raising_products H V w hH hV).1

/-- The companion inverse is likewise constructed from the finite weight filtration. -/
def rightWeightUnit (H V : Matrix ι ι R) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) : (Matrix ι ι R)ˣ :=
  weightUnit (H*V) w b hw (preserving_raising_products H V w hH hV).2

/-- Actual finite matrices carrying every identity of a simultaneous cancellation.
These identities apply to all graded components whenever the supplied matrices
have the usual differential/contraction degrees. -/
structure MatrixRetraction (D P : Matrix ι ι R) where
  differential : Matrix ι ι R
  inclusion : Matrix ι ι R
  retraction : Matrix ι ι R
  homotopy : Matrix ι ι R
  square : differential*differential = 0
  inclusion_chain : D*inclusion = inclusion*differential
  retraction_chain : retraction*D = differential*retraction
  retract : retraction*inclusion = P
  homotopy_identity : inclusion*retraction = 1-D*homotopy-homotopy*D
  homotopy_square : homotopy*homotopy = 0
  homotopy_regular : homotopy*D*homotopy = homotopy

/-- Explicit finite simultaneous cancellation of the chosen pure unit pairs.
Only their original splitting, the perturbed square-zero identity, and finite
weight increase are inputs; all corrected maps and their identities are built. -/
def filteredCancellation (U H V : Matrix ι ι R)
    (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
    (hD : (U+V)*(U+V) = 0) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    MatrixRetraction (U+V) (pureProjection U H) := by
  let q := leftWeightUnit H V w b hw hH hV
  let l := rightWeightUnit H V w b hw hH hV
  have hq : (q : Matrix ι ι R) = 1+V*H := rfl
  have hl : (l : Matrix ι ι R) = 1+H*V := rfl
  exact {
    differential := residualDifferential U H V q
    inclusion := correctedInclusion U H V q
    retraction := correctedRetraction U H V q
    homotopy := correctedHomotopy H V q
    square := residual_square U H V hU hHH hHUH hUHU q l hq hl hD
    inclusion_chain := corrected_inclusion_chain U H V hU hHH hHUH hUHU q l hq hl hD
    retraction_chain := corrected_retraction_chain U H V hU hHH hHUH hUHU q l hq hl hD
    retract := corrected_retraction_inclusion U H V hU hHH hHUH hUHU q
    homotopy_identity := corrected_homotopy_identity U H V hU hHH hHUH hUHU q l hq hl hD
    homotopy_square := corrected_homotopy_square H V hHH q
    homotopy_regular := corrected_homotopy_regular U H V hU hHH hHUH hUHU q l hq hl hD }

end FiniteMatrices

section ScalarPerturbation

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual boundary contains the perturbation scalar as an actual common factor. -/
theorem residual_scalar_factor (U H V : Matrix ι ι R) (s : R) (q : (Matrix ι ι R)ˣ) :
    residualDifferential U H (s • V) q =
      s • (pureProjection U H * q.inv * V * pureProjection U H) := by
  simp only [residualDifferential, correction, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]

/-- Every nonempty perturbation path has a hyperbolic scalar factor. -/
theorem hyperbolic_path_scalar (H V : Matrix ι ι R) (s : R) (hs : s*s = 2*s) (k : ℕ) :
    (-(s • V * H))^k * (s • V) =
      s • ((2 : R)^k • ((-(V*H))^k * V)) := by
  have hp (n : ℕ) : s^(n+1) = 2^n*s := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, mul_assoc, hs, ← mul_assoc, ← pow_succ]
  have he : -(s • V * H) = s • (-(V*H)) := by rw [Matrix.smul_mul, smul_neg]
  rw [he, smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ, hp]
  rw [smul_smul, mul_comm]

/-- The full bounded residual path sum has an explicit scalar-free coefficient matrix. -/
theorem finite_hyperbolic_residual (U H V : Matrix ι ι R) (s : R) (hs : s*s = 2*s)
    (n : ℕ) (hn : (s • V * H)^n = 0) :
    residualDifferential U H (s • V) (finiteUnit (s • V*H) n hn) =
      s • (pureProjection U H *
        (∑ k ∈ Finset.range n, (2 : R)^k • ((-(V*H))^k * V)) * pureProjection U H) := by
  change pureProjection U H * ((∑ k ∈ Finset.range n, (-(s • V*H))^k) *
    (s • V)) * pureProjection U H = _
  rw [Finset.sum_mul]
  simp_rw [hyperbolic_path_scalar H V s hs]
  rw [← Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

end ScalarPerturbation

section IntegralCoefficients

open Finset

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise integer coefficient extension, as an actual matrix ring homomorphism. -/
def integerMatrixMap : Matrix ι ι ℤ →+* Matrix ι ι R := (Int.castRingHom R).mapMatrix

theorem integerMatrixMap_smul (z : ℤ) (M : Matrix ι ι ℤ) :
    integerMatrixMap (R := R) (z • M) = (z : R) • integerMatrixMap M := by
  ext i j
  change ((z * M i j : ℤ) : R) = (z : R)*(M i j : R)
  exact Int.cast_mul z _

/-- The integer coefficient matrix of the residual boundary is a literal finite path sum. -/
def integerResidual (U H V : Matrix ι ι ℤ) (n : ℕ) : Matrix ι ι ℤ :=
  pureProjection U H * (∑ k ∈ range n, (2 : ℤ)^k • ((-(V*H))^k*V)) * pureProjection U H

/-- Cancellation of an integer pure part with perturbation `hV` leaves exactly `hA`
with the displayed integer matrix `A`; the assertion is not merely ideal membership. -/
theorem finite_integral_hyperbolic_residual (U H V : Matrix ι ι ℤ)
    (s : R) (hs : s*s = 2*s) (n : ℕ)
    (hn : (s • integerMatrixMap (R := R) V * integerMatrixMap H)^n = 0) :
    residualDifferential (integerMatrixMap U) (integerMatrixMap H) (s • integerMatrixMap V)
      (finiteUnit (s • integerMatrixMap V * integerMatrixMap H) n hn) =
      s • integerMatrixMap (integerResidual U H V n) := by
  rw [finite_hyperbolic_residual _ _ _ s hs n hn]
  congr 1
  simp only [integerResidual, pureProjection, map_mul, map_sub, map_one, map_sum,
    integerMatrixMap_smul, map_pow, map_neg, Int.cast_pow, Int.cast_ofNat]

end IntegralCoefficients

#print axioms square_zero_suffix
#print axioms pureProjection
#print axioms pureProjection_square
#print axioms pureProjection_u
#print axioms u_pureProjection
#print axioms pureProjection_h
#print axioms h_pureProjection
#print axioms correction
#print axioms correction_left
#print axioms correction_right
#print axioms correction_left_equation
#print axioms correction_right_equation
#print axioms correction_twisting
#print axioms correctedHomotopy
#print axioms correctedInclusion
#print axioms correctedRetraction
#print axioms residualDifferential

#print axioms zero_mul_suffix
#print axioms idempotent_suffix
#print axioms corrected_retraction_inclusion
#print axioms corrected_inclusion_retraction_expansion
#print axioms corrected_homotopy_identity
#print axioms residual_square
#print axioms corrected_inclusion_chain
#print axioms corrected_retraction_chain
#print axioms corrected_homotopy_square
#print axioms corrected_homotopy_inclusion
#print axioms corrected_homotopy_regular

#print axioms preserving_raising_products
#print axioms finiteUnit
#print axioms weightUnit
#print axioms leftWeightUnit
#print axioms rightWeightUnit
#print axioms filteredCancellation
#print axioms residual_scalar_factor
#print axioms hyperbolic_path_scalar
#print axioms finite_hyperbolic_residual

#print axioms integerMatrixMap
#print axioms integerMatrixMap_smul
#print axioms integerResidual
#print axioms finite_integral_hyperbolic_residual

end Verification.FinitePerturbation

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.FinitePerturbation.MatrixRetraction
