import WPActualEvenLogCarry
import WPFiniteCarry.OriginalCoordinate
import WPActualRankTwoFiniteLegendre
import WPActualNativeQuadraticSquare
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial BigOperators
open Polynomial WPPIntegralReduction WPActualEvenLogCarry WPActualRankTwoHatLift
  WPActualRankTwoFirstLift WPActualRankTwoGaussODE WPActualRankTwoProper
  WPActualRankTwoFiniteLegendre WPActualRankTwoLowTaylor WPActualNativeHasse
  WPActualRankTwoLegendreField WPActualNativeQuadraticSquare

namespace WPFiniteCarry

set_option maxHeartbeats 1000000

/-- The rational homogeneous Jacobi kernel has no polynomial below degree d. -/
theorem rationalJacobi_kernel_below_degree (d : ℕ) (P : ℚ[X])
    (hd : P.natDegree < d) (hs : legendreJacobi d P = 0) : P = 0 := by
  by_contra hP
  have ht := legendreJacobi_coeff d P.natDegree P
  rw [hs, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, zero_add] at ht
  have hmQ : (P.natDegree : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hu : (d : ℚ) * ((d : ℚ) + 1) -
      (P.natDegree : ℚ) * ((P.natDegree : ℚ) + 1) ≠ 0 := by
    have hh : (0 : ℚ) < (d : ℚ) * ((d : ℚ) + 1) -
        (P.natDegree : ℚ) * ((P.natDegree : ℚ) + 1) := by
      calc
        0 < ((d : ℚ) - (P.natDegree : ℚ)) *
            ((d : ℚ) + (P.natDegree : ℚ) + 1) :=
          mul_pos (sub_pos.mpr hmQ) (by positivity)
        _ = _ := by ring
    exact ne_of_gt hh
  have hz : P.coeff P.natDegree = 0 := (mul_eq_zero.mp ht.symm).resolve_left hu
  exact (leadingCoeff_ne_zero.mpr hP) (by simpa only [coeff_natDegree] using hz)

theorem rationalJacobi_reflection (d : ℕ) (P : ℚ[X]) :
    legendreJacobi d (P.comp (-X)) = (legendreJacobi d P).comp (-X) := by
  have h1 : (P.comp (-X)).derivative = -P.derivative.comp (-X) := by
    simp [derivative_comp]
  have h2 : (P.comp (-X)).derivative.derivative = P.derivative.derivative.comp (-X) := by
    rw [h1]
    simp [derivative_comp]
  unfold legendreJacobi
  rw [h2, h1]
  simp only [add_comp, sub_comp, mul_comp, pow_comp, one_comp, X_comp, C_comp,
    ofNat_comp]
  ring

theorem rationalJacobi_sub (d : ℕ) (P Q : ℚ[X]) :
    legendreJacobi d (P - Q) = legendreJacobi d P - legendreJacobi d Q := by
  simp only [legendreJacobi, derivative_sub]
  ring

/-- Parity of the actual normalized Y, derived from its rational source and top coefficient. -/
theorem rationalLegendre_reflection (d : ℕ) (hd : 0 < d) :
    (rationalLegendre d).comp (-X) = C ((-1 : ℚ) ^ d) * rationalLegendre d := by
  let D := (rationalLegendre d).comp (-X) - C ((-1 : ℚ) ^ d) * rationalLegendre d
  have hs : legendreJacobi d D = 0 := by
    dsimp only [D]
    rw [rationalJacobi_sub, rationalJacobi_reflection, rationalLegendre_ODE,
      legendreJacobi_C_mul, rationalLegendre_ODE]
    simp
  have hdeg : D.natDegree ≤ d - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    dsimp only [D]
    rw [coeff_sub, coeff_comp_neg, coeff_C_mul]
    by_cases hnd : n = d
    · subst n
      ring
    · rw [coeff_eq_zero_of_natDegree_lt ((rationalLegendre_degree d).trans_lt (by omega))]
      ring
  have hz := rationalJacobi_kernel_below_degree d D (by omega) hs
  exact sub_eq_zero.mp hz

theorem rationalLegendre_derivative_reflection (d : ℕ) (hd : 0 < d) :
    (rationalLegendre d).derivative.comp (-X) =
      -C ((-1 : ℚ) ^ d) * (rationalLegendre d).derivative := by
  have h := congrArg Polynomial.derivative (rationalLegendre_reflection d hd)
  simp only [derivative_comp, derivative_neg, derivative_X, derivative_mul,
    derivative_C, zero_mul, zero_add] at h
  linear_combination -h

/-- Parity of the actual proper n, forced by the same source and the proper degree bound. -/
theorem rationalProperJacobi_reflection (d : ℕ) (hd : 0 < d) :
    (rationalProperJacobi d).comp (-X) =
      -C ((-1 : ℚ) ^ d) * rationalProperJacobi d := by
  let D := (rationalProperJacobi d).comp (-X) + C ((-1 : ℚ) ^ d) * rationalProperJacobi d
  have hs : legendreJacobi d D = 0 := by
    dsimp only [D]
    rw [legendreJacobi_add, rationalJacobi_reflection, rationalProperJacobi_source,
      legendreJacobi_C_mul, rationalProperJacobi_source]
    simp only [mul_comp, neg_comp, ofNat_comp]
    rw [rationalLegendre_derivative_reflection d hd]
    ring
  have href : ((rationalProperJacobi d).comp (-X)).natDegree ≤ d - 1 := by
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul (rationalProperJacobi_degree d)
        (show (-X : ℚ[X]).natDegree ≤ 1 by simp)).trans (by simp))
  have hscalar : (C ((-1 : ℚ) ^ d) * rationalProperJacobi d).natDegree ≤ d - 1 :=
    (natDegree_C_mul_le _ _).trans (rationalProperJacobi_degree d)
  have hdeg : D.natDegree ≤ d - 1 := by
    simpa only [D, Nat.max_self] using natDegree_add_le_of_le href hscalar
  have hz := rationalJacobi_kernel_below_degree d D (by omega) hs
  dsimp only [D] at hz
  linear_combination hz

noncomputable def rationalProperProduct (d : ℕ) : ℚ[X] :=
  rationalProperJacobi d * rationalLegendre d

theorem rationalProperProduct_odd (d : ℕ) (hd : 0 < d) :
    (rationalProperProduct d).comp (-X) = -rationalProperProduct d := by
  have hsign : ((-1 : ℚ) ^ d) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  have hc : C ((-1 : ℚ) ^ d) * C ((-1 : ℚ) ^ d) = (1 : ℚ[X]) := by
    rw [← C_mul, ← pow_two, hsign, C_1]
  unfold rationalProperProduct
  rw [mul_comp, rationalProperJacobi_reflection d hd,
    rationalLegendre_reflection d hd]
  linear_combination -(rationalProperJacobi d * rationalLegendre d) * hc

/-- The literal proper product after T(t)=4t^3-3t; no parity is assigned. -/
noncomputable def actualProperCover (p : ℕ) : ℚ[X] :=
  (rationalProperProduct (p / 6)).comp (4 * X ^ 3 - 3 * X)

theorem actualProperCover_odd (p : ℕ) (hp : 19 ≤ p) :
    (actualProperCover p).comp (-X) = -actualProperCover p := by
  have hT : (4 * X ^ 3 - 3 * X : ℚ[X]).comp (-X) = -(4 * X ^ 3 - 3 * X) := by
    simp only [sub_comp, mul_comp, pow_comp, ofNat_comp, X_comp]
    ring
  calc
    _ = (rationalProperProduct (p / 6)).comp (-(4 * X ^ 3 - 3 * X)) := by
      rw [actualProperCover, Polynomial.comp_assoc, hT]
    _ = ((rationalProperProduct (p / 6)).comp (-X)).comp (4 * X ^ 3 - 3 * X) := by
      simp only [Polynomial.comp_assoc, neg_comp, X_comp]
    _ = -actualProperCover p := by
      rw [rationalProperProduct_odd (p / 6) (by omega)]
      simp only [neg_comp, actualProperCover]

theorem rational_odd_coeff_even_zero (P : ℚ[X]) (ho : P.comp (-X) = -P) (j : ℕ) :
    P.coeff (2 * j) = 0 := by
  have h := congrArg (fun Q : ℚ[X] => Q.coeff (2 * j)) ho
  rw [coeff_comp_neg, coeff_neg] at h
  have hs : (-1 : ℚ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [hs, mul_one] at h
  linarith

/-- Literal selection of odd coefficients through a stated finite cutoff. -/
noncomputable def oddCoefficientPolynomial {K : Type*} [CommRing K] (P : K[X]) (e : ℕ) : K[X] :=
  rankCoefficientPolynomial e (fun j => P.coeff (2 * j + 1))

theorem oddCoefficientPolynomial_coeff (P : ℚ[X]) (j : ℕ) :
    (oddCoefficientPolynomial P P.natDegree).coeff j = P.coeff (2 * j + 1) := by
  rw [oddCoefficientPolynomial, rankCoefficientPolynomial_coeff]
  split_ifs with hj
  · rfl
  · symm
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem oddCoefficientPolynomial_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : K[X]) (e : ℕ) :
    (oddCoefficientPolynomial P e).map f = oddCoefficientPolynomial (P.map f) e := by
  ext j
  rw [coeff_map, oddCoefficientPolynomial, oddCoefficientPolynomial,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs
  · rw [coeff_map]
  · exact map_zero f

theorem rational_odd_reconstruct (P : ℚ[X]) (ho : P.comp (-X) = -P) :
    P = X * (oddCoefficientPolynomial P P.natDegree).comp (X ^ 2) := by
  ext n
  cases n with
  | zero =>
    rw [coeff_X_mul_zero]
    simpa only [Nat.mul_zero] using rational_odd_coeff_even_zero P ho 0
  | succ n =>
    rw [coeff_X_mul]
    change P.coeff (n + 1) = (expand ℚ 2 (oddCoefficientPolynomial P P.natDegree)).coeff n
    rw [coeff_expand (by omega : 0 < 2)]
    by_cases hn : 2 ∣ n
    · rw [if_pos hn, oddCoefficientPolynomial_coeff, Nat.mul_div_cancel' hn]
    · rw [if_neg hn]
      have hm : n % 2 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
      have he : n + 1 = 2 * ((n + 1) / 2) := by omega
      rw [he]
      exact rational_odd_coeff_even_zero P ho _

/-- The actual R_B is selected from the actual transported nY polynomial. -/
noncomputable def actualRB (p : ℕ) : ℚ[X] :=
  oddCoefficientPolynomial (actualProperCover p) (actualProperCover p).natDegree

theorem actualRB_coeff (p j : ℕ) :
    (actualRB p).coeff j = (actualProperCover p).coeff (2 * j + 1) :=
  oddCoefficientPolynomial_coeff _ _

theorem actualProperCover_degree (p : ℕ) (hp : 19 ≤ p) :
    (actualProperCover p).natDegree ≤ 6 * (p / 6) - 3 := by
  have hprod : (rationalProperProduct (p / 6)).natDegree ≤ (p / 6 - 1) + p / 6 :=
    natDegree_mul_le_of_le (rationalProperJacobi_degree _) (rationalLegendre_degree _)
  have hcubic : (4 * X ^ 3 - 3 * X : ℚ[X]).natDegree ≤ 3 := by compute_degree
  have h := (natDegree_comp_le (p := rationalProperProduct (p / 6))
    (q := 4 * X ^ 3 - 3 * X)).trans (Nat.mul_le_mul hprod hcubic)
  change (actualProperCover p).natDegree ≤ ((p / 6 - 1) + p / 6) * 3 at h
  exact h.trans (by omega)

theorem actualRB_degree (p : ℕ) (hp : 19 ≤ p) :
    (actualRB p).natDegree ≤ 3 * (p / 6) - 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [actualRB_coeff]
  exact coeff_eq_zero_of_natDegree_lt ((actualProperCover_degree p hp).trans_lt (by omega))

theorem actualProperCover_descent (p : ℕ) (hp : 19 ≤ p) :
    actualProperCover p = X * (actualRB p).comp (X ^ 2) :=
  rational_odd_reconstruct _ (actualProperCover_odd p hp)

noncomputable def actualIntegralProperCover (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (integralProperJacobi p (by omega) * integralLegendre p (p / 6) (by omega)).comp
    (4 * X ^ 3 - 3 * X)

theorem actualIntegralProperCover_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualIntegralProperCover p hp).map (integralRationals p).subtype = actualProperCover p := by
  rw [actualIntegralProperCover, Polynomial.map_comp, Polynomial.map_mul,
    integralProperJacobi_value, integralLegendre_value]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, actualProperCover, rationalProperProduct]

noncomputable def actualIntegralRB (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  oddCoefficientPolynomial (actualIntegralProperCover p hp) (actualProperCover p).natDegree

theorem actualIntegralRB_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualIntegralRB p hp).map (integralRationals p).subtype = actualRB p := by
  rw [actualIntegralRB, oddCoefficientPolynomial_map, actualIntegralProperCover_value p hp]
  rfl

theorem actualIntegralProperCover_descent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualIntegralProperCover p hp = X * (actualIntegralRB p hp).comp (X ^ 2) := by
  apply polynomial_subtype_injective p
  simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp,
    Polynomial.map_pow, actualIntegralProperCover_value, actualIntegralRB_value]
  exact actualProperCover_descent p hp

theorem actualRB_coefficient_integral (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualRB p).coeff j) := by
  rw [← actualIntegralRB_value p hp, coeff_map]
  exact ((actualIntegralRB p hp).coeff j).property

/-- The original x-coordinate s=(x+1)/5 used by the actual C_B. -/
noncomputable def actualOriginalS : ℚ[X] := C (1 / 5 : ℚ) * (X + 1)

noncomputable def integralOriginalS (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  C (smallIntegralInverse p 5) * (X + 1)

theorem integralOriginalS_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralOriginalS p).map (integralRationals p).subtype = actualOriginalS := by
  simp only [integralOriginalS, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one, actualOriginalS]
  rw [show (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) from
    smallIntegralInverse_value p 5 (by omega) (by omega)]

/-- The specified original-coordinate C_B, constructed before any residue. -/
noncomputable def actualCB (p : ℕ) : ℚ[X] :=
  C (1 / 5 : ℚ) * actualOriginalS ^ ((p - 1) / 2 + 1) * (actualRB p).comp actualOriginalS

noncomputable def actualIntegralCB (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  C (smallIntegralInverse p 5) * integralOriginalS p ^ ((p - 1) / 2 + 1) *
    (actualIntegralRB p hp).comp (integralOriginalS p)

theorem actualIntegralCB_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualIntegralCB p hp).map (integralRationals p).subtype = actualCB p := by
  rw [actualIntegralCB, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_comp, integralOriginalS_value p hp,
    actualIntegralRB_value p hp,
    show (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) from
      smallIntegralInverse_value p 5 (by omega) (by omega)]
  rfl

theorem actualCB_coefficient_integral (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualCB p).coeff j) := by
  rw [← actualIntegralCB_value p hp, coeff_map]
  exact ((actualIntegralCB p hp).coeff j).property

theorem actualCB_degree (p : ℕ) (hp : 19 ≤ p) :
    (actualCB p).natDegree ≤ (p - 1) / 2 + 1 + (3 * (p / 6) - 2) := by
  have hs : actualOriginalS.natDegree ≤ 1 := by
    unfold actualOriginalS
    compute_degree
  have hpow : (actualOriginalS ^ ((p - 1) / 2 + 1)).natDegree ≤ (p - 1) / 2 + 1 :=
    (natDegree_pow_le_of_le _ hs).trans (by simp)
  have hr : ((actualRB p).comp actualOriginalS).natDegree ≤ 3 * (p / 6) - 2 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (actualRB_degree p hp) hs).trans (by simp))
  exact natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hpow) hr

theorem actualCB_degree_lt_prime (p : ℕ) (hp : 19 ≤ p) : (actualCB p).natDegree < p := by
  have := actualCB_degree p hp
  omega

noncomputable def actualRBField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (actualIntegralRB p hp).map (residueHom p)

noncomputable def actualCBField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (actualIntegralCB p hp).map (residueHom p)

theorem actualRBField_coeff (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualRBField p hp).coeff j = residueHom p ((actualIntegralRB p hp).coeff j) := by
  rw [actualRBField, coeff_map]

theorem actualCBField_coeff (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualCBField p hp).coeff j = residueHom p ((actualIntegralCB p hp).coeff j) := by
  rw [actualCBField, coeff_map]

theorem actualCB_coefficient_field (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((actualCB p).coeff j : ZMod p) = (actualCBField p hp).coeff j := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff j) (actualIntegralCB_value p hp)
  rw [coeff_map] at hv
  rw [← hv, actualCBField_coeff]
  rfl

theorem actualOriginalS_cover : actualOriginalS.comp originalX = (X ^ 2 : ℚ[X]) := by
  simpa only [actualOriginalS, mul_comp, C_comp, add_comp, X_comp, one_comp] using
    original_s_coordinate

theorem actualProperCover_original (p : ℕ) :
    actualProperCover p =
      (rationalProperJacobi (p / 6)).comp originalT *
        (rationalLegendre (p / 6)).comp originalT := by
  simp only [actualProperCover, rationalProperProduct, mul_comp, originalT_chebyshev]

theorem actualCB_cover (p : ℕ) :
    (actualCB p).comp originalX = C (1 / 5 : ℚ) *
      (X ^ 2) ^ ((p - 1) / 2 + 1) * (actualRB p).comp (X ^ 2) := by
  simp only [actualCB, mul_comp, C_comp, pow_comp, Polynomial.comp_assoc,
    actualOriginalS_cover]

/-- The exact original-cover identity with the complete actual cubic power A_p. -/
theorem actualCB_original_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalT ^ p * actualProperCover p =
      (rationalCubicPower p * actualCB p).comp originalX := by
  have hhalf : p + 1 = 2 * ((p - 1) / 2 + 1) := by
    have := prime_half_identity p (by omega : 7 ≤ p)
    omega
  have hx : (X : ℚ[X]) ^ p * X = (X ^ 2) ^ ((p - 1) / 2 + 1) := by
    rw [← pow_succ, ← pow_mul, hhalf]
  have hc : (C (1 / 5 : ℚ) : ℚ[X]) ^ p =
      C (1 / (5 : ℚ) ^ (p - 1)) * C (1 / 5 : ℚ) := by
    calc
      _ = C (1 / 5 : ℚ) ^ ((p - 1) + 1) := by congr 1; omega
      _ = C (1 / 5 : ℚ) ^ (p - 1) * C (1 / 5 : ℚ) := pow_succ _ _
      _ = _ := by rw [← C_pow, one_div_pow]
  calc
    originalT ^ p * actualProperCover p =
        C (1 / 5 : ℚ) ^ p * (4 * originalX - 11) ^ p *
          ((X : ℚ[X]) ^ p * X) * (actualRB p).comp (X ^ 2) := by
      rw [originalT, actualProperCover_descent p hp, mul_pow, mul_pow]
      ring
    _ = (C (1 / (5 : ℚ) ^ (p - 1)) * (4 * originalX - 11) ^ p) *
        (C (1 / 5 : ℚ) * (X ^ 2) ^ ((p - 1) / 2 + 1) *
          (actualRB p).comp (X ^ 2)) := by
      rw [hc, hx]
      ring
    _ = (rationalCubicPower p * actualCB p).comp originalX := by
      rw [mul_comp, actualCB_cover]
      simp only [rationalCubicPower, mul_comp, C_comp, pow_comp, sub_comp,
        ofNat_comp, X_comp]
      norm_num

theorem actualCB_original_proper_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalT ^ p * (rationalProperJacobi (p / 6)).comp originalT *
        (rationalLegendre (p / 6)).comp originalT =
      (rationalCubicPower p * actualCB p).comp originalX := by
  simpa only [actualProperCover_original, mul_assoc] using actualCB_original_source p hp

/-- Composition with the nonconstant original x-cover loses no rational polynomial. -/
theorem originalX_comp_injective :
    Function.Injective (fun P : ℚ[X] => P.comp originalX) := by
  intro P Q h
  change P.comp originalX = Q.comp originalX at h
  apply sub_eq_zero.mp
  have hz : (P - Q).comp originalX = 0 := by rw [sub_comp, h, sub_self]
  rcases comp_eq_zero_iff.mp hz with hPQ | ⟨_, hc⟩
  · exact hPQ
  · have hh := congrArg (fun R : ℚ[X] => R.coeff 2) hc
    norm_num [originalX] at hh

/-- Literal even-coefficient selection, with the degree bound supplied separately. -/
noncomputable def evenCoefficientPolynomial {K : Type*} [CommRing K]
    (P : K[X]) (e : ℕ) : K[X] :=
  rankCoefficientPolynomial e (fun j => P.coeff (2 * j))

theorem evenCoefficientPolynomial_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : K[X]) (e : ℕ) :
    (evenCoefficientPolynomial P e).map f = evenCoefficientPolynomial (P.map f) e := by
  ext j
  rw [coeff_map, evenCoefficientPolynomial, evenCoefficientPolynomial,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs
  · rw [coeff_map]
  · exact map_zero f

theorem evenCoefficientPolynomial_coeff (P : ℚ[X]) (e j : ℕ)
    (hd : P.natDegree ≤ 2 * e) :
    (evenCoefficientPolynomial P e).coeff j = P.coeff (2 * j) := by
  rw [evenCoefficientPolynomial, rankCoefficientPolynomial_coeff]
  split_ifs with hj
  · rfl
  · symm
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem rational_even_coeff_odd_zero (P : ℚ[X]) (he : P.comp (-X) = P) (j : ℕ) :
    P.coeff (2 * j + 1) = 0 := by
  have h := congrArg (fun Q : ℚ[X] => Q.coeff (2 * j + 1)) he
  rw [coeff_comp_neg] at h
  have hs : (-1 : ℚ) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hs] at h
  linarith

theorem rational_even_reconstruct (P : ℚ[X]) (e : ℕ)
    (hd : P.natDegree ≤ 2 * e) (he : P.comp (-X) = P) :
    P = (evenCoefficientPolynomial P e).comp (X ^ 2) := by
  ext n
  change P.coeff n = (expand ℚ 2 (evenCoefficientPolynomial P e)).coeff n
  rw [coeff_expand (by omega : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, evenCoefficientPolynomial_coeff P e _ hd,
      Nat.mul_div_cancel' hn]
  · rw [if_neg hn]
    have hm : n % 2 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    have hodd : n = 2 * (n / 2) + 1 := by omega
    rw [hodd]
    exact rational_even_coeff_odd_zero P he _

noncomputable def rationalLowSquare (d : ℕ) : ℚ[X] := rationalLegendre d ^ 2

theorem rationalLowSquare_degree (d : ℕ) : (rationalLowSquare d).natDegree ≤ 2 * d := by
  simpa only [rationalLowSquare, pow_two, two_mul] using
    natDegree_mul_le_of_le (rationalLegendre_degree d) (rationalLegendre_degree d)

theorem rationalLowSquare_even (d : ℕ) (hd : 0 < d) :
    (rationalLowSquare d).comp (-X) = rationalLowSquare d := by
  have hsign : ((-1 : ℚ) ^ d) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  have hc : (C ((-1 : ℚ) ^ d) : ℚ[X]) ^ 2 = 1 := by
    rw [← C_pow, hsign, C_1]
  unfold rationalLowSquare
  rw [pow_comp, rationalLegendre_reflection d hd, mul_pow, hc, one_mul]

noncomputable def rationalLowEven (d : ℕ) : ℚ[X] :=
  evenCoefficientPolynomial (rationalLowSquare d) d

noncomputable def actualLowF (p : ℕ) : ℚ[X] := (rationalLowEven (p / 6)).comp (1 - X)

theorem actualLowF_degree (p : ℕ) : (actualLowF p).natDegree ≤ p / 6 := by
  have he : (rationalLowEven (p / 6)).natDegree ≤ p / 6 :=
    rankCoefficientPolynomial_degree _ _
  have hq : (1 - X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul he hq).trans (by simp))

/-- The actual rational low square descends through q=1-T^2. -/
theorem actualLowF_Jacobi_square (p : ℕ) (hp : 19 ≤ p) :
    (actualLowF p).comp (1 - X ^ 2) = rationalLegendre (p / 6) ^ 2 := by
  have harg : (1 - X : ℚ[X]).comp (1 - X ^ 2) = X ^ 2 := by
    simp only [sub_comp, one_comp, X_comp]
    ring
  rw [actualLowF, Polynomial.comp_assoc, harg]
  exact (rational_even_reconstruct _ _ (rationalLowSquare_degree (p / 6))
    (rationalLowSquare_even (p / 6) (by omega))).symm

theorem actualLowF_origin (p : ℕ) (hp : 19 ≤ p) : (actualLowF p).eval 0 = 1 := by
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (actualLowF_Jacobi_square p hp)
  simpa only [eval_comp, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self,
    rationalLegendre_endpoint_one] using h

noncomputable def integralLowF (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (evenCoefficientPolynomial (integralLegendre p (p / 6) (by omega) ^ 2) (p / 6)).comp (1 - X)

theorem integralLowF_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralLowF p hp).map (integralRationals p).subtype = actualLowF p := by
  rw [integralLowF, Polynomial.map_comp, evenCoefficientPolynomial_map,
    Polynomial.map_pow, integralLegendre_value]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    actualLowF, rationalLowEven, rationalLowSquare]

theorem integralLowF_descent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralLowF p hp).comp (1 - X ^ 2) =
      integralLegendre p (p / 6) (by omega) ^ 2 := by
  apply polynomial_subtype_injective p
  simp only [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_pow, integralLowF_value, integralLegendre_value]
  exact actualLowF_Jacobi_square p hp

theorem actualLowF_coefficient_integral (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualLowF p).coeff j) := by
  rw [← integralLowF_value p hp, coeff_map]
  exact ((integralLowF p hp).coeff j).property

noncomputable def actualLowFField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (integralLowF p hp).map (residueHom p)

theorem squareComplement_comp_injective {K : Type*} [Field K] :
    Function.Injective (fun P : K[X] => P.comp (1 - X ^ 2)) := by
  intro P Q h
  change P.comp (1 - X ^ 2) = Q.comp (1 - X ^ 2) at h
  apply sub_eq_zero.mp
  have hz : (P - Q).comp (1 - X ^ 2) = 0 := by rw [sub_comp, h, sub_self]
  rcases comp_eq_zero_iff.mp hz with hPQ | ⟨_, hc⟩
  · exact hPQ
  · have hh := congrArg (fun R : K[X] => R.coeff 2) hc
    norm_num at hh

/-- The constructed integral low F reduces to the actual native field polynomial. -/
theorem actualLowFField_native (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualLowFField p hp = nativeField p (p / 6) := by
  apply squareComplement_comp_injective
  change (actualLowFField p hp).comp (1 - X ^ 2) =
    (nativeField p (p / 6)).comp (1 - X ^ 2)
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (integralLowF_descent p hp)
  simp only [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_pow, integralLegendre_field] at h
  rw [actualLowFField, h, actual_native_Jacobi_square p hp]

theorem actualLowF_coefficient_field (p j : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((actualLowF p).coeff j : ZMod p) = (nativeField p (p / 6)).coeff j := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff j) (integralLowF_value p hp)
  have hr := congrArg (fun P : (ZMod p)[X] => P.coeff j) (actualLowFField_native p hp)
  rw [coeff_map] at hv
  rw [actualLowFField, coeff_map] at hr
  rw [← hv]
  exact hr

end WPFiniteCarry
