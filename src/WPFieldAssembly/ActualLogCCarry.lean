import WPFieldAssembly.ActualEntropyPolynomial
import WPActualPullbackSource
import WPHasseIntegralTransport
import WPFiniteZSource

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPActualRankTwoLegendreField WPActualGaussProper WPFieldAssembly.ActualEntropyPolynomial

namespace WPFieldAssembly.ActualLogCCarry

set_option maxHeartbeats 1200000

/-- The narrow integral realization of the original finite logarithm at 1-V. -/
noncomputable def conicLogIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (movingEvenIntegral p).comp (1 - WPHasseIntegralTransport.integralV p (by omega))

noncomputable def conicLogQ (p : ℕ) : ℚ[X] :=
  (movingEvenQ p).comp (1 - WPActualPullbackSource.Vpolynomial)

noncomputable def logCIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  -(((p - 1) / 2 : ℕ) : integralRationals p) *
    (conicLogIntegral p hp).coeff ((p - 1) / 2)

theorem conicLogIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (conicLogIntegral p hp).map (integralRationals p).subtype = conicLogQ p := by
  simp only [conicLogIntegral, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_one, movingEvenIntegral_value,
    WPHasseIntegralTransport.integralV_map_rational, conicLogQ]

theorem logCIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (logCIntegral p hp).val = -(((p - 1) / 2 : ℕ) : ℚ) *
      (conicLogQ p).coeff ((p - 1) / 2) := by
  change -(((p - 1) / 2 : ℕ) : ℚ) *
    (integralRationals p).subtype ((conicLogIntegral p hp).coeff ((p - 1) / 2)) = _
  rw [←coeff_map, conicLogIntegral_value p hp]

theorem movingEvenQ_derivative (p : ℕ) :
    (movingEvenQ p).derivative =
      C (1 / 2 : ℚ) * ∑ j ∈ Finset.range ((p - 1) / 2), X^j := by
  ext n
  have hg : (∑ j ∈ Finset.range ((p - 1) / 2), (X : ℚ[X])^j).coeff n =
      if n < (p - 1) / 2 then 1 else 0 := by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  rw [coeff_derivative, movingEvenQ, rankCoefficientPolynomial_coeff,
    coeff_C_mul, hg]
  by_cases hn : n < (p - 1) / 2
  · rw [if_pos (by omega : n + 1 < (p - 1) / 2 + 1),
      if_neg (by omega : n + 1 ≠ 0), if_pos hn]
    have hnu : (((2 * (n + 1) : ℕ)) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp [hnu]
  · rw [if_neg (by omega : ¬n + 1 < (p - 1) / 2 + 1), if_neg hn]
    ring

theorem movingEvenQ_source (p : ℕ) :
    2 * (1 - X) * (movingEvenQ p).derivative =
      (1 - X^((p - 1) / 2) : ℚ[X]) := by
  rw [movingEvenQ_derivative]
  have hc : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    change C (2 : ℚ) * C (1 / 2 : ℚ) = C 1
    rw [←C_mul]
    norm_num
  calc
    _ = ((2 : ℚ[X]) * C (1 / 2 : ℚ)) *
        ((1 - X) * ∑ j ∈ Finset.range ((p - 1) / 2), X^j) := by ring
    _ = (1 - X) * ∑ j ∈ Finset.range ((p - 1) / 2), X^j := by rw [hc, one_mul]
    _ = _ := mul_neg_geom_sum X ((p - 1) / 2)

theorem movingEvenQ_origin (p : ℕ) : (movingEvenQ p).eval 0 = 0 := by
  rw [←coeff_zero_eq_eval_zero, movingEvenQ, rankCoefficientPolynomial_coeff]
  simp

/-- Characteristic-zero uniqueness will identify this narrow source with the
original finite squared logarithm once its checked import is available. -/
theorem finite_squared_log_unique (p : ℕ) (P : ℚ[X])
    (hP : 2 * (1 - X) * P.derivative = 1 - X^((p - 1) / 2))
    (h0 : P.eval 0 = 0) : P = movingEvenQ p := by
  let R := P - movingEvenQ p
  have hs : 2 * (1 - X) * R.derivative = 0 := by
    dsimp only [R]
    rw [derivative_sub, mul_sub, hP, movingEvenQ_source p, sub_self]
  have hlinear : (1 - X : ℚ[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun Q : ℚ[X] => Q.coeff 0) hz
    norm_num at hc
  have hfactor : (2 * (1 - X) : ℚ[X]) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)) hlinear
  have hd : R.derivative = 0 := (mul_eq_zero.mp hs).resolve_left hfactor
  have hc := eq_C_of_derivative_eq_zero hd
  have horigin : R.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp only [R]
    rw [eval_sub, h0, movingEvenQ_origin, sub_self]
  rw [horigin, C_0] at hc
  exact sub_eq_zero.mp hc

/-- The narrow lift satisfies the original cleared conic differential source. -/
theorem conicLogQ_source (p : ℕ) :
    2 * WPActualPullbackSource.Vpolynomial * (conicLogQ p).derivative =
      ((1 - WPActualPullbackSource.Vpolynomial)^((p - 1) / 2) - 1) *
        WPActualPullbackSource.Vpolynomial.derivative := by
  have he := congrArg (fun P : ℚ[X] =>
    P.comp (1 - WPActualPullbackSource.Vpolynomial)) (movingEvenQ_source p)
  simp only [mul_comp, ofNat_comp, sub_comp, one_comp, X_comp,
    pow_comp, sub_sub_cancel] at he
  rw [conicLogQ, derivative_comp, derivative_sub, derivative_one, zero_sub]
  linear_combination -WPActualPullbackSource.Vpolynomial.derivative * he

theorem conicLogQ_Abar_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * (WPFiniteZSource.Abar : ℚ[X]) * (conicLogQ p).derivative - 3 * (4 * X - 11) =
      -C (3 * (1 / 5 : ℚ)^(p - 1)) *
        (C (1 / 5 : ℚ) * (X + 1))^((p - 1) / 2) * (4 * X - 11)^p := by
  let V := WPActualPullbackSource.Vpolynomial
  let s : ℚ[X] := C (1 / 5 : ℚ) * (X + 1)
  let c : ℚ[X] := 4 * X - 11
  let A : ℚ[X] := WPFiniteZSource.Abar
  have hv : 1 - V = C (1 / 25 : ℚ) * s * c^2 := by
    have ht : (125 : ℚ[X]) - (4 * X - 1)^2 * (4 - X) =
        (X + 1) * (4 * X - 11)^2 := by ring
    have hc : C (1 / 125 : ℚ) * 125 = (1 : ℚ[X]) := by
      change C (1 / 125 : ℚ) * C 125 = C 1
      rw [←C_mul]
      norm_num
    calc
      _ = C (1 / 125 : ℚ) * (125 - (4 * X - 1)^2 * (4 - X)) := by
        rw [mul_sub, hc]
        simp only [V, WPActualPullbackSource.Vpolynomial]
        ring
      _ = C (1 / 125 : ℚ) * ((X + 1) * (4 * X - 11)^2) := by rw [ht]
      _ = _ := by
        simp only [s, c, ←mul_assoc, ←C_mul]
        norm_num
  have hd : A * V.derivative = -3 * c * V := by
    have ht : (4 - X : ℚ[X]) * (4 * X - 1) *
        (((4 * X - 1)^2 * (4 - X)) : ℚ[X]).derivative =
        -3 * (4 * X - 11) * ((4 * X - 1)^2 * (4 - X)) := by
      norm_num [derivative_mul, derivative_pow_succ, derivative_X,
        derivative_sub, derivative_ofNat, derivative_one, zero_sub, C_ofNat]
      ring
    simp only [A, V, c, WPFiniteZSource.Abar, WPActualPullbackSource.Vpolynomial,
      mul_assoc, derivative_C_mul]
    linear_combination C (1 / 125 : ℚ) * ht
  have hn : 2 * ((p - 1) / 2) + 1 = p := by
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  have hk : (C (1 / 25 : ℚ) * s * c^2)^((p - 1) / 2) * c =
      C ((1 / 5 : ℚ)^(p - 1)) * s^((p - 1) / 2) * c^p := by
    rw [mul_pow, mul_pow, ←C_pow, ←pow_mul]
    have hnum : (1 / 25 : ℚ)^((p - 1) / 2) = (1 / 5 : ℚ)^(p - 1) := by
      rw [show (1 / 25 : ℚ) = (1 / 5)^2 by norm_num, ←pow_mul]
      congr 1
      omega
    rw [hnum]
    have hpow : c^(2 * ((p - 1) / 2)) * c = c^p := by rw [←pow_succ, hn]
    linear_combination C ((1 / 5 : ℚ)^(p - 1)) * s^((p - 1) / 2) * hpow
  have hkv : (1 - V)^((p - 1) / 2) * c =
      C ((1 / 5 : ℚ)^(p - 1)) * s^((p - 1) / 2) * c^p := by
    simpa only [hv] using hk
  have he := conicLogQ_source p
  change 2 * V * (conicLogQ p).derivative =
    ((1 - V)^((p - 1) / 2) - 1) * V.derivative at he
  have he2 : V * (2 * A * (conicLogQ p).derivative - 3 * c +
      C (3 * (1 / 5 : ℚ)^(p - 1)) * s^((p - 1) / 2) * c^p) = 0 := by
    rw [map_mul, map_ofNat]
    linear_combination A * he + ((1 - V)^((p - 1) / 2) - 1) * hd - 3 * V * hkv
  have hV0 : V ≠ 0 := by
    intro hz
    have h := congrArg (fun P : ℚ[X] => P.eval 0) hz
    norm_num [V, WPActualPullbackSource.Vpolynomial] at h
  have hz := (mul_eq_zero.mp he2).resolve_left hV0
  change 2 * A * (conicLogQ p).derivative - 3 * c =
    -C (3 * (1 / 5 : ℚ)^(p - 1)) * s^((p - 1) / 2) * c^p
  linear_combination hz

noncomputable def geometricJet (N : ℕ) (a : ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range N, C (a^j) * X^j

theorem geometricJet_source (N : ℕ) (a : ℚ) :
    (1 - C a * X) * geometricJet N a = 1 - C (a^N) * X^N := by
  simpa only [geometricJet, mul_pow, C_pow] using
    (mul_neg_geom_sum (C a * (X : ℚ[X])) N)

theorem geometricJet_coeff (N n : ℕ) (a : ℚ) :
    (geometricJet N a).coeff n = if n < N then a^n else 0 := by
  simp only [geometricJet, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp only [ite_true]
    · intro j hj hjn
      exact if_neg hjn.symm
    · intro hx
      exact (hx (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro j hj
    exact if_neg (by intro he; subst j; exact hn (Finset.mem_range.mp hj))

/-- The inverse of A is used only through the coefficient band that can contribute. -/
noncomputable def inverseAJet (N : ℕ) : ℚ[X] :=
  C (1 / 60 : ℚ) * geometricJet N (1 / 4) -
    C (4 / 15 : ℚ) * geometricJet N 4

theorem inverseAJet_source (N : ℕ) :
    (WPFiniteZSource.Abar : ℚ[X]) * inverseAJet N =
      1 + X^N * (-C ((1 / 15 : ℚ) * (1 / 4 : ℚ)^N) * (4 * X - 1) -
        C ((4 / 15 : ℚ) * (4 : ℚ)^N) * (4 - X)) := by
  have h1 := geometricJet_source N (1 / 4)
  have h4 := geometricJet_source N 4
  have hquarter : (4 : ℚ[X]) * C (1 / 4 : ℚ) = 1 := by
    change C 4 * C (1 / 4 : ℚ) = C 1
    rw [←C_mul]
    norm_num
  have h1s : (4 - X) * geometricJet N (1 / 4) =
      4 - 4 * C ((1 / 4 : ℚ)^N) * X^N := by
    calc
      _ = (4 - 4 * C (1 / 4 : ℚ) * X) * geometricJet N (1 / 4) := by
        rw [hquarter, one_mul]
      _ = 4 * ((1 - C (1 / 4 : ℚ) * X) * geometricJet N (1 / 4)) := by ring
      _ = _ := by rw [h1]; ring
  simp only [map_ofNat] at h4
  have ht : (4 - X) * (4 * X - 1) *
      (geometricJet N (1 / 4) - 16 * geometricJet N 4) =
      60 + X^N * (-4 * C ((1 / 4 : ℚ)^N) * (4 * X - 1) -
        16 * C ((4 : ℚ)^N) * (4 - X)) := by
    linear_combination (4 * X - 1) * h1s + 16 * (4 - X) * h4
  have hc60 : C (1 / 60 : ℚ) * 60 = (1 : ℚ[X]) := by
    change C (1 / 60 : ℚ) * C 60 = C 1
    rw [←C_mul]
    norm_num
  have hc4 : C (1 / 60 : ℚ) * 4 = C (1 / 15 : ℚ) := by
    change C (1 / 60 : ℚ) * C 4 = C (1 / 15 : ℚ)
    rw [←C_mul]
    norm_num
  have hc16 : C (1 / 60 : ℚ) * 16 = C (4 / 15 : ℚ) := by
    change C (1 / 60 : ℚ) * C 16 = C (4 / 15 : ℚ)
    rw [←C_mul]
    norm_num
  have hQ : inverseAJet N = C (1 / 60 : ℚ) *
      (geometricJet N (1 / 4) - 16 * geometricJet N 4) := by
    rw [inverseAJet, mul_sub, ←mul_assoc, hc16]
  have hright : 1 + X^N * (-C ((1 / 15 : ℚ) * (1 / 4 : ℚ)^N) * (4 * X - 1) -
        C ((4 / 15 : ℚ) * (4 : ℚ)^N) * (4 - X)) =
      C (1 / 60 : ℚ) * (60 + X^N * (-4 * C ((1 / 4 : ℚ)^N) * (4 * X - 1) -
        16 * C ((4 : ℚ)^N) * (4 - X))) := by
    rw [map_mul, map_mul, ←hc4, ←hc16, ←hc60]
    ring
  rw [hQ, hright]
  change (4 - X) * (4 * X - 1) *
      (C (1 / 60 : ℚ) * (geometricJet N (1 / 4) - 16 * geometricJet N 4)) = _
  linear_combination C (1 / 60 : ℚ) * ht

theorem inverseAJet_linear_source (N : ℕ) :
    C (3 / 2 : ℚ) * inverseAJet N * (4 * X - 11) =
      C (1 / 8 : ℚ) * geometricJet N (1 / 4) +
        4 * geometricJet N 4 +
        X^N * C ((2 / 5 : ℚ) * (1 / 4 : ℚ)^N - (2 / 5 : ℚ) * (4 : ℚ)^N) := by
  have h1 := geometricJet_source N (1 / 4)
  have h4 := geometricJet_source N 4
  have hquarter : (4 : ℚ[X]) * C (1 / 4 : ℚ) = 1 := by
    change C 4 * C (1 / 4 : ℚ) = C 1
    rw [←C_mul]
    norm_num
  have h1s : (4 - X) * geometricJet N (1 / 4) =
      4 - 4 * C ((1 / 4 : ℚ)^N) * X^N := by
    calc
      _ = (4 - 4 * C (1 / 4 : ℚ) * X) * geometricJet N (1 / 4) := by
        rw [hquarter, one_mul]
      _ = 4 * ((1 - C (1 / 4 : ℚ) * X) * geometricJet N (1 / 4)) := by ring
      _ = _ := by rw [h1]; ring
  simp only [map_ofNat] at h4
  have ht : (geometricJet N (1 / 4) - 16 * geometricJet N 4) * (4 * X - 11) =
      5 * geometricJet N (1 / 4) + 160 * geometricJet N 4 +
        16 * X^N * (C ((1 / 4 : ℚ)^N) - C ((4 : ℚ)^N)) := by
    linear_combination -4 * h1s + 16 * h4
  have hc16a : C (1 / 60 : ℚ) * 16 = C (4 / 15 : ℚ) := by
    change C (1 / 60 : ℚ) * C 16 = C (4 / 15 : ℚ)
    rw [←C_mul]
    norm_num
  have hQ : inverseAJet N = C (1 / 60 : ℚ) *
      (geometricJet N (1 / 4) - 16 * geometricJet N 4) := by
    rw [inverseAJet, mul_sub, ←mul_assoc, hc16a]
  have hc : C (3 / 2 : ℚ) * C (1 / 60 : ℚ) = C (1 / 40 : ℚ) := by
    rw [←C_mul]
    norm_num
  have hc5 : C (1 / 40 : ℚ) * 5 = C (1 / 8 : ℚ) := by
    change C (1 / 40 : ℚ) * C 5 = C (1 / 8 : ℚ)
    rw [←C_mul]
    norm_num
  have hc160 : C (1 / 40 : ℚ) * 160 = (4 : ℚ[X]) := by
    change C (1 / 40 : ℚ) * C 160 = C 4
    rw [←C_mul]
    norm_num
  have hc16 : C (1 / 40 : ℚ) * 16 = C (2 / 5 : ℚ) := by
    change C (1 / 40 : ℚ) * C 16 = C (2 / 5 : ℚ)
    rw [←C_mul]
    norm_num
  have hright : C (1 / 8 : ℚ) * geometricJet N (1 / 4) + 4 * geometricJet N 4 +
        X^N * C ((2 / 5 : ℚ) * (1 / 4 : ℚ)^N - (2 / 5 : ℚ) * (4 : ℚ)^N) =
      C (1 / 40 : ℚ) * (5 * geometricJet N (1 / 4) + 160 * geometricJet N 4 +
        16 * X^N * (C ((1 / 4 : ℚ)^N) - C ((4 : ℚ)^N))) := by
    rw [map_sub, map_mul, map_mul, ←hc5, ←hc160, ←hc16]
    ring
  rw [hQ, hright]
  calc
    _ = C (1 / 40 : ℚ) *
        ((geometricJet N (1 / 4) - 16 * geometricJet N 4) * (4 * X - 11)) := by
      rw [←mul_assoc, ←mul_assoc, hc]
    _ = _ := by rw [ht]

/-- An exact residue coefficient, before any division by p or field map. -/
noncomputable def reciprocalResidueQ (p : ℕ) : ℚ :=
  -3 * (1 / 5 : ℚ)^(p - 1 + (p - 1) / 2) *
    (inverseAJet ((p - 1) / 2) * (X + 1)^((p - 1) / 2) *
      (4 * X - 11)^p).coeff ((p - 1) / 2 - 1)

/-- Exact original-coefficient reciprocity, with the two unit-pole terms unchanged. -/
theorem logCIntegral_reciprocity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (logCIntegral p hp).val = -(2 : ℚ)^(p - 1) -
      1 / (2 * (2 : ℚ)^(p - 1)) - reciprocalResidueQ p / 2 := by
  let N := (p - 1) / 2
  let Q := inverseAJet N
  let A : ℚ[X] := WPFiniteZSource.Abar
  let c : ℚ[X] := 4 * X - 11
  let D := (conicLogQ p).derivative
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have high_zero (P : ℚ[X]) : (X^N * P).coeff (N - 1) = 0 := by
    rw [coeff_X_pow_mul', if_neg (by omega : ¬N ≤ N - 1)]
  have hQD : ((A * Q) * D).coeff (N - 1) = D.coeff (N - 1) := by
    dsimp only [A, Q]
    rw [inverseAJet_source, add_mul, one_mul, coeff_add]
    have htop := high_zero
      ((-C ((1 / 15 : ℚ) * (1 / 4 : ℚ)^N) * (4 * X - 1) -
        C ((4 / 15 : ℚ) * (4 : ℚ)^N) * (4 - X)) * D)
    rw [mul_assoc, htop, add_zero]
  have hsource : 2 * ((A * Q) * D) - 3 * (Q * c) =
      -C (3 * (1 / 5 : ℚ)^(p - 1 + N)) * (Q * (X + 1)^N * c^p) := by
    have hs := congrArg (fun P : ℚ[X] => Q * P) (conicLogQ_Abar_source p hp)
    change Q * (2 * A * D - 3 * c) =
      Q * (-C (3 * (1 / 5 : ℚ)^(p - 1)) *
        (C (1 / 5 : ℚ) * (X + 1))^N * c^p) at hs
    simp only [mul_pow, pow_add, map_mul, map_pow, map_ofNat] at hs ⊢
    linear_combination hs
  have hco := congrArg (fun P : ℚ[X] => P.coeff (N - 1)) hsource
  change (C (2 : ℚ) * ((A * Q) * D) - C (3 : ℚ) * (Q * c)).coeff (N - 1) =
    (-C (3 * (1 / 5 : ℚ)^(p - 1 + N)) * (Q * (X + 1)^N * c^p)).coeff (N - 1) at hco
  simp only [coeff_sub, neg_mul, coeff_neg, coeff_C_mul, hQD] at hco
  have hlin := congrArg (fun P : ℚ[X] => P.coeff (N - 1))
    (inverseAJet_linear_source N)
  rw [mul_assoc] at hlin
  change (C (3 / 2 : ℚ) * (Q * c)).coeff (N - 1) =
    (C (1 / 8 : ℚ) * geometricJet N (1 / 4) +
      C (4 : ℚ) * geometricJet N 4 +
      X^N * C ((2 / 5 : ℚ) * (1 / 4 : ℚ)^N - (2 / 5 : ℚ) * (4 : ℚ)^N)).coeff (N - 1) at hlin
  simp only [coeff_C_mul, coeff_add, geometricJet_coeff,
    if_pos (by omega : N - 1 < N), high_zero] at hlin
  have hpow : (4 : ℚ)^N = (4 : ℚ)^(N - 1) * 4 := by
    rw [←pow_succ, Nat.sub_add_cancel hN]
  have hlead : (1 / 8 : ℚ) * (1 / 4 : ℚ)^(N - 1) + 4 * (4 : ℚ)^(N - 1) =
      (4 : ℚ)^N + 1 / (2 * (4 : ℚ)^N) := by
    rw [one_div_pow, hpow]
    field_simp [pow_ne_zero (N - 1) (by norm_num : (4 : ℚ) ≠ 0)]
    ring
  have hp1 : p - 1 = 2 * N := by
    have hn := WPFiniteWSource.half_exponent p hp
    dsimp only [N]
    omega
  have hU : (2 : ℚ)^(p - 1) = (4 : ℚ)^N := by rw [hp1, pow_mul]; norm_num
  have hD : -D.coeff (N - 1) = (logCIntegral p hp).val := by
    rw [logCIntegral_value p hp]
    change -(conicLogQ p).derivative.coeff (N - 1) =
      -(N : ℚ) * (conicLogQ p).coeff N
    rw [coeff_derivative, Nat.sub_add_cancel hN]
    have hc : ((N - 1 : ℕ) : ℚ) + 1 = (N : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel hN
    rw [hc]
    ring
  have hco' : 2 * D.coeff (N - 1) - 3 * (Q * c).coeff (N - 1) =
      reciprocalResidueQ p := by
    convert hco using 1
    dsimp only [reciprocalResidueQ, N, Q, c]
    ring
  change (3 / 2 : ℚ) * (Q * c).coeff (N - 1) =
    (1 / 8 : ℚ) * (1 / 4 : ℚ)^(N - 1) + 4 * (4 : ℚ)^(N - 1) + 0 at hlin
  rw [hlead, ←hU] at hlin
  linear_combination -hD - (1 / 2 : ℚ) * hco' - hlin

/-- The intermediate binomial contraction, with every denominator retained. -/
theorem binomial_contraction {K : Type*} [Field K] (m : ℕ) (hm : 0 < m)
    (hm0 : (m : K) ≠ 0) (hk0 : ∀ k < m, ((k + 1 : ℕ) : K) ≠ 0) (r : K) :
    (∑ k ∈ Finset.range m,
      (Nat.choose (m - 1) k : K) * r^(k + 1) / ((k + 1 : ℕ) : K)) =
      ((1 + r)^m - 1) / (m : K) := by
  have hterm (k : ℕ) (hk : k < m) :
      (m : K) * ((Nat.choose (m - 1) k : K) * r^(k + 1) /
        ((k + 1 : ℕ) : K)) = (Nat.choose m (k + 1) : K) * r^(k + 1) := by
    have hc := Nat.add_one_mul_choose_eq (m - 1) k
    rw [Nat.sub_add_cancel hm] at hc
    have hcast := congrArg (fun n : ℕ => (n : K)) hc
    simp only [Nat.cast_mul] at hcast
    rw [←mul_div_assoc]
    apply (div_eq_iff (hk0 k hk)).2
    linear_combination r^(k + 1) * hcast
  have hsum : (m : K) * (∑ k ∈ Finset.range m,
      (Nat.choose (m - 1) k : K) * r^(k + 1) / ((k + 1 : ℕ) : K)) =
      ∑ k ∈ Finset.range m, (Nat.choose m (k + 1) : K) * r^(k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  have hbin := add_pow r (1 : K) m
  rw [Finset.sum_range_succ'] at hbin
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one] at hbin
  have hpow : (1 + r)^m - 1 =
      ∑ k ∈ Finset.range m, (Nat.choose m (k + 1) : K) * r^(k + 1) := by
    rw [add_comm 1 r, hbin]
    rw [add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  apply (eq_div_iff hm0).2
  linear_combination hsum - hpow

noncomputable def halfLog {K : Type*} [Field K] (N : ℕ) (z : K) : K :=
  ∑ m ∈ Finset.range N, z^(m + 1) / ((m + 1 : ℕ) : K)

/-- The top half coefficient vanishes through its actual factor, before summing. -/
theorem top_half_factor {K : Type*} [Field K] (N : ℕ) (h4 : (4 : K) ≠ 0) :
    1 - (4 : K)^N / (4 : K)^N = 0 := by
  rw [div_self (pow_ne_zero _ h4), sub_self]

/-- The four literal finite logarithms are the contracted reciprocal source. -/
theorem reciprocal_log_contraction {K : Type*} [Field K] (N : ℕ)
    (h4N : (4 : K)^N = 1) :
    (∑ m ∈ Finset.range N,
      ((3 / 11 : K)^(m + 1) - (1 / 5 : K)^(m + 1)) /
        ((m + 1 : ℕ) : K) *
        (1 - (4 : K)^(m + 1) / (4 : K)^N)) =
      halfLog N (3 / 11 : K) - halfLog N (12 / 11 : K) +
        halfLog N (4 / 5 : K) - halfLog N (1 / 5 : K) := by
  rw [h4N]
  simp only [div_one, halfLog, ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have h12 : (12 / 11 : K)^(m + 1) =
      (3 / 11 : K)^(m + 1) * (4 : K)^(m + 1) := by
    rw [←mul_pow]
    congr 1
    ring
  have h45 : (4 / 5 : K)^(m + 1) =
      (1 / 5 : K)^(m + 1) * (4 : K)^(m + 1) := by
    rw [←mul_pow]
    congr 1
    ring
  rw [h12, h45]
  ring

/-- The k=0 extreme and every intermediate negative-binomial index share one row. -/
def infinityBinomialRow (m k : ℕ) : ℕ :=
  if m = 0 then if k = 0 then 1 else 0 else
    if k = 0 then 0 else Nat.choose (m - 1) (k - 1)

theorem infinityBinomialRow_pascal (m k : ℕ) :
    infinityBinomialRow (m + 1) (k + 1) =
      infinityBinomialRow m k + infinityBinomialRow m (k + 1) := by
  cases m with
  | zero => cases k <;> simp [infinityBinomialRow]
  | succ m =>
    cases k with
    | zero => simp [infinityBinomialRow]
    | succ k => simp [infinityBinomialRow, Nat.choose_succ_succ]

noncomputable def infinityKernelQ (N k : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N, (infinityBinomialRow m k : ℚ) *
    (1 / 5 : ℚ)^m * (1 - (4 : ℚ)^m / (4 : ℚ)^N)

theorem infinityKernelQ_extreme (N : ℕ) (hN : 0 < N) :
    infinityKernelQ N 0 = 1 - 1 / (4 : ℚ)^N := by
  unfold infinityKernelQ
  rw [Finset.sum_eq_single 0]
  · simp [infinityBinomialRow]
  · intro m hm hm0
    simp [infinityBinomialRow, hm0]
  · intro hz
    exact (hz (Finset.mem_range.mpr hN)).elim

/-- Pascal recurrence for the complete infinity source, including the zero top factor. -/
theorem infinityKernelQ_succ (N k : ℕ) :
    infinityKernelQ (N + 1) (k + 1) =
      (infinityKernelQ N k + infinityKernelQ N (k + 1)) / 5 := by
  unfold infinityKernelQ
  rw [Finset.sum_range_succ']
  have hz : (infinityBinomialRow 0 (k + 1) : ℚ) = 0 := by
    simp [infinityBinomialRow]
  rw [hz, zero_mul, zero_mul, add_zero]
  rw [←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [infinityBinomialRow_pascal, Nat.cast_add, pow_succ, pow_succ]
  have h4 : (4 : ℚ)^N ≠ 0 := pow_ne_zero N (by norm_num)
  field_simp [h4]
  ring

theorem geometricJet_binomial_coefficient (N : ℕ) (a : ℚ) :
    (geometricJet (N + 1) a * (1 + X)^N).coeff N = (1 + a)^N := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hb := add_pow a (1 : ℚ) N
  rw [add_comm 1 a, hb]
  simp only [one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := by have hh := Finset.mem_range.mp hj; omega
  rw [geometricJet_coeff, if_pos (Finset.mem_range.mp hj), coeff_one_add_X_pow,
    Nat.choose_symm hjN]

theorem geometricJet_binomial_lower (N : ℕ) (hN : 0 < N) (a : ℚ) (ha : a ≠ 0) :
    (geometricJet N a * (1 + X)^N).coeff (N - 1) = ((1 + a)^N - 1) / a := by
  have hs := congrArg (fun P : ℚ[X] => (P * (1 + X)^N).coeff N)
    (geometricJet_source N a)
  have he : geometricJet (N + 1) a = geometricJet N a + C (a^N) * X^N := by
    simp only [geometricJet, Finset.sum_range_succ]
  have hb := geometricJet_binomial_coefficient N a
  rw [he, add_mul, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', if_pos (le_refl N), Nat.sub_self,
    coeff_one_add_X_pow, Nat.choose_zero_right, Nat.cast_one, mul_one] at hb
  have hs' : (geometricJet N a * (1 + X)^N).coeff N -
      a * (geometricJet N a * (1 + X)^N).coeff (N - 1) = 1 - a^N := by
    have hpoly : (1 - C a * X) * geometricJet N a * (1 + X)^N =
        geometricJet N a * (1 + X)^N -
          C a * ((geometricJet N a * (1 + X)^N) * X) := by ring
    have hX : ((geometricJet N a * (1 + X)^N) * X).coeff N =
        (geometricJet N a * (1 + X)^N).coeff (N - 1) := by
      simpa only [pow_one, if_pos (Nat.succ_le_of_lt hN)] using
        (coeff_mul_X_pow' (geometricJet N a * (1 + X)^N) 1 N)
    rw [hpoly, coeff_sub, coeff_C_mul, hX] at hs
    have hR : ((1 - C (a^N) * X^N) * (1 + X)^N).coeff N = 1 - a^N := by
      rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul,
        coeff_X_pow_mul', if_pos (le_refl N), Nat.sub_self,
        coeff_one_add_X_pow, coeff_one_add_X_pow,
        Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    simpa only [hR] using hs
  apply (eq_div_iff ha).2
  linear_combination hb - hs'

noncomputable def coefficientKernelQ (N k : ℕ) : ℚ :=
  if k < N then -15 * (1 / 5 : ℚ)^N *
    (inverseAJet N * (1 + X)^N).coeff (N - 1 - k) else 0

theorem coefficientKernelQ_extreme (N : ℕ) (hN : 0 < N) :
    coefficientKernelQ N 0 = 1 - 1 / (4 : ℚ)^N := by
  rw [coefficientKernelQ, if_pos hN, Nat.sub_zero, inverseAJet, sub_mul,
    coeff_sub]
  simp only [mul_assoc, coeff_C_mul]
  rw [
    geometricJet_binomial_lower N hN (1 / 4) (by norm_num),
    geometricJet_binomial_lower N hN 4 (by norm_num)]
  norm_num
  rw [div_pow (5 : ℚ) (4 : ℚ) N, one_div_pow]
  have h5 : (5 : ℚ)^N ≠ 0 := pow_ne_zero N (by norm_num)
  have h4 : (4 : ℚ)^N ≠ 0 := pow_ne_zero N (by norm_num)
  field_simp [h4, h5]
  ring

theorem inverseAJet_coeff (N n : ℕ) :
    (inverseAJet N).coeff n = if n < N then
      (1 / 60 : ℚ) * (1 / 4 : ℚ)^n - (4 / 15 : ℚ) * (4 : ℚ)^n else 0 := by
  rw [inverseAJet, coeff_sub, coeff_C_mul, coeff_C_mul,
    geometricJet_coeff, geometricJet_coeff]
  split_ifs <;> ring

theorem inverseAJet_mul_stable (N n : ℕ) (hn : n < N) (P : ℚ[X]) :
    (inverseAJet (N + 1) * P).coeff n = (inverseAJet N * P).coeff n := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hi : i < N := by have hh := Finset.mem_antidiagonal.mp hij; omega
  rw [inverseAJet_coeff, inverseAJet_coeff, if_pos (by omega : i < N + 1), if_pos hi]

/-- The original reciprocal coefficient has the same Pascal recurrence as the full pole source. -/
theorem coefficientKernelQ_succ (N k : ℕ) :
    coefficientKernelQ (N + 1) (k + 1) =
      (coefficientKernelQ N k + coefficientKernelQ N (k + 1)) / 5 := by
  by_cases hk : k < N
  · rw [coefficientKernelQ, if_pos (by omega : k + 1 < N + 1),
      coefficientKernelQ, if_pos hk]
    have hn : N + 1 - 1 - (k + 1) = N - 1 - k := by omega
    rw [hn, pow_succ (1 + X : ℚ[X]) N,
      inverseAJet_mul_stable N (N - 1 - k) (by omega) ((1 + X)^N * (1 + X))]
    have he : inverseAJet N * ((1 + X)^N * (1 + X)) =
        inverseAJet N * (1 + X)^N + (inverseAJet N * (1 + X)^N) * X := by ring
    rw [he, coeff_add]
    by_cases hk1 : k + 1 < N
    · have hX : ((inverseAJet N * (1 + X)^N) * X).coeff (N - 1 - k) =
          (inverseAJet N * (1 + X)^N).coeff (N - 1 - (k + 1)) := by
        have hr : N - 1 - k - 1 = N - 1 - (k + 1) := by omega
        simpa only [pow_one, if_pos (by omega : 1 ≤ N - 1 - k), hr] using
          (coeff_mul_X_pow' (inverseAJet N * (1 + X)^N) 1 (N - 1 - k))
      rw [hX, coefficientKernelQ, if_pos hk1, pow_succ]
      ring
    · have hz : N - 1 - k = 0 := by omega
      rw [hz, coeff_mul_X_zero, coefficientKernelQ, if_neg hk1, pow_succ]
      ring
  · rw [coefficientKernelQ, if_neg (by omega : ¬k + 1 < N + 1),
      coefficientKernelQ, if_neg hk, coefficientKernelQ,
      if_neg (by omega : ¬k + 1 < N)]
    ring

/-- Exact contraction from the original reciprocal coefficient to all binomial indices. -/
theorem coefficientKernelQ_eq_infinity (N k : ℕ) :
    coefficientKernelQ N k = infinityKernelQ N k := by
  induction N generalizing k with
  | zero => simp [coefficientKernelQ, infinityKernelQ]
  | succ N ih =>
    cases k with
    | zero =>
      rw [coefficientKernelQ_extreme (N + 1) (by omega),
        infinityKernelQ_extreme (N + 1) (by omega)]
    | succ k =>
      rw [coefficientKernelQ_succ, infinityKernelQ_succ, ih, ih]

theorem coefficient_binomial_band (P : ℚ[X]) (a b : ℚ) (p n : ℕ) :
    (P * (C a * X + C b)^p).coeff n =
      ∑ k ∈ Finset.range (p + 1),
        (Nat.choose p k : ℚ) * a^k * b^(p - k) *
          (if k ≤ n then P.coeff (n - k) else 0) := by
  rw [add_pow, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_pow, ←C_pow]
  rw [show (Nat.choose p k : ℚ[X]) = C (Nat.choose p k : ℚ) by
    simp only [map_natCast]]
  have he : P * (C (a^k) * X^k * C (b^(p - k)) * C (Nat.choose p k : ℚ)) =
      C ((Nat.choose p k : ℚ) * a^k * b^(p - k)) * (P * X^k) := by
    simp only [map_mul]
    ring
  rw [he, coeff_C_mul, coeff_mul_X_pow']

/-- The exact residue coefficient is the complete infinity source of
`Z=v*(3-11*v^2)/(5*v^2-1)`. Its inverse-power rows retain both CM poles
before division; the second extreme and all excluded indices vanish by the
proved coefficient band, and the top half index retains its zero factor. -/
theorem reciprocalResidueQ_binomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    reciprocalResidueQ p =
      ∑ k ∈ Finset.range ((p - 1) / 2), (Nat.choose p k : ℚ) *
        (-11 / 5 : ℚ)^(p - k) * (4 / 5 : ℚ)^k *
          infinityKernelQ ((p - 1) / 2) k := by
  let N := (p - 1) / 2
  let P : ℚ[X] := inverseAJet N * (X + 1)^N
  have hN : 0 < N := by dsimp only [N]; omega
  have hNp : N ≤ p + 1 := by dsimp only [N]; omega
  have hc : (4 * X - 11 : ℚ[X]) = C (4 : ℚ) * X + C (-11 : ℚ) := by
    simp only [map_neg, map_ofNat]
    ring
  have hb := coefficient_binomial_band P 4 (-11) p (N - 1)
  rw [←hc] at hb
  rw [←Finset.sum_range_add_sum_Ico _ hNp] at hb
  have ht : (∑ k ∈ Finset.Ico N (p + 1),
      (Nat.choose p k : ℚ) * (4 : ℚ)^k * (-11 : ℚ)^(p - k) *
        (if k ≤ N - 1 then P.coeff (N - 1 - k) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by have hh := Finset.mem_Ico.mp hk; omega), mul_zero]
  rw [ht, add_zero] at hb
  change -3 * (1 / 5 : ℚ)^(p - 1 + N) * (P * (4 * X - 11)^p).coeff (N - 1) = _
  rw [hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k < N := Finset.mem_range.mp hk
  have hkp : k ≤ p := by have hn := WPFiniteWSource.half_exponent p hp; dsimp only [N] at hkN; omega
  rw [←coefficientKernelQ_eq_infinity, coefficientKernelQ, if_pos hkN,
    if_pos (by omega : k ≤ N - 1)]
  rw [add_comm (1 : ℚ[X]) X]
  have h5 : (1 / 5 : ℚ)^(p - 1) = 5 * (1 / 5 : ℚ)^p := by
    have hh : (1 / 5 : ℚ)^p = (1 / 5 : ℚ)^(p - 1) * (1 / 5) := by
      rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    linear_combination -5 * hh
  have hpow : (-11 / 5 : ℚ)^(p - k) * (4 / 5 : ℚ)^k =
      (-11 : ℚ)^(p - k) * (4 : ℚ)^k * (1 / 5 : ℚ)^p := by
    rw [show (-11 / 5 : ℚ) = (-11) * (1 / 5) by ring,
      show (4 / 5 : ℚ) = 4 * (1 / 5) by ring, mul_pow, mul_pow]
    have hh : (1 / 5 : ℚ)^(p - k) * (1 / 5 : ℚ)^k = (1 / 5 : ℚ)^p := by
      rw [←pow_add, Nat.sub_add_cancel hkp]
    linear_combination (-11 : ℚ)^(p - k) * (4 : ℚ)^k * hh
  rw [pow_add, h5]
  have hr : (Nat.choose p k : ℚ) * (-11 / 5 : ℚ)^(p - k) * (4 / 5 : ℚ)^k =
      (Nat.choose p k : ℚ) * ((-11 / 5 : ℚ)^(p - k) * (4 / 5 : ℚ)^k) := by ring
  rw [hr, hpow]
  ring

noncomputable def infinityKernelIntegral (p : ℕ) [Fact p.Prime] (N k : ℕ) :
    integralRationals p :=
  ∑ m ∈ Finset.range N, (infinityBinomialRow m k : integralRationals p) *
    (smallIntegralInverse p 5)^m *
    (1 - (4 : integralRationals p)^m * (smallIntegralInverse p 2)^(p - 1))

/-- The actual infinity residue divided by p, with the original extreme power retained. -/
noncomputable def reciprocalResidueDigitIntegral (p : ℕ) [Fact p.Prime] :
    integralRationals p :=
  (-11 * smallIntegralInverse p 5)^p *
      (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
      (smallIntegralInverse p 2)^(p - 1) +
    ∑ k ∈ Finset.Ico 1 ((p - 1) / 2),
      ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : integralRationals p)) *
        (-11 * smallIntegralInverse p 5)^(p - k) *
        (4 * smallIntegralInverse p 5)^k *
        infinityKernelIntegral p ((p - 1) / 2) k

/-- The C digit is constructed from the original rational coefficient reciprocity. -/
noncomputable def logCDigitIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) +
    (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
      (smallIntegralInverse p 2)^(p - 1) * smallIntegralInverse p 2 -
    smallIntegralInverse p 2 * reciprocalResidueDigitIntegral p

/-- The added top half factor vanishes in the actual integral lift before p-division. -/
theorem infinityKernel_top_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    1 - (4 : integralRationals p)^((p - 1) / 2) *
      (smallIntegralInverse p 2)^(p - 1) = 0 := by
  apply Subtype.ext
  change (integralRationals p).subtype
    (1 - (4 : integralRationals p)^((p - 1) / 2) *
      (smallIntegralInverse p 2)^(p - 1)) = 0
  rw [map_sub, map_one, map_mul, map_pow, map_ofNat, map_pow]
  change 1 - (4 : ℚ)^((p - 1) / 2) * (smallIntegralInverse p 2).val^(p - 1) = 0
  rw [smallIntegralInverse_value p 2 (by omega) (by omega)]
  simp only [Nat.cast_ofNat]
  have hn : p - 1 = 2 * ((p - 1) / 2) := by
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  have hphase : (1 / 2 : ℚ)^(p - 1) = (1 / 4 : ℚ)^((p - 1) / 2) := by
    rw [hn, pow_mul]
    norm_num
  rw [hphase]
  rw [one_div_pow, mul_one_div_cancel (pow_ne_zero _ (by norm_num : (4 : ℚ) ≠ 0)), sub_self]

theorem infinityKernelIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℕ) :
    (infinityKernelIntegral p ((p - 1) / 2) k).val =
      infinityKernelQ ((p - 1) / 2) k := by
  have hn : p - 1 = 2 * ((p - 1) / 2) := by
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  have hphase : (1 / 2 : ℚ)^(p - 1) = (1 / 4 : ℚ)^((p - 1) / 2) := by
    rw [hn, pow_mul]
    norm_num
  change (integralRationals p).subtype (infinityKernelIntegral p ((p - 1) / 2) k) = _
  simp only [infinityKernelIntegral, infinityKernelQ, map_sum, map_mul,
    map_natCast, map_pow, map_sub, map_one, map_ofNat, Subring.subtype_apply]
  rw [smallIntegralInverse_value p 5 (by omega) (by omega),
    smallIntegralInverse_value p 2 (by omega) (by omega)]
  simp only [Nat.cast_ofNat]
  rw [hphase]
  apply Finset.sum_congr rfl
  intro m hm
  rw [one_div_pow (4 : ℚ) ((p - 1) / 2)]
  ring

theorem infinityKernelIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (N k : ℕ) :
    residueHom p (infinityKernelIntegral p N k) =
      ∑ m ∈ Finset.range N, (infinityBinomialRow m k : ZMod p) *
        (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hpow : ((2 : ZMod p)⁻¹)^(p - 1) = 1 := by
    apply mul_right_cancel₀ (inv_ne_zero h2)
    rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
      ZMod.pow_card, one_mul]
  simp only [infinityKernelIntegral, map_sum, map_mul, map_natCast, map_pow,
    map_sub, map_one, map_ofNat,
    smallIntegralInverse_field p 5 (by omega) (by omega),
    smallIntegralInverse_field p 2 (by omega) (by omega), Nat.cast_ofNat,
    hpow, mul_one, one_div]

theorem reciprocalResidueDigitIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (reciprocalResidueDigitIntegral p).val = reciprocalResidueQ p / (p : ℚ) := by
  let N := (p - 1) / 2
  let a : ℚ := -11 / 5
  let b : ℚ := 4 / 5
  let q : ℚ := (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hn : p - 1 = 2 * N := by
    have hh := WPFiniteWSource.half_exponent p hp
    dsimp only [N]
    omega
  have hphase : (1 / 2 : ℚ)^(p - 1) = 1 / (4 : ℚ)^N := by
    rw [hn, pow_mul]
    simp only [show (1 / 2 : ℚ)^2 = (1 / 4 : ℚ) by norm_num]
    rw [one_div_pow]
  have hq : q * (p : ℚ) = (2 : ℚ)^(p - 1) - 1 := by
    dsimp only [q]
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2
      (by simpa using small_cast_ne_zero p 2 (by omega) (by omega))
  have hU : (2 : ℚ)^(p - 1) = (4 : ℚ)^N := by rw [hn, pow_mul]; norm_num
  have hext : a^p * (1 - 1 / (4 : ℚ)^N) =
      (p : ℚ) * (a^p * q * (1 / 2 : ℚ)^(p - 1)) := by
    rw [hphase]
    have h4 : (4 : ℚ)^N ≠ 0 := pow_ne_zero N (by norm_num)
    field_simp [h4]
    rw [hU] at hq
    linear_combination -a^p * hq
  have hchoose (k : ℕ) (hk : k ∈ Finset.Ico 1 N) :
      (Nat.choose p k : ℚ) = (p : ℚ) *
        ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : ℚ)) := by
    have hk0 : k ≠ 0 := by have hh := Finset.mem_Ico.mp hk; omega
    have hkp : k < p := by
      have hh := Finset.mem_Ico.mp hk
      have hhalf := WPFiniteWSource.half_exponent p hp
      dsimp only [N] at hh
      omega
    have hd : (p : ℤ) ∣ (Nat.choose p k : ℤ) := by
      exact_mod_cast (Fact.out : p.Prime).dvd_choose_self hk0 hkp
    exact_mod_cast (Int.mul_ediv_cancel' hd).symm
  have hd : (reciprocalResidueDigitIntegral p).val =
      a^p * q * (1 / 2 : ℚ)^(p - 1) +
      ∑ k ∈ Finset.Ico 1 N,
        ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : ℚ)) * a^(p - k) * b^k *
          infinityKernelQ N k := by
    change (integralRationals p).subtype (reciprocalResidueDigitIntegral p) = _
    simp only [reciprocalResidueDigitIntegral, map_add, map_sum, map_mul,
      map_pow, map_intCast, map_neg, map_ofNat,
      Subring.subtype_apply, smallIntegralInverse_value p 5 (by omega) (by omega),
      smallIntegralInverse_value p 2 (by omega) (by omega),
      infinityKernelIntegral_value p hp]
    dsimp only [a, b, q, N]
    norm_num
  have hr := reciprocalResidueQ_binomial p hp
  change reciprocalResidueQ p =
    ∑ k ∈ Finset.range N, (Nat.choose p k : ℚ) * a^(p - k) * b^k * infinityKernelQ N k at hr
  rw [←Finset.sum_range_add_sum_Ico _ hN] at hr
  simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one,
    Nat.sub_zero, pow_zero, one_mul, mul_one, infinityKernelQ_extreme N (by omega)] at hr
  have hR : reciprocalResidueQ p = (p : ℚ) * (reciprocalResidueDigitIntegral p).val := by
    rw [hr, hd, mul_add, Finset.mul_sum, hext]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hchoose k hk]
    ring
  apply (eq_div_iff hp0).2
  rw [hR]
  ring

/-- Exact p-division of the original narrow C coefficient, before its field digit is summed. -/
theorem logCDigitIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (logCDigitIntegral p).val = ((logCIntegral p hp).val + 3 / 2) / (p : ℚ) := by
  let q : ℚ := (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : (2 : ℚ)^(p - 1) ≠ 0 := pow_ne_zero (p - 1) (by norm_num)
  have hq : q * (p : ℚ) = (2 : ℚ)^(p - 1) - 1 := by
    dsimp only [q]
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2
      (by simpa using small_cast_ne_zero p 2 (by omega) (by omega))
  have hq' : q = ((2 : ℚ)^(p - 1) - 1) / (p : ℚ) := (eq_div_iff hp0).2 hq
  change (integralRationals p).subtype (logCDigitIntegral p) = _
  simp only [logCDigitIntegral, map_sub, map_add, map_mul, map_neg, map_intCast,
    map_pow, Subring.subtype_apply, smallIntegralInverse_value p 2 (by omega) (by omega),
    reciprocalResidueDigitIntegral_value p hp]
  change -q + q * (1 / 2 : ℚ)^(p - 1) * (1 / 2) -
    (1 / 2) * (reciprocalResidueQ p / (p : ℚ)) = _
  rw [logCIntegral_reciprocity p hp, one_div_pow, hq']
  field_simp [hp0, hU]
  ring

/-- The actual integral first difference preserves the original rational division. -/
theorem logCIntegral_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    logCIntegral p hp = -3 * smallIntegralInverse p 2 +
      (p : integralRationals p) * logCDigitIntegral p := by
  apply Subtype.ext
  change (logCIntegral p hp).val =
    -3 * (smallIntegralInverse p 2).val + (p : ℚ) * (logCDigitIntegral p).val
  rw [smallIntegralInverse_value p 2 (by omega) (by omega), logCDigitIntegral_value p hp]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [Nat.cast_ofNat]
  field_simp [hp0]
  ring

theorem divided_binomial_pair_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (k : ℕ) (hk : k ∈ Finset.Ico 1 p) :
    ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : ZMod p)) *
        (-11 / 5 : ZMod p)^(p - k) * (4 / 5 : ZMod p)^k =
      (11 / 5 : ZMod p) * (4 / 11 : ZMod p)^k / (k : ZMod p) := by
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hkp : k ≤ p := (Finset.mem_Ico.mp hk).2.le
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h11 : (11 : ZMod p) ≠ 0 := small_cast_ne_zero p 11 (by omega) (by omega)
  have hb : (4 / 5 : ZMod p) = (-11 / 5 : ZMod p) * (-4 / 11) := by
    field_simp [h5, h11]
  have hpw : (-11 / 5 : ZMod p)^(p - k) * (4 / 5 : ZMod p)^k =
      (-11 / 5 : ZMod p) * (-4 / 11 : ZMod p)^k := by
    rw [hb, mul_pow]
    calc
      _ = ((-11 / 5 : ZMod p)^(p - k) * (-11 / 5 : ZMod p)^k) *
          (-4 / 11 : ZMod p)^k := by ring
      _ = _ := by rw [←pow_add, Nat.sub_add_cancel hkp, ZMod.pow_card]
  have hs : (-1 : ZMod p)^k = -(-1)^(k - 1) := by
    calc
      _ = (-1 : ZMod p)^(k - 1) * (-1) := by
        rw [←pow_succ, Nat.sub_add_cancel hk1]
      _ = _ := by ring
  have hsq : ((-1 : ZMod p)^(k - 1))^2 = 1 := by
    rw [←pow_mul, Nat.mul_comm (k - 1) 2, pow_mul]
    norm_num
  have hsign : (-1 : ZMod p)^(k - 1) * (-4 / 11 : ZMod p)^k =
      -(4 / 11 : ZMod p)^k := by
    rw [show (-4 / 11 : ZMod p) = -(4 / 11) by ring,
      neg_pow (4 / 11 : ZMod p) k, hs]
    calc
      _ = -((-1 : ZMod p)^(k - 1))^2 * (4 / 11 : ZMod p)^k := by ring
      _ = _ := by rw [hsq]; ring
  rw [WPFiniteInversion.divided_choose_cast p k hk]
  calc
    _ = (-11 / 5 : ZMod p) *
        ((-1 : ZMod p)^(k - 1) * (-4 / 11 : ZMod p)^k) / (k : ZMod p) := by
      have hh := congrArg (fun z : ZMod p => (-1 : ZMod p)^(k - 1) / (k : ZMod p) * z) hpw
      linear_combination hh
    _ = _ := by rw [hsign]; ring

theorem binomial_contraction_Ico {K : Type*} [Field K] (m : ℕ) (hm : 0 < m)
    (hm0 : (m : K) ≠ 0) (hk0 : ∀ k < m, ((k + 1 : ℕ) : K) ≠ 0) (r : K) :
    (∑ k ∈ Finset.Ico 1 (m + 1),
      (Nat.choose (m - 1) (k - 1) : K) * r^k / (k : K)) =
      ((1 + r)^m - 1) / (m : K) := by
  rw [←Finset.sum_Ico_add' (fun k =>
    (Nat.choose (m - 1) (k - 1) : K) * r^k / (k : K)) 0 m 1]
  simpa only [Nat.zero_add, Nat.Ico_zero_eq_range, Nat.add_sub_cancel] using
    binomial_contraction m hm hm0 hk0 r

theorem infinity_intermediate_field_contraction (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (∑ k ∈ Finset.Ico 1 ((p - 1) / 2), (4 / 11 : ZMod p)^k / (k : ZMod p) *
      ∑ m ∈ Finset.range ((p - 1) / 2), (infinityBinomialRow m k : ZMod p) *
        (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m)) =
      halfLog ((p - 1) / 2) (3 / 11 : ZMod p) -
        halfLog ((p - 1) / 2) (12 / 11 : ZMod p) +
        halfLog ((p - 1) / 2) (4 / 5 : ZMod p) -
        halfLog ((p - 1) / 2) (1 / 5 : ZMod p) := by
  let N := (p - 1) / 2
  let f (m : ℕ) : ZMod p :=
    ((3 / 11 : ZMod p)^m - (1 / 5 : ZMod p)^m) / (m : ZMod p) *
      (1 - (4 : ZMod p)^m)
  have hNp : N < p := by
    have hh := WPFiniteWSource.half_exponent p hp
    dsimp only [N]
    omega
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h11 : (11 : ZMod p) ≠ 0 := small_cast_ne_zero p 11 (by omega) (by omega)
  have h4N : (4 : ZMod p)^N = 1 := by
    have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
    have hpow : (2 : ZMod p)^(p - 1) = 1 := by
      apply mul_right_cancel₀ h2
      rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le, ZMod.pow_card, one_mul]
    have hn : p - 1 = 2 * N := by
      have hh := WPFiniteWSource.half_exponent p hp
      dsimp only [N]
      omega
    rw [hn, pow_mul] at hpow
    norm_num at hpow
    exact hpow
  have hinner (m : ℕ) (hm : m ∈ Finset.range N) :
      (∑ k ∈ Finset.Ico 1 N,
        (4 / 11 : ZMod p)^k / (k : ZMod p) * (infinityBinomialRow m k : ZMod p) *
          (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m)) = f m := by
    by_cases hm0 : m = 0
    · subst m
      simp only [infinityBinomialRow, pow_zero, sub_self, mul_zero, f]
      simp
    · have hm1 : 1 ≤ m := by omega
      have hmN : m < N := Finset.mem_range.mp hm
      have hmcast : (m : ZMod p) ≠ 0 := small_cast_ne_zero p m hm1 (hmN.trans hNp)
      have hkcast : ∀ k < m, ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
        intro k hk
        exact small_cast_ne_zero p (k + 1) (by omega) (by omega)
      have htail : (∑ k ∈ Finset.Ico (m + 1) N,
          (Nat.choose (m - 1) (k - 1) : ZMod p) * (4 / 11 : ZMod p)^k /
            (k : ZMod p)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Nat.choose_eq_zero_of_lt (by have hh := Finset.mem_Ico.mp hk; omega),
          Nat.cast_zero, zero_mul, zero_div]
      have hc := binomial_contraction_Ico m (by omega) hmcast hkcast (4 / 11 : ZMod p)
      have hsum : (∑ k ∈ Finset.Ico 1 N,
          (Nat.choose (m - 1) (k - 1) : ZMod p) * (4 / 11 : ZMod p)^k /
            (k : ZMod p)) = ((1 + 4 / 11 : ZMod p)^m - 1) / (m : ZMod p) := by
        rw [←Finset.sum_Ico_consecutive _ (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ N),
          hc, htail, add_zero]
      have hrow : (∑ k ∈ Finset.Ico 1 N,
          (4 / 11 : ZMod p)^k / (k : ZMod p) * (infinityBinomialRow m k : ZMod p) *
            (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m)) =
          (∑ k ∈ Finset.Ico 1 N,
            (Nat.choose (m - 1) (k - 1) : ZMod p) * (4 / 11 : ZMod p)^k /
              (k : ZMod p)) * (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 : k ≠ 0 := by have hh := Finset.mem_Ico.mp hk; omega
        rw [infinityBinomialRow, if_neg hm0, if_neg hk0]
        ring
      rw [hrow, hsum]
      have hratio : (1 + 4 / 11 : ZMod p) * (1 / 5) = 3 / 11 := by
        field_simp [h5, h11]
        ring
      have hpowers : ((1 + 4 / 11 : ZMod p)^m - 1) * (1 / 5 : ZMod p)^m =
          (3 / 11 : ZMod p)^m - (1 / 5 : ZMod p)^m := by
        rw [sub_mul, ←mul_pow, hratio, one_mul]
      dsimp only [f]
      have hh := congrArg (fun z : ZMod p => z / (m : ZMod p) * (1 - (4 : ZMod p)^m)) hpowers
      linear_combination hh
  have hraw : (∑ k ∈ Finset.Ico 1 N, (4 / 11 : ZMod p)^k / (k : ZMod p) *
      ∑ m ∈ Finset.range N, (infinityBinomialRow m k : ZMod p) *
        (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m)) = ∑ m ∈ Finset.range N, f m := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    calc
      _ = ∑ k ∈ Finset.Ico 1 N,
          (4 / 11 : ZMod p)^k / (k : ZMod p) * (infinityBinomialRow m k : ZMod p) *
            (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = f m := hinner m hm
  have hzero : f 0 = 0 := by simp [f]
  have htop : f N = 0 := by simp only [f, h4N, sub_self, mul_zero]
  have hshift : (∑ m ∈ Finset.range N, f m) = ∑ m ∈ Finset.range N, f (m + 1) := by
    have h1 := Finset.sum_range_succ f N
    have h2 := Finset.sum_range_succ' f N
    rw [htop, add_zero] at h1
    rw [hzero, add_zero] at h2
    exact h1.symm.trans h2
  rw [hraw, hshift]
  have hc := reciprocal_log_contraction N h4N
  simpa only [f, h4N, div_one] using hc

theorem reciprocalResidueDigitIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (reciprocalResidueDigitIntegral p) = (11 / 5 : ZMod p) *
      (-(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        halfLog ((p - 1) / 2) (3 / 11 : ZMod p) -
        halfLog ((p - 1) / 2) (12 / 11 : ZMod p) +
        halfLog ((p - 1) / 2) (4 / 5 : ZMod p) -
        halfLog ((p - 1) / 2) (1 / 5 : ZMod p)) := by
  let N := (p - 1) / 2
  let q : ZMod p := (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)
  let S (k : ℕ) : ZMod p := ∑ m ∈ Finset.range N,
    (infinityBinomialRow m k : ZMod p) * (1 / 5 : ZMod p)^m * (1 - (4 : ZMod p)^m)
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hpow : ((2 : ZMod p)⁻¹)^(p - 1) = 1 := by
    apply mul_right_cancel₀ (inv_ne_zero h2)
    rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
      ZMod.pow_card, one_mul]
  have hN : N < p := by
    have hh := WPFiniteWSource.half_exponent p hp
    dsimp only [N]
    omega
  simp only [reciprocalResidueDigitIntegral, map_add, map_mul, map_pow, map_sum,
    map_intCast, map_neg, map_ofNat,
    smallIntegralInverse_field p 5 (by omega) (by omega),
    smallIntegralInverse_field p 2 (by omega) (by omega),
    Nat.cast_ofNat, ←one_div,
    infinityKernelIntegral_field p hp]
  simp only [mul_one_div]
  change (-11 / 5 : ZMod p)^p * q * (1 / 2 : ZMod p)^(p - 1) +
    (∑ k ∈ Finset.Ico 1 N,
      ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : ZMod p)) *
        (-11 / 5 : ZMod p)^(p - k) * (4 / 5 : ZMod p)^k * S k) = _
  rw [ZMod.pow_card, one_div, hpow, mul_one]
  have hsum : (∑ k ∈ Finset.Ico 1 N,
      ((((Nat.choose p k : ℤ) / (p : ℤ) : ℤ) : ZMod p)) *
        (-11 / 5 : ZMod p)^(p - k) * (4 / 5 : ZMod p)^k * S k) =
      (11 / 5 : ZMod p) * (∑ k ∈ Finset.Ico 1 N,
        (4 / 11 : ZMod p)^k / (k : ZMod p) * S k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k ∈ Finset.Ico 1 p := by
      have hh := Finset.mem_Ico.mp hk
      exact Finset.mem_Ico.mpr ⟨hh.1, hh.2.trans hN⟩
    rw [divided_binomial_pair_field p hp k hkp]
    ring
  rw [hsum]
  have hc := infinity_intermediate_field_contraction p hp
  change (∑ k ∈ Finset.Ico 1 N, (4 / 11 : ZMod p)^k / (k : ZMod p) * S k) = _ at hc
  rw [hc]
  dsimp only [q]
  ring

noncomputable def logCFirstDigit (p : ℕ) [Fact p.Prime] : ZMod p :=
  (3 / 5 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
    (11 / 10 : ZMod p) * (halfLog ((p - 1) / 2) (3 / 11 : ZMod p) -
      halfLog ((p - 1) / 2) (12 / 11 : ZMod p) +
      halfLog ((p - 1) / 2) (4 / 5 : ZMod p) -
      halfLog ((p - 1) / 2) (1 / 5 : ZMod p))

/-- SB102d's complete first coefficient digit, with both prime classes unrestricted. -/
theorem logCDigitIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (logCDigitIntegral p) = logCFirstDigit p := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h10 : (10 : ZMod p) ≠ 0 := small_cast_ne_zero p 10 (by omega) (by omega)
  have hpow : ((2 : ZMod p)⁻¹)^(p - 1) = 1 := by
    apply mul_right_cancel₀ (inv_ne_zero h2)
    rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
      ZMod.pow_card, one_mul]
  simp only [logCDigitIntegral, map_sub, map_add, map_mul, map_neg, map_intCast,
    map_pow, smallIntegralInverse_field p 2 (by omega) (by omega), Nat.cast_ofNat,
    hpow, mul_one,
    reciprocalResidueDigitIntegral_field p hp, logCFirstDigit]
  field_simp [h2, h5, h10]
  ring

/-- The same first digit reaches every characteristic-p field through the canonical map. -/
theorem logCDigitIntegral_base_change {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (logCDigitIntegral p)) =
      (3 / 5 : K) * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        (11 / 10 : K) * (halfLog ((p - 1) / 2) (3 / 11 : K) -
          halfLog ((p - 1) / 2) (12 / 11 : K) +
          halfLog ((p - 1) / 2) (4 / 5 : K) -
          halfLog ((p - 1) / 2) (1 / 5 : K)) := by
  rw [logCDigitIntegral_field p hp]
  simp only [logCFirstDigit, halfLog, map_sub, map_add, map_mul,
    map_div₀, map_ofNat, map_one, map_intCast, map_sum, map_pow, map_natCast]

end WPFieldAssembly.ActualLogCCarry
