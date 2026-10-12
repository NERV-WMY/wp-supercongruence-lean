import WPFieldAssembly.NativeSecondBridge
import WPFieldAssembly.NativeShiftedChi
import WPFieldAssembly.NativePrecisionTwo
import WPFieldAssembly.NativeTerminal
import WPActualRankTwoComparison
import WPActualRankTwoProper

open scoped Polynomial BigOperators
open Polynomial WPPIntegralReduction WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualNativeSecondTaylor
  WPActualRankTwoParameter WPActualRankTwoDividedDifference
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField
  WPActualRankTwoResidueSource WPActualRankTwoComparison WPActualRankTwoProper
  WPHasseIntegralTransport
  WPFieldAssembly.TerminatingSquare WPFieldAssembly.NativeDiscriminant
  WPFieldAssembly.NativePrecision WPFieldAssembly.NativePrecisionTwo
  WPFieldAssembly.NativeSecondGreen WPFieldAssembly.NativeSecondBridge
  WPFieldAssembly.NativeTerminatingNodes WPFieldAssembly.NativeShiftedChi

namespace WPFieldAssembly.NativeFullGreen

set_option maxHeartbeats 1600000

variable {K : Type*} [CommRing K]

private def TopBound (P : K[X]) (n : ℕ) (a : K) : Prop :=
  P.natDegree ≤ n ∧ P.coeff n = a

private theorem top_reindex {P : K[X]} {n m : ℕ} {a b : K}
    (h : TopBound P n a) (hn : n = m) (ha : a = b) : TopBound P m b := by
  rcases hn with rfl
  rcases ha with rfl
  exact h

private theorem top_mul {P Q : K[X]} {n m : ℕ} {a b : K}
    (hP : TopBound P n a) (hQ : TopBound Q m b) : TopBound (P * Q) (n + m) (a * b) := by
  refine ⟨natDegree_mul_le_of_le hP.1 hQ.1, ?_⟩
  rw [coeff_mul_add_eq_of_natDegree_le hP.1 hQ.1, hP.2, hQ.2]

private theorem top_sq {P : K[X]} {n : ℕ} {a : K}
    (hP : TopBound P n a) : TopBound (P ^ 2) (2 * n) (a ^ 2) := by
  simpa only [pow_two, two_mul] using top_mul hP hP

private theorem top_C_mul (c : K) {P : K[X]} {n : ℕ} {a : K}
    (hP : TopBound P n a) : TopBound (C c * P) n (c * a) := by
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add] using natDegree_mul_le_of_le
      (show (C c : K[X]).natDegree ≤ 0 by simp) hP.1
  · rw [coeff_C_mul, hP.2]

private theorem top_add {P Q : K[X]} {n : ℕ} {a b : K}
    (hP : TopBound P n a) (hQ : TopBound Q n b) : TopBound (P + Q) n (a + b) := by
  refine ⟨?_, ?_⟩
  · simpa only [max_self] using natDegree_add_le_of_le hP.1 hQ.1
  · rw [coeff_add, hP.2, hQ.2]

private theorem top_sub {P Q : K[X]} {n : ℕ} {a b : K}
    (hP : TopBound P n a) (hQ : TopBound Q n b) : TopBound (P - Q) n (a - b) := by
  refine ⟨?_, ?_⟩
  · simpa only [max_self] using natDegree_sub_le_of_le hP.1 hQ.1
  · rw [coeff_sub, hP.2, hQ.2]

private theorem top_derivative {P : K[X]} {n : ℕ} {a : K}
    (hn : 1 ≤ n) (hP : TopBound P n a) : TopBound P.derivative (n - 1) ((n : K) * a) := by
  refine ⟨?_, ?_⟩
  · have hd := natDegree_derivative_le P
    have hp := hP.1
    omega
  · rw [coeff_derivative, show n - 1 + 1 = n by omega, hP.2]
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring

private theorem top_X : TopBound (X : K[X]) 1 (1 : K) :=
  ⟨natDegree_X_le, by simp⟩

private theorem top_quadratic : TopBound (1 - X ^ 2 : K[X]) 2 (-1 : K) := by
  refine ⟨?_, ?_⟩
  · have hx : (X ^ 2 : K[X]).natDegree ≤ 2 := by
      simpa using natDegree_pow_le_of_le 2 (natDegree_X_le (R := K))
    exact (natDegree_sub_le_of_le (show (1 : K[X]).natDegree ≤ 0 by simp) hx).trans (by omega)
  · simp only [coeff_sub, coeff_one, coeff_X_pow]
    norm_num

private theorem field_prime_zero (p : ℕ) : (p : (ZMod p)[X]) = 0 := by
  change C (p : ZMod p) = 0
  rw [ZMod.natCast_self, C_0]

private theorem integral_sub_value (p : ℕ) [Fact p.Prime]
    (a b : integralRationals p) : (a - b).val = a.val - b.val := rfl

theorem quadraticGreen_degree_top (Y Q : K[X]) (d m : ℕ)
    (hd : 2 ≤ d) (hm : 2 ≤ m) (hY : Y.natDegree ≤ d) (hQ : Q.natDegree ≤ m) :
    (quadraticGreen Y Q).natDegree ≤ 2 * d + m + 2 ∧
      (quadraticGreen Y Q).coeff (2 * d + m + 2) =
        ((m : K) + 1) * ((m : K) - 2 * (d : K)) * Y.coeff d ^ 2 * Q.coeff m := by
  let lcY : K := Y.coeff d
  let lcQ : K := Q.coeff m
  let q : K[X] := 1 - X ^ 2
  let A : K[X] := q ^ 2 * Y ^ 2
  let B : K[X] := C (-2 : K) * (q * X * Y ^ 2) -
    C (2 : K) * (q ^ 2 * Y * Y.derivative)
  let Cg : K[X] := C (-2 : K) * (q ^ 2 * Y * Y.derivative.derivative) +
    C (2 : K) * (q ^ 2 * Y.derivative ^ 2) + C (4 : K) * (X * q * Y * Y.derivative)
  let N : ℕ := 2 * d + m + 2
  have hy : TopBound Y d lcY := ⟨hY, rfl⟩
  have hr : TopBound Q m lcQ := ⟨hQ, rfl⟩
  have hq : TopBound q 2 (-1 : K) := top_quadratic
  have hq2 : TopBound (q ^ 2) 4 (1 : K) := top_reindex (top_sq hq) (by norm_num) (by ring)
  have hy2 : TopBound (Y ^ 2) (2 * d) (lcY ^ 2) := top_sq hy
  have hdy : TopBound Y.derivative (d - 1) ((d : K) * lcY) := top_derivative (by omega) hy
  have hddy : TopBound Y.derivative.derivative (d - 2) ((d : K) * ((d : K) - 1) * lcY) :=
    top_reindex (top_derivative (by omega : 1 ≤ d - 1) hdy) (by omega)
      (by rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]; ring)
  have hdr : TopBound Q.derivative (m - 1) ((m : K) * lcQ) := top_derivative (by omega) hr
  have hddr : TopBound Q.derivative.derivative (m - 2) ((m : K) * ((m : K) - 1) * lcQ) :=
    top_reindex (top_derivative (by omega : 1 ≤ m - 1) hdr) (by omega)
      (by rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring)
  have hA : TopBound A (2 * d + 4) (lcY ^ 2) :=
    top_reindex (top_mul hq2 hy2) (by omega) (by ring)
  have hb1 : TopBound (C (-2 : K) * (q * X * Y ^ 2)) (2 * d + 3) (2 * lcY ^ 2) :=
    top_reindex (top_C_mul (-2) (top_mul (top_mul hq top_X) hy2)) (by omega) (by ring)
  have hb2 : TopBound (C (2 : K) * (q ^ 2 * Y * Y.derivative)) (2 * d + 3) (2 * (d : K) * lcY ^ 2) :=
    top_reindex (top_C_mul 2 (top_mul (top_mul hq2 hy) hdy)) (by omega) (by ring)
  have hB : TopBound B (2 * d + 3) ((2 - 2 * (d : K)) * lcY ^ 2) :=
    top_reindex (top_sub hb1 hb2) rfl (by ring)
  have hc1 : TopBound (C (-2 : K) * (q ^ 2 * Y * Y.derivative.derivative))
      (2 * d + 2) (-2 * (d : K) * ((d : K) - 1) * lcY ^ 2) :=
    top_reindex (top_C_mul (-2) (top_mul (top_mul hq2 hy) hddy)) (by omega) (by ring)
  have hc2 : TopBound (C (2 : K) * (q ^ 2 * Y.derivative ^ 2)) (2 * d + 2) (2 * (d : K) ^ 2 * lcY ^ 2) :=
    top_reindex (top_C_mul 2 (top_mul hq2 (top_sq hdy))) (by omega) (by ring)
  have hc3 : TopBound (C (4 : K) * (X * q * Y * Y.derivative)) (2 * d + 2) (-4 * (d : K) * lcY ^ 2) :=
    top_reindex (top_C_mul 4 (top_mul (top_mul (top_mul top_X hq) hy) hdy)) (by omega) (by ring)
  have hC : TopBound Cg (2 * d + 2) (-2 * (d : K) * lcY ^ 2) :=
    top_reindex (top_add (top_add hc1 hc2) hc3) rfl (by ring)
  have htA : TopBound (A * Q.derivative.derivative) N (lcY ^ 2 * ((m : K) * ((m : K) - 1) * lcQ)) :=
    top_reindex (top_mul hA hddr) (by dsimp [N]; omega) rfl
  have htB : TopBound (B * Q.derivative) N ((2 - 2 * (d : K)) * lcY ^ 2 * ((m : K) * lcQ)) :=
    top_reindex (top_mul hB hdr) (by dsimp [N]; omega) rfl
  have htC : TopBound (Cg * Q) N (-2 * (d : K) * lcY ^ 2 * lcQ) :=
    top_reindex (top_mul hC hr) (by dsimp [N]; omega) rfl
  have he : quadraticGreen Y Q = A * Q.derivative.derivative + B * Q.derivative + Cg * Q := by
    dsimp [A, B, Cg, q, quadraticGreen]
    simp only [_root_.map_neg, _root_.map_ofNat]
    ring
  have hg : TopBound (quadraticGreen Y Q) N
      (((m : K) + 1) * ((m : K) - 2 * (d : K)) * lcY ^ 2 * lcQ) := by
    rw [he]
    exact top_reindex (top_add (top_add htA htB) htC) rfl (by ring)
  exact ⟨hg.1, hg.2⟩

def fullCutoff (p : ℕ) : ℕ := p - 1 - p / 6
noncomputable def sixth (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 6, WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
noncomputable def twelfth (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 12, WPFiniteConductorPolynomial.small_inverse_integral p 12 (by norm_num) (by omega)⟩
noncomputable def fullScale (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  5 * sixth p hp * twelfth p hp

theorem fullScale_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullScale p hp).val = (5 / 72 : ℚ) := by
  change (5 : ℚ) * (1 / 6) * (1 / 12) = 5 / 72
  norm_num

theorem fullScale_identity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (72 : integralRationals p) * fullScale p hp = 5 := by
  apply Subtype.ext
  change (72 : ℚ) * (fullScale p hp).val = 5
  rw [fullScale_value]
  norm_num

noncomputable def fullNativeJacobi (p : ℕ) : ℚ[X] :=
  (WPReview.nativePolynomial (fullCutoff p + 1)).comp (1 - X ^ 2)
noncomputable def fullWeightedDiscriminant (p : ℕ) : ℚ[X] :=
  (1 - X ^ 2) * jacobiDiscriminant 0 (fullNativeJacobi p)
noncomputable def fullC2 (p : ℕ) : ℚ[X] :=
  (nativeSecondJetAt p (fullCutoff p)).comp (1 - X ^ 2)
noncomputable def fullQ (p : ℕ) : ℚ[X] := 2 * fullC2 p - 2 * rankDividedJacobi p ^ 2

theorem fullNativeSecondJet_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((nativeSecondJetAt p (fullCutoff p)).coeff n) := by
  rw [nativeSecondJetAt, coefficientPolynomial_coeff]
  split_ifs with hn
  · exact actual_parameterSecondJet_integral p n (by omega)
      (by dsimp [fullCutoff] at hn; omega)
  · simp

noncomputable def fullNativeC2Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := integralPolynomialLift p
      (nativeSecondJetAt p (fullCutoff p)) (fullNativeSecondJet_integral p hp)
noncomputable def fullC2Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := (fullNativeC2Integral p hp).comp (1 - X ^ 2)
noncomputable def fullQIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  2 * fullC2Integral p hp - 2 * rankDividedIntegralJacobi p (by omega) ^ 2
noncomputable def fullQField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (fullQIntegral p hp).map (residueHom p)

theorem fullNativeC2Integral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullNativeC2Integral p hp).map (integralRationals p).subtype =
      nativeSecondJetAt p (fullCutoff p) := integralPolynomialLift_rational _ _ _

theorem fullC2Integral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullC2Integral p hp).map (integralRationals p).subtype = fullC2 p := by
  rw [fullC2Integral, Polynomial.map_comp, fullNativeC2Integral_value]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

theorem fullQIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullQIntegral p hp).map (integralRationals p).subtype = fullQ p := by
  simp only [fullQIntegral, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
    Polynomial.map_pow, fullC2Integral_value, rankDividedIntegralJacobi_value]
  rfl

theorem fullC2Integral_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullC2Integral p hp).natDegree ≤ 2 * fullCutoff p := by
  have hc : (fullNativeC2Integral p hp).natDegree ≤ fullCutoff p := by
    rw [fullNativeC2Integral, integralPolynomialLift_degree]
    exact coefficientPolynomial_degree _ _
  have hq : (1 - X ^ 2 : (integralRationals p)[X]).natDegree ≤ 2 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hc hq).trans_eq (Nat.mul_comm _ _))

theorem fullQField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullQField p hp).natDegree ≤ 2 * fullCutoff p := by
  apply natDegree_map_le.trans
  have hC := fullC2Integral_degree p hp
  have hR := rankDividedIntegralJacobi_degree p (by omega)
  have hR2 : (rankDividedIntegralJacobi p (by omega) ^ 2).natDegree ≤ 2 * fullCutoff p :=
    by simpa only [fullCutoff] using natDegree_pow_le_of_le 2 hR
  have h1 : (2 * fullC2Integral p hp).natDegree ≤ 2 * fullCutoff p :=
    (natDegree_C_mul_le _ _).trans hC
  have h2 : (2 * rankDividedIntegralJacobi p (by omega) ^ 2).natDegree ≤ 2 * fullCutoff p :=
    (natDegree_C_mul_le _ _).trans hR2
  simpa only [fullQIntegral, max_self] using natDegree_sub_le_of_le h1 h2

theorem actual_upper_middle_numerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : (p - 1) / 2 < n) :
    (clearedNumerator ℚ n).eval (-(p : ℚ) / 2) = 0 := by
  rw [clearedNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  have hhalf := congrArg (fun k : ℕ => (k : ℚ)) (WPFiniteWSource.half_exponent p hp)
  push_cast at hhalf
  have hz : 2 * (((p - 1) / 2 : ℕ) : ℚ) + 1 + 2 * (-(p : ℚ) / 2) = 0 := by linarith
  simp only [eval_mul, eval_add, eval_C, eval_ofNat, eval_X]
  rw [hz, mul_zero, zero_mul]

theorem actual_upper_double_zero_second_jet (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (hupper : (p - 1) / 2 < n) :
    ∃ v : integralRationals p,
      parameterJet n (-(p : ℚ) / 6) - (p : ℚ) / 3 * parameterSecondJet p n =
        (p : ℚ) ^ 2 * v.val := by
  let R := integralRationals p
  let A := clearedNumerator R n
  let D := clearedDenominator R n
  let a := integralNode p (by omega)
  let b := rankNode p (by omega) 3
  have haunit := denominator_node_unit p n (by omega) hn
  have hbunit := nativeDenominator_node_unit p n (by omega) hn 3
  let ua : R := ⟨(D.eval a).val⁻¹, haunit.2⟩
  let ub : R := ⟨(D.eval b).val⁻¹, hbunit.2⟩
  have ha : D.eval a * ua = 1 := by
    apply Subtype.ext
    change (D.eval a).val * (D.eval a).val⁻¹ = 1
    exact mul_inv_cancel₀ haunit.1
  have hb : D.eval b * ub = 1 := by
    apply Subtype.ext
    change (D.eval b).val * (D.eval b).val⁻¹ = 1
    exact mul_inv_cancel₀ hbunit.1
  have ha0 : A.eval a = 0 := by
    apply Subtype.ext
    change (A.eval a).val = 0
    rw [evaluate_subtype, clearedNumerator_map, integralNode_value]
    exact terminating_numerator_zero p n (by omega) (by omega)
  have hb0 : A.eval b = 0 := by
    apply Subtype.ext
    change (A.eval b).val = 0
    rw [evaluate_subtype, clearedNumerator_map, rankNode_value]
    simp only [Nat.cast_ofNat]
    rw [show -(3 : ℚ) * (p : ℚ) / 6 = -(p : ℚ) / 2 by ring]
    exact actual_upper_middle_numerator_zero p n hp hupper
  obtain ⟨u, hu⟩ := integral_shifted_second_expansion A D a b ua ub ha hb
  have hJ0 : firstJetOver A D a ua =
      (A.derivative.eval a * D.eval a - A.eval a * D.derivative.eval a) * ua ^ 2 := by
    unfold firstJetOver
    linear_combination -(A.derivative.eval a * ua) * ha
  have hJ : (firstJetOver A D a ua).val = parameterJet n (-(p : ℚ) / 6) := by
    rw [hJ0]
    change (integralParameterJet p n (by omega) hn).val = _
    exact integralParameterJet_value p n (by omega) hn
  have hK : (secondJetOver A D a ua).val = parameterSecondJet p n := by
    change (integralParameterSecondJet p n (by omega) hn).val = _
    exact integralParameterSecondJet_value p n (by omega) hn
  have hdelta : b.val - a.val = -(p : ℚ) / 3 := by
    simp only [b, a, rankNode_value, integralNode_value, Nat.cast_ofNat]
    ring
  simp only [ha0, hb0, zero_mul, sub_zero, zero_sub] at hu
  have hv := congrArg R.subtype hu
  simp only [_root_.map_sub, _root_.map_neg, _root_.map_mul, _root_.map_pow,
    Subring.subtype_apply] at hv
  change -((b.val - a.val) * (firstJetOver A D a ua).val) -
      (b.val - a.val) ^ 2 * (secondJetOver A D a ua).val = (b.val - a.val) ^ 3 * u.val at hv
  rw [hJ, hK, hdelta] at hv
  let ninth : R := ⟨1 / 9,
    WPFiniteConductorPolynomial.small_inverse_integral p 9 (by norm_num) (by omega)⟩
  let v : R := -u * ninth
  refine ⟨v, ?_⟩
  have hvval : v.val = -u.val / 9 := by
    change -u.val * (1 / 9 : ℚ) = -u.val / 9
    ring
  rw [hvval]
  apply mul_left_cancel₀ (by positivity : (p : ℚ) / 3 ≠ 0)
  linear_combination hv

theorem actual_upper_native_divided_two_witness (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (hupper : (p - 1) / 2 < n) :
    ∃ b : integralRationals p, b.val = WPReview.nativeCoefficient n / (p : ℚ) ^ 2 ∧
      residueHom p b = residueHom p (twelfth p hp) *
        residueHom p (integralParameterSecondJet p n (by omega) hn) := by
  obtain ⟨v, hv⟩ := actual_upper_double_zero_second_jet p n hp hn hupper
  let K := integralParameterSecondJet p n (by omega) hn
  let E : integralRationals p :=
    ⟨nativeCubicError p n, actual_nativeCubicError_integral p n (by omega) hn⟩
  let b : integralRationals p :=
    K * twelfth p hp + (p : integralRationals p) * (v * sixth p hp + E)
  have hK : K.val = parameterSecondJet p n := integralParameterSecondJet_value p n (by omega) hn
  have ha : parameterCoefficient n (-(p : ℚ) / 6) = 0 := by
    rw [parameterCoefficient, terminating_numerator_zero p n (by omega) (by omega), zero_div]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hTaylor : WPReview.nativeCoefficient n - parameterCoefficient n (-(p : ℚ) / 6) -
      (p : ℚ) / 6 * parameterJet n (-(p : ℚ) / 6) -
      (p : ℚ) ^ 2 / 36 * parameterSecondJet p n = (p : ℚ) ^ 3 * E.val := by
    change _ = (p : ℚ) ^ 3 * nativeCubicError p n
    unfold nativeCubicError
    field_simp [hpq]
  refine ⟨b, ?_, ?_⟩
  · change K.val * (1 / 12 : ℚ) + (p : ℚ) * (v.val * (1 / 6 : ℚ) + E.val) =
      WPReview.nativeCoefficient n / (p : ℚ) ^ 2
    rw [hK]
    rw [ha] at hTaylor
    apply (eq_div_iff (pow_ne_zero 2 hpq)).2
    linear_combination -hTaylor - ((p : ℚ) / 6) * hv
  · simp only [b, _root_.map_add, _root_.map_mul, _root_.map_natCast, ZMod.natCast_self, zero_mul, add_zero]
    ring

noncomputable def fullCubicIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := integralPolynomialLift p
      (nativeCubicErrorPolynomial p (fullCutoff p))
      (nativeCubicErrorPolynomial_integral p (fullCutoff p) (by omega) (by dsimp [fullCutoff]; omega))

theorem fullCubicIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullCubicIntegral p hp).map (integralRationals p).subtype =
      nativeCubicErrorPolynomial p (fullCutoff p) := integralPolynomialLift_rational _ _ _

noncomputable def balancedIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := rankIntegralJacobi p (by omega) 1 +
      C ((p : integralRationals p) * sixth p hp) * rankDividedIntegralJacobi p (by omega)

theorem balancedIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (balancedIntegral p hp).map (integralRationals p).subtype = balancedRank p := by
  simp only [balancedIntegral, balancedRank, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, rankIntegralJacobi_value, rankDividedIntegralJacobi_value]
  simp only [Subring.subtype_apply]
  congr 3
  change (p : ℚ) * (1 / 6 : ℚ) = (p : ℚ) / 6
  ring

theorem balancedIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (balancedIntegral p hp).map (residueHom p) = actualLegendreJacobi p := by
  simp only [balancedIntegral, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, rankIntegralJacobi_field, _root_.map_mul, _root_.map_natCast,
    Polynomial.map_natCast, field_prime_zero, zero_mul, add_zero]

theorem actual_full_balanced_taylor_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ T : (integralRationals p)[X], fullNativeJacobi p = balancedRank p ^ 2 +
      C (5 * (p : ℚ) ^ 2 / 72) * fullQ p + C ((p : ℚ) ^ 3) * T.map (integralRationals p).subtype := by
  obtain ⟨E, hE⟩ := actual_full_native_second_bridge p hp
  let T : (integralRationals p)[X] :=
    C (sixth p hp) * E + (fullCubicIntegral p hp).comp (1 - X ^ 2)
  have hT : T.map (integralRationals p).subtype = C (1 / 6 : ℚ) * E.map (integralRationals p).subtype +
      (nativeCubicErrorPolynomial p (fullCutoff p)).comp (1 - X ^ 2) := by
    simp only [T, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_comp, fullCubicIntegral_value, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    rfl
  have hF := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2))
    (actual_native_polynomial_secondTaylor p (fullCutoff p))
  have hnode : nativeTermAt p (fullCutoff p) = nativeNodeAt p 1 := by
    simp only [nativeTermAt, nativeNodeAt, fullCutoff, Nat.cast_one, neg_one_mul]
  rw [hnode] at hF
  simp only [sub_comp, mul_comp, C_comp] at hF
  rw [actual_terminating_native_node_square p 1 hp (Or.inl rfl)] at hF
  refine ⟨T, ?_⟩
  rw [hT]
  dsimp only [fullNativeJacobi, fullQ, fullC2, balancedRank, fullCutoff] at hF ⊢
  have hthird : C ((3 : ℚ)⁻¹) = 2 * C ((6 : ℚ)⁻¹) := by
    change C ((3 : ℚ)⁻¹) = C (2 : ℚ) * C ((6 : ℚ)⁻¹)
    rw [← C_mul]
    norm_num
  have h36 : C ((36 : ℚ)⁻¹) = C ((6 : ℚ)⁻¹) ^ 2 := by
    rw [← C_pow]
    norm_num
  have h72 : 2 * C ((72 : ℚ)⁻¹) = C ((36 : ℚ)⁻¹) := by
    change C (2 : ℚ) * C ((72 : ℚ)⁻¹) = C ((36 : ℚ)⁻¹)
    rw [← C_mul]
    norm_num
  simp only [div_eq_mul_inv, _root_.map_mul, _root_.map_pow, _root_.map_ofNat,
    _root_.map_one, hthird, h36] at hF hE ⊢
  have h72' : 2 * C ((72 : ℚ)⁻¹) = C ((6 : ℚ)⁻¹) ^ 2 := h72.trans h36
  linear_combination hF + C (p : ℚ) * C ((6 : ℚ)⁻¹) * hE +
    5 * C (p : ℚ) ^ 2 * (rankDividedJacobi p ^ 2 -
      (nativeSecondJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2)) * h72'

noncomputable def fullTaylorRemainder (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := Classical.choose (actual_full_balanced_taylor_integral p hp)

theorem fullTaylorRemainder_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fullNativeJacobi p = balancedRank p ^ 2 + C (5 * (p : ℚ) ^ 2 / 72) * fullQ p +
      C ((p : ℚ) ^ 3) * (fullTaylorRemainder p hp).map (integralRationals p).subtype :=
  Classical.choose_spec (actual_full_balanced_taylor_integral p hp)

noncomputable def fullCorrectionIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  C (fullScale p hp) * fullQIntegral p hp + C (p : integralRationals p) * fullTaylorRemainder p hp
noncomputable def balancedForcingIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := -5 * rankIntegralJacobi p (by omega) 1 -
      10 * X * (rankDividedIntegralJacobi p (by omega)).derivative -
      5 * rankDividedIntegralJacobi p (by omega) + C (25 * (p : integralRationals p) * sixth p hp) *
        rankDividedIntegralJacobi p (by omega)

theorem jacobiPolar_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F G : R[X]) :
    (jacobiPolar F G).map f = jacobiPolar (F.map f) (G.map f) := by
  simp only [jacobiPolar, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat, ← derivative_map]

theorem jacobiPolar_C_right {K : Type*} [CommRing K] (F G : K[X]) (s : K) :
    jacobiPolar F (C s * G) = C s * jacobiPolar F G := by
  simp [jacobiPolar]
  ring

theorem jacobiDiscriminant_add_scaled {K : Type*} [CommRing K] (F H : K[X]) (r : K) :
    jacobiDiscriminant 0 (F + C r * H) = jacobiDiscriminant 0 F +
      2 * C r * jacobiPolar F H + C (r ^ 2) * jacobiDiscriminant 0 H := by
  simp [jacobiDiscriminant, jacobiPolar, derivative_add, _root_.map_ofNat]
  ring

noncomputable def fullDividedDiscriminantIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := (1 - X ^ 2) * balancedIntegral p hp ^ 3 * balancedForcingIntegral p hp +
      2 * (1 - X ^ 2) * jacobiPolar (balancedIntegral p hp ^ 2) (fullCorrectionIntegral p hp) +
      C ((p : integralRationals p) ^ 2) * (1 - X ^ 2) * jacobiDiscriminant 0 (fullCorrectionIntegral p hp)

theorem actual_full_discriminant_divided_two_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullDividedDiscriminantIntegral p hp).map (integralRationals p).subtype =
      C (1 / (p : ℚ) ^ 2) * fullWeightedDiscriminant p := by
  let H := (fullCorrectionIntegral p hp).map (integralRationals p).subtype
  let S : ℚ[X] := -5 * rankJacobiNode p 1 - 10 * X * (rankDividedJacobi p).derivative -
    5 * rankDividedJacobi p + C (25 * (p : ℚ) / 6) * rankDividedJacobi p
  have hS : (balancedForcingIntegral p hp).map (integralRationals p).subtype = S := by
    simp only [balancedForcingIntegral, S, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_ofNat, Polynomial.map_neg,
      Polynomial.map_X, ← derivative_map, rankIntegralJacobi_value, rankDividedIntegralJacobi_value]
    simp only [Subring.subtype_apply]
    congr 3
    change 25 * (p : ℚ) * (1 / 6 : ℚ) = 25 * (p : ℚ) / 6
    ring
  have hH : H = C (5 / 72 : ℚ) * fullQ p +
      C (p : ℚ) * (fullTaylorRemainder p hp).map (integralRationals p).subtype := by
    simp only [H, fullCorrectionIntegral, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, fullQIntegral_value, Subring.subtype_apply, fullScale_value]
    rfl
  have hF : fullNativeJacobi p = balancedRank p ^ 2 + C ((p : ℚ) ^ 2) * H := by
    rw [hH]
    have ht := fullTaylorRemainder_value p hp
    rw [show 5 * (p : ℚ) ^ 2 / 72 = (p : ℚ) ^ 2 * (5 / 72) by ring] at ht
    simp only [_root_.map_mul, _root_.map_pow] at ht ⊢
    linear_combination ht
  have hM : (fullDividedDiscriminantIntegral p hp).map (integralRationals p).subtype =
      (1 - X ^ 2) * balancedRank p ^ 3 * S + 2 * (1 - X ^ 2) * jacobiPolar (balancedRank p ^ 2) H +
        C ((p : ℚ) ^ 2) * (1 - X ^ 2) * jacobiDiscriminant 0 H := by
    simp only [fullDividedDiscriminantIntegral, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, Polynomial.map_C, balancedIntegral_value, hS, jacobiPolar_map,
      jacobiDiscriminant_map]
    rfl
  have hD : fullWeightedDiscriminant p = C ((p : ℚ) ^ 2) *
      ((1 - X ^ 2) * balancedRank p ^ 3 * S + 2 * (1 - X ^ 2) * jacobiPolar (balancedRank p ^ 2) H +
        C ((p : ℚ) ^ 2) * (1 - X ^ 2) * jacobiDiscriminant 0 H) := by
    rw [fullWeightedDiscriminant, hF, jacobiDiscriminant_add_scaled]
    have hb := actual_balanced_square_discriminant_source p hp
    change (1 - X ^ 2) * jacobiDiscriminant 0 (balancedRank p ^ 2) =
      C ((p : ℚ) ^ 2) * (1 - X ^ 2) * balancedRank p ^ 3 * S at hb
    simp only [_root_.map_pow] at hb ⊢
    linear_combination hb
  rw [hM, hD, ← mul_assoc]
  have hc : C (1 / (p : ℚ) ^ 2) * C ((p : ℚ) ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    have hpq : (p : ℚ) ≠ 0 := by positivity
    field_simp [hpq]
    simp only [C_1]
  rw [hc, one_mul]

theorem rankJacobiClear_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (Y : R[X]) :
    (rankJacobiClear t Y).map f = rankJacobiClear (f t) (Y.map f) := by
  simp only [rankJacobiClear, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_ofNat, ← derivative_map, _root_.map_add, _root_.map_mul, _root_.map_ofNat, _root_.map_one]

theorem actual_rank_clear_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankJacobiClear 0 (actualLegendreJacobi p) = 0 := by
  have hi : rankJacobiClear (integralNode p (by omega)) (rankIntegralJacobi p (by omega) 1) = 0 := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [rankJacobiClear_map, rankIntegralJacobi_value, Subring.subtype_apply,
      integralNode_value, Polynomial.map_zero]
    simpa only [Nat.cast_one, neg_one_mul] using actual_rankJacobi_ODE p 1 (by omega) (Or.inl rfl)
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simpa only [rankJacobiClear_map, integralNode_residue, rankIntegralJacobi_field,
    Polynomial.map_zero] using hf

theorem actual_full_discriminant_field_source_four (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    4 * (fullDividedDiscriminantIntegral p hp).map (residueHom p) =
      -20 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
        (actualLegendreJacobi p + 2 * X * (actualRankDividedField p (by omega)).derivative +
          actualRankDividedField p (by omega)) +
      5 * quadraticGreen (actualLegendreJacobi p) (fullQField p hp) := by
  let Y := actualLegendreJacobi p
  let R := actualRankDividedField p (by omega)
  let σ := residueHom p (fullScale p hp)
  let Q := fullQField p hp
  let M := (fullDividedDiscriminantIntegral p hp).map (residueHom p)
  have hH : (fullCorrectionIntegral p hp).map (residueHom p) = C σ * Q := by
    simp only [fullCorrectionIntegral, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      _root_.map_natCast, Polynomial.map_natCast, field_prime_zero, zero_mul, add_zero]
    rfl
  have hS : (balancedForcingIntegral p hp).map (residueHom p) =
      -5 * Y - 10 * X * R.derivative - 5 * R := by
    simp only [balancedForcingIntegral, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_neg, Polynomial.map_ofNat,
      Polynomial.map_X, ← derivative_map, rankIntegralJacobi_field, _root_.map_mul, _root_.map_natCast,
      Polynomial.map_natCast, field_prime_zero, mul_zero, zero_mul, add_zero]
    rfl
  have hM : M = -5 * (1 - X ^ 2) * Y ^ 3 * (Y + 2 * X * R.derivative + R) +
      2 * C σ * ((1 - X ^ 2) * jacobiPolar (Y ^ 2) Q) := by
    dsimp only [M, Y]
    simp only [fullDividedDiscriminantIntegral, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X,
      Polynomial.map_ofNat, balancedIntegral_field, hS, hH,
      jacobiPolar_map, jacobiDiscriminant_map, _root_.map_pow, _root_.map_natCast,
      Polynomial.map_natCast, field_prime_zero,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, jacobiPolar_C_right]
    dsimp only [Y]
    ring
  have hG : (1 - X ^ 2) * jacobiPolar (Y ^ 2) Q = 9 * quadraticGreen Y Q := by
    rw [quadraticGreen_polar, actual_rank_clear_zero p hp, mul_zero, add_zero]
  have hσ : (72 : ZMod p) * σ = 5 := by
    have h := congrArg (residueHom p) (fullScale_identity p hp)
    simpa only [_root_.map_mul, _root_.map_ofNat] using h
  have hσP := congrArg (C : ZMod p → (ZMod p)[X]) hσ
  simp only [_root_.map_mul, _root_.map_ofNat] at hσP
  change 4 * M = -20 * (1 - X ^ 2) * Y ^ 3 * (Y + 2 * X * R.derivative + R) + 5 * quadraticGreen Y Q
  linear_combination 4 * hM + 8 * C σ * hG + quadraticGreen Y Q * hσP

noncomputable def fullNativeIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := (nativeIntegral p (fullCutoff p) (by omega)
      (by dsimp [fullCutoff]; omega)).comp (1 - X ^ 2)

theorem fullNativeIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullNativeIntegral p hp).map (integralRationals p).subtype = fullNativeJacobi p := by
  rw [fullNativeIntegral, Polynomial.map_comp, nativeIntegral_map_rational]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

noncomputable def fullTerminalDividedThree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨WPReview.nativeCoefficient (fullCutoff p + 1) / (p : ℚ) ^ 3, by
    change 0 ≤ padicValRat p (WPReview.nativeCoefficient (fullCutoff p + 1) / (p : ℚ) ^ 3)
    rw [padicValRat.div (WPNativeMomentIntegrality.nativeCoefficient_ne_zero _)
      (pow_ne_zero 3 (by positivity : (p : ℚ) ≠ 0)), padicValRat.pow,
      padicValRat.self (Fact.out : p.Prime).one_lt,
      WPNativeMomentIntegrality.native_high_tail_valuation p (fullCutoff p + 1) (by omega)
        (by dsimp [fullCutoff]; omega) (by dsimp [fullCutoff]; omega)]
    norm_num⟩
noncomputable def fullTerminalEta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ((fullCutoff p + 1 : ℕ) : integralRationals p) ^ 3 * fullTerminalDividedThree p hp

theorem fullTerminalEta_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullTerminalEta p hp).val = WPReview.nativeEndpoint (fullCutoff p + 1) / (p : ℚ) ^ 3 := by
  rw [WPReview.nativeEndpoint_eq _ (by omega)]
  change (((fullCutoff p + 1 : ℕ) : ℚ) ^ 3 *
      (WPReview.nativeCoefficient (fullCutoff p + 1) / (p : ℚ) ^ 3)) =
    (((fullCutoff p + 1 : ℕ) : ℚ) ^ 3 * WPReview.nativeCoefficient (fullCutoff p + 1)) / (p : ℚ) ^ 3
  ring

theorem actual_full_native_square_source (p : ℕ) [Fact p.Prime] (_hp : 19 ≤ p) :
    jacobiSquare 0 (fullNativeJacobi p) =
      C (288 * WPReview.nativeEndpoint (fullCutoff p + 1)) * X * (1 - X ^ 2) ^ fullCutoff p := by
  rw [fullNativeJacobi, termRegular_jacobi_source, termRegular_zero,
    rational_native_regular_residual, mul_comp, C_comp, pow_comp, X_comp]
  simp only [_root_.map_mul, _root_.map_neg, _root_.map_ofNat]
  ring

theorem actual_full_weighted_discriminant_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullWeightedDiscriminant p).derivative =
      C (144 * WPReview.nativeEndpoint (fullCutoff p + 1)) *
        X * (1 - X ^ 2) ^ fullCutoff p * fullNativeJacobi p := by
  have he := jacobiDiscriminant_zero_source (fullNativeJacobi p)
  rw [actual_full_native_square_source p hp] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℚ[X]) ≠ 0)
  simp only [fullWeightedDiscriminant, _root_.map_mul, _root_.map_ofNat] at he ⊢
  linear_combination he

theorem actual_full_divided_discriminant_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullDividedDiscriminantIntegral p hp).derivative =
      C (144 * (p : integralRationals p) * fullTerminalEta p hp) *
        X * (1 - X ^ 2) ^ fullCutoff p * fullNativeIntegral p hp := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [← derivative_map, actual_full_discriminant_divided_two_value,
    derivative_C_mul, actual_full_weighted_discriminant_source p hp]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, fullNativeIntegral_value,
    Subring.subtype_apply]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hc : (1 / (p : ℚ) ^ 2) * (144 * WPReview.nativeEndpoint (fullCutoff p + 1)) =
      144 * (p : ℚ) * (fullTerminalEta p hp).val := by
    rw [fullTerminalEta_value]
    field_simp [hpq]
  have he := congrArg (C : ℚ → ℚ[X]) hc
  simp only [Subring.coe_mul, Subring.coe_natCast,
    show (144 : integralRationals p).val = (144 : ℚ) by rfl]
  simp only [_root_.map_mul, _root_.map_ofNat] at he ⊢
  linear_combination (X * (1 - X ^ 2) ^ fullCutoff p * fullNativeJacobi p) * he

theorem actual_full_divided_discriminant_derivative_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((fullDividedDiscriminantIntegral p hp).map (residueHom p)).derivative = 0 := by
  rw [derivative_map, actual_full_divided_discriminant_derivative]
  simp only [Polynomial.map_mul, Polynomial.map_C, _root_.map_mul, _root_.map_natCast,
    Polynomial.map_natCast, field_prime_zero, mul_zero, zero_mul]

theorem quadratic_comp_coeff_top (P : ℚ[X]) (e : ℕ) (hP : P.natDegree ≤ e) :
    (P.comp (1 - X ^ 2)).coeff (2 * e) = P.coeff e * (-1 : ℚ) ^ e := by
  by_cases he : P.natDegree = e
  · have hc := coeff_comp_degree_mul_degree (p := P) (q := (1 - X ^ 2 : ℚ[X]))
      (by rw [quadratic_degree]; norm_num)
    have hlead : P.leadingCoeff = P.coeff e := by rw [leadingCoeff, he]
    rw [he, quadratic_degree, hlead, quadratic_leading] at hc
    simpa only [Nat.mul_comm] using hc
  · have hs : P.natDegree < e := by omega
    have hd := natDegree_comp_le (p := P) (q := (1 - X ^ 2 : ℚ[X]))
    rw [quadratic_degree] at hd
    have hc : (P.comp (1 - X ^ 2)).natDegree < 2 * e := by omega
    rw [coeff_eq_zero_of_natDegree_lt hc, coeff_eq_zero_of_natDegree_lt hs]
    ring

theorem actual_fullQ_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullQField p hp).coeff (2 * fullCutoff p) =
      2 * (actualRankDividedField p (by omega)).coeff (fullCutoff p) ^ 2 := by
  let e := fullCutoff p
  obtain ⟨v, hv⟩ := actual_upper_double_zero_second_jet p e hp (by dsimp [e, fullCutoff]; omega)
    (by have hh := WPFiniteWSource.half_exponent p hp; dsimp [e, fullCutoff]; omega)
  obtain ⟨E, hE⟩ := actual_full_native_second_bridge p hp
  let w : integralRationals p := (-1) ^ e * v
  have hJ : ((nativeFirstJetAt p e).comp (1 - X ^ 2)).coeff (2 * e) =
      parameterJet e (-(p : ℚ) / 6) * (-1 : ℚ) ^ e := by
    unfold nativeFirstJetAt
    rw [quadratic_comp_coeff_top _ e (coefficientPolynomial_degree _ _)]
    rw [coefficientPolynomial_coeff, if_pos (by omega)]
  have hK : (fullC2 p).coeff (2 * e) = parameterSecondJet p e * (-1 : ℚ) ^ e := by
    change ((nativeSecondJetAt p e).comp (1 - X ^ 2)).coeff (2 * e) = _
    unfold nativeSecondJetAt
    rw [quadratic_comp_coeff_top _ e (coefficientPolynomial_degree _ _)]
    rw [coefficientPolynomial_coeff, if_pos (by omega)]
  have hupper : ((nativeFirstJetAt p e).comp (1 - X ^ 2)).coeff (2 * e) -
      (p : ℚ) / 3 * (fullC2 p).coeff (2 * e) = (p : ℚ) ^ 2 * w.val := by
    rw [hJ, hK]
    change _ = (p : ℚ) ^ 2 * ((-1 : ℚ) ^ e * v.val)
    linear_combination (-1 : ℚ) ^ e * hv
  have hlow : (2 * rankJacobiNode p 1 * rankDividedJacobi p).coeff (2 * e) = 0 := by
    have ha := actual_low_rankJacobi_degree p (by omega)
    have hR := rankDividedJacobi_degree p
    have h2a : (2 * rankJacobiNode p 1).natDegree ≤ p / 6 := (natDegree_C_mul_le _ _).trans ha
    have hd := natDegree_mul_le_of_le h2a hR
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [e, fullCutoff] at *
    omega
  have hbridge := congrArg (fun P : ℚ[X] => P.coeff (2 * e)) hE
  change ((nativeFirstJetAt p e).comp (1 - X ^ 2) -
      2 * rankJacobiNode p 1 * rankDividedJacobi p - C ((p : ℚ) / 3) * fullQ p).coeff (2 * e) =
      (C ((p : ℚ) ^ 2) * E.map (integralRationals p).subtype).coeff (2 * e) at hbridge
  rw [coeff_sub, coeff_sub, hlow, sub_zero, coeff_C_mul, coeff_C_mul, coeff_map] at hbridge
  simp only [Subring.subtype_apply] at hbridge
  have hi : (fullQIntegral p hp).coeff (2 * e) - (fullC2Integral p hp).coeff (2 * e) =
      (p : integralRationals p) * 3 * (w - E.coeff (2 * e)) := by
    apply Subtype.ext
    have hQv := congrArg (fun P : ℚ[X] => P.coeff (2 * e)) (fullQIntegral_value p hp)
    have hCv := congrArg (fun P : ℚ[X] => P.coeff (2 * e)) (fullC2Integral_value p hp)
    rw [coeff_map] at hQv hCv
    simp only [Subring.subtype_apply] at hQv hCv
    change ((fullQIntegral p hp).coeff (2 * e)).val - ((fullC2Integral p hp).coeff (2 * e)).val =
      (p : ℚ) * 3 * (w.val - (E.coeff (2 * e)).val)
    rw [hQv, hCv]
    apply mul_left_cancel₀ (by positivity : (p : ℚ) / 3 ≠ 0)
    linear_combination hupper - hbridge
  have hsame : (fullQField p hp).coeff (2 * e) =
      ((fullC2Integral p hp).map (residueHom p)).coeff (2 * e) := by
    have hf := congrArg (residueHom p) hi
    simp only [_root_.map_sub, _root_.map_mul, _root_.map_natCast, ZMod.natCast_self, zero_mul, _root_.map_ofNat] at hf
    rw [sub_eq_zero] at hf
    simpa only [fullQField, coeff_map] using hf
  have hR := actualRankDividedField_degree p (by omega)
  change (actualRankDividedField p (by omega)).natDegree ≤ e at hR
  have hR2 : (actualRankDividedField p (by omega) ^ 2).coeff (2 * e) =
      (actualRankDividedField p (by omega)).coeff e ^ 2 := by
    rw [pow_two, show 2 * e = e + e by omega, coeff_mul_add_eq_of_natDegree_le hR hR]
    ring
  have hdef : (fullQField p hp).coeff (2 * e) =
      2 * ((fullC2Integral p hp).map (residueHom p)).coeff (2 * e) -
        2 * (actualRankDividedField p (by omega)).coeff e ^ 2 := by
    simp only [fullQField, fullQIntegral, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_ofNat, Polynomial.map_pow, coeff_sub, coeff_ofNat_mul]
    change 2 * ((fullC2Integral p hp).map (residueHom p)).coeff (2 * e) -
        2 * (actualRankDividedField p (by omega) ^ 2).coeff (2 * e) =
      2 * ((fullC2Integral p hp).map (residueHom p)).coeff (2 * e) -
        2 * (actualRankDividedField p (by omega)).coeff e ^ 2
    rw [hR2]
  change (fullQField p hp).coeff (2 * e) = 2 * (actualRankDividedField p (by omega)).coeff e ^ 2
  linear_combination 2 * hsame - hdef

theorem quadraticWronskian_top {K : Type*} [CommRing K] (Y R : K[X]) (d e : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hY : Y.natDegree ≤ d) (hR : R.natDegree ≤ e) :
    ((1 - X ^ 2) * (Y * R.derivative - Y.derivative * R)).coeff (d + e + 1) =
      -((e : K) - (d : K)) * Y.coeff d * R.coeff e := by
  have hy : TopBound Y d (Y.coeff d) := ⟨hY, rfl⟩
  have hr : TopBound R e (R.coeff e) := ⟨hR, rfl⟩
  have hdy := top_derivative hd hy
  have hdr := top_derivative he hr
  have h1 : TopBound (Y * R.derivative) (d + e - 1) ((e : K) * Y.coeff d * R.coeff e) :=
    top_reindex (top_mul hy hdr) (by omega) (by ring)
  have h2 : TopBound (Y.derivative * R) (d + e - 1) ((d : K) * Y.coeff d * R.coeff e) :=
    top_reindex (top_mul hdy hr) (by omega) (by ring)
  have hw : TopBound (Y * R.derivative - Y.derivative * R) (d + e - 1)
      (((e : K) - (d : K)) * Y.coeff d * R.coeff e) := top_reindex (top_sub h1 h2) rfl (by ring)
  have h := top_reindex (top_mul top_quadratic hw)
    (show 2 + (d + e - 1) = d + e + 1 by omega)
    (show (-1 : K) * (((e : K) - (d : K)) * Y.coeff d * R.coeff e) =
      -((e : K) - (d : K)) * Y.coeff d * R.coeff e by ring)
  exact h.2

theorem actual_first_rank_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (actualLegendreJacobi p * (actualRankDividedField p (by omega)).derivative -
      (actualLegendreJacobi p).derivative * actualRankDividedField p (by omega)) =
      X * actualLegendreJacobi p ^ 2 - X ^ p := by
  have hxp : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by simp [derivative_X_pow]
  rw [actual_rankDividedField_eq_hat p hp]
  simp only [rankHatField, derivative_sub, derivative_mul, derivative_add,
    derivative_C, add_zero, hxp, zero_mul, zero_add]
  linear_combination actualLegendreJacobi p ^ 2 * evenLogPolynomial_source p hp -
    X ^ p * properLegendreJacobi_wronskian p (by omega)

theorem actual_rank_top_product (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 + 2 * ((p / 6 : ℕ) : ZMod p)) * (actualLegendreJacobi p).coeff (p / 6) *
      (actualRankDividedField p (by omega)).coeff (fullCutoff p) = -1 := by
  let d := p / 6
  let e := fullCutoff p
  have hindex : d + e + 1 = p := by dsimp [d, e, fullCutoff]; omega
  have htop := congrArg (fun P : (ZMod p)[X] => P.coeff p) (actual_first_rank_wronskian p hp)
  have hleft := quadraticWronskian_top (actualLegendreJacobi p) (actualRankDividedField p (by omega))
    d e (by dsimp [d]; omega) (by dsimp [e, fullCutoff]; omega)
    (actualLegendreJacobi_degree p) (actualRankDividedField_degree p (by omega))
  rw [hindex] at hleft
  rw [hleft, coeff_sub] at htop
  have hlow : (X * actualLegendreJacobi p ^ 2).coeff p = 0 := by
    have hY := actualLegendreJacobi_degree p
    have hY2 := natDegree_pow_le_of_le 2 hY
    have hd := natDegree_mul_le_of_le (natDegree_X_le (R := ZMod p)) hY2
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [d] at *
    omega
  rw [hlow, coeff_X_pow, if_pos rfl, zero_sub] at htop
  have hsum : (d : ZMod p) + (e : ZMod p) + 1 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hindex
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using h
  change (1 + 2 * (d : ZMod p)) * (actualLegendreJacobi p).coeff d *
    (actualRankDividedField p (by omega)).coeff e = -1
  linear_combination htop + (actualLegendreJacobi p).coeff d *
    (actualRankDividedField p (by omega)).coeff e * hsum

theorem actual_fullGreen_degree_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (quadraticGreen (actualLegendreJacobi p) (fullQField p hp)).natDegree ≤ 2 * p ∧
      (quadraticGreen (actualLegendreJacobi p) (fullQField p hp)).coeff (2 * p) = 4 := by
  let d := p / 6
  let e := fullCutoff p
  have hindex : 2 * d + 2 * e + 2 = 2 * p := by dsimp [d, e, fullCutoff]; omega
  obtain ⟨hdeg, htop⟩ := quadraticGreen_degree_top (actualLegendreJacobi p) (fullQField p hp) d (2 * e)
    (by dsimp [d]; omega) (by dsimp [e, fullCutoff]; omega)
    (actualLegendreJacobi_degree p) (fullQField_degree p hp)
  rw [hindex] at hdeg htop
  refine ⟨hdeg, ?_⟩
  rw [actual_fullQ_top p hp] at htop
  push_cast at htop
  have hsum : (d : ZMod p) + (e : ZMod p) + 1 = 0 := by
    have h : d + e + 1 = p := by dsimp [d, e, fullCutoff]; omega
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hc
  have he : (e : ZMod p) = -(d : ZMod p) - 1 := by linear_combination hsum
  have hunit := actual_rank_top_product p hp
  change (1 + 2 * (d : ZMod p)) * (actualLegendreJacobi p).coeff d *
    (actualRankDividedField p (by omega)).coeff e = -1 at hunit
  have halg : (2 * (e : ZMod p) + 1) * (2 * (e : ZMod p) - 2 * (d : ZMod p)) *
      (actualLegendreJacobi p).coeff d ^ 2 * (2 * (actualRankDividedField p (by omega)).coeff e ^ 2) =
      4 * ((1 + 2 * (d : ZMod p)) * (actualLegendreJacobi p).coeff d *
        (actualRankDividedField p (by omega)).coeff e) ^ 2 := by rw [he]; ring
  rw [halg, hunit] at htop
  norm_num at htop
  exact htop

theorem actual_full_divided_discriminant_degree_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((fullDividedDiscriminantIntegral p hp).map (residueHom p)).natDegree ≤ 2 * p ∧
      ((fullDividedDiscriminantIntegral p hp).map (residueHom p)).coeff (2 * p) = 5 := by
  let Y := actualLegendreJacobi p
  let R := actualRankDividedField p (by omega)
  let A : (ZMod p)[X] := (1 - X ^ 2) * Y ^ 3 * (Y + 2 * X * R.derivative + R)
  let G := quadraticGreen Y (fullQField p hp)
  let M := (fullDividedDiscriminantIntegral p hp).map (residueHom p)
  let d := p / 6
  let e := fullCutoff p
  have hY : Y.natDegree ≤ d := actualLegendreJacobi_degree p
  have hR : R.natDegree ≤ e := actualRankDividedField_degree p (by omega)
  have hRd : R.derivative.natDegree ≤ e - 1 :=
    (natDegree_derivative_le R).trans (Nat.sub_le_sub_right hR 1)
  have hXR : (2 * X * R.derivative).natDegree ≤ e := by
    have h2X : (2 * (X : (ZMod p)[X])).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    have h := natDegree_mul_le_of_le h2X hRd
    dsimp [e, fullCutoff] at *
    omega
  have hforce : (Y + 2 * X * R.derivative + R).natDegree ≤ e := by
    have hYe : Y.natDegree ≤ e := hY.trans (by dsimp [d, e, fullCutoff]; omega)
    exact (natDegree_add_le_of_le (natDegree_add_le_of_le hYe hXR) hR).trans (by simp)
  have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
  have hY3 : (Y ^ 3).natDegree ≤ 3 * d := natDegree_pow_le_of_le 3 hY
  have hA : A.natDegree < 2 * p := by
    have h := natDegree_mul_le_of_le (natDegree_mul_le_of_le hq hY3) hforce
    dsimp [A, d, e, fullCutoff] at *
    omega
  obtain ⟨hG, hGtop⟩ := actual_fullGreen_degree_top p hp
  change G.natDegree ≤ 2 * p at hG
  change G.coeff (2 * p) = 4 at hGtop
  have hs0 : 4 * M = -20 * (1 - X ^ 2) * Y ^ 3 *
      (Y + 2 * X * R.derivative + R) + 5 * G :=
    actual_full_discriminant_field_source_four p hp
  have hs : 4 * M = -20 * A + 5 * G := hs0.trans (by dsimp only [A]; ring)
  have h4 : (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hMdeg : M.natDegree ≤ 2 * p := by
    have h1 : (-20 * A).natDegree ≤ 2 * p := by
      simpa only [_root_.map_neg, _root_.map_ofNat] using
        (natDegree_C_mul_le (-20 : ZMod p) A).trans hA.le
    have h2 : (5 * G).natDegree ≤ 2 * p := by
      simpa only [_root_.map_ofNat] using (natDegree_C_mul_le (5 : ZMod p) G).trans hG
    have hh : (-20 * A + 5 * G).natDegree ≤ 2 * p := by
      simpa only [max_self] using natDegree_add_le_of_le h1 h2
    have hn : (4 * M).natDegree = M.natDegree := natDegree_C_mul h4
    rw [← hn, hs]
    exact hh
  refine ⟨hMdeg, ?_⟩
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff (2 * p)) hs
  have hAc : A.coeff (2 * p) = 0 := coeff_eq_zero_of_natDegree_lt hA
  have hneg : -20 * A = -(20 * A) := by ring
  rw [hneg, coeff_add, coeff_neg, coeff_ofNat_mul, coeff_ofNat_mul, coeff_ofNat_mul, hAc, hGtop] at hc
  apply mul_left_cancel₀ h4
  linear_combination hc

theorem fullWeightedDiscriminant_even (p : ℕ) :
    (fullWeightedDiscriminant p).comp (-X) = fullWeightedDiscriminant p := by
  let F := WPReview.nativePolynomial (fullCutoff p + 1)
  let q : ℚ[X] := 1 - X ^ 2
  have hq : q.comp (-X) = q := by simp [q]
  have htwo := native_discriminant_quadratic F
  change 2 * jacobiDiscriminant 0 (F.comp q) = (WPActualNativeFirstIntegral.nativeDiscriminant F).comp q at htwo
  have hD : (jacobiDiscriminant 0 (F.comp q)).comp (-X) = jacobiDiscriminant 0 (F.comp q) := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℚ[X]) ≠ 0)
    calc
      2 * (jacobiDiscriminant 0 (F.comp q)).comp (-X) = (2 * jacobiDiscriminant 0 (F.comp q)).comp (-X) := by simp
      _ = ((WPActualNativeFirstIntegral.nativeDiscriminant F).comp q).comp (-X) := by rw [htwo]
      _ = (WPActualNativeFirstIntegral.nativeDiscriminant F).comp q := by rw [comp_assoc, hq]
      _ = 2 * jacobiDiscriminant 0 (F.comp q) := htwo.symm
  change (q * jacobiDiscriminant 0 (F.comp q)).comp (-X) = q * jacobiDiscriminant 0 (F.comp q)
  rw [mul_comp, hq, hD]

theorem actual_full_divided_discriminant_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((fullDividedDiscriminantIntegral p hp).map (residueHom p)).comp (-X) =
      (fullDividedDiscriminantIntegral p hp).map (residueHom p) := by
  have hi : (fullDividedDiscriminantIntegral p hp).comp (-X) = fullDividedDiscriminantIntegral p hp := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [Polynomial.map_comp, actual_full_discriminant_divided_two_value]
    simp only [Polynomial.map_neg, Polynomial.map_X, mul_comp, C_comp, fullWeightedDiscriminant_even]
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simpa only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using hf

theorem actual_full_divided_discriminant_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((fullDividedDiscriminantIntegral p hp).map (residueHom p)).eval 1 = 0 := by
  have hi : (fullDividedDiscriminantIntegral p hp).eval 1 = 0 := by
    apply Subtype.ext
    have hv := congrArg (fun P : ℚ[X] => P.eval 1) (actual_full_discriminant_divided_two_value p hp)
    simpa [eval_map, eval₂_at_one, fullWeightedDiscriminant] using hv
  simpa only [eval_map, eval₂_at_one, _root_.map_zero] using congrArg (residueHom p) hi

theorem actual_full_divided_discriminant_normalization (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullDividedDiscriminantIntegral p hp).map (residueHom p) = 5 * (X ^ (2 * p) - 1) := by
  let M := (fullDividedDiscriminantIntegral p hp).map (residueHom p)
  let H : (ZMod p)[X] := X ^ (2 * p) - 1
  obtain ⟨hdeg, htop⟩ := actual_full_divided_discriminant_degree_top p hp
  have hHdeg : H.natDegree ≤ 2 * p := by dsimp [H]; compute_degree
  have hHder : H.derivative = 0 := by simp [H, derivative_X_pow, Nat.cast_mul]
  have hHpar : H.comp (-X) = H := by
    have hx : (-X : (ZMod p)[X]) ^ (2 * p) = X ^ (2 * p) := by rw [pow_mul, pow_mul]; simp
    simp only [H, sub_comp, pow_comp, X_comp, one_comp, hx]
  have hHtop : H.coeff (2 * p) = 1 := by
    have hn : 2 * p ≠ 0 := by omega
    simp [H, coeff_sub, coeff_X_pow, coeff_one, hn]
  have hz : M - 5 * H = 0 := by
    apply even_derivative_zero_two_digits_eq_zero p hp
    · have h5 : (5 * H).natDegree ≤ 2 * p := (natDegree_C_mul_le _ _).trans hHdeg
      simpa only [max_self] using natDegree_sub_le_of_le hdeg h5
    · dsimp only [M]
      rw [derivative_sub, show (5 : (ZMod p)[X]) = C (5 : ZMod p) by rfl,
        derivative_C_mul, actual_full_divided_discriminant_derivative_zero, hHder,
        mul_zero, sub_zero]
    · dsimp only [M]
      rw [sub_comp, mul_comp, ofNat_comp, actual_full_divided_discriminant_even, hHpar]
      simp only [Nat.cast_ofNat]
    · rw [coeff_sub, coeff_ofNat_mul, htop, hHtop]; ring
    · dsimp only [M]
      simp only [eval_sub, eval_mul, eval_ofNat, actual_full_divided_discriminant_endpoint,
        H, eval_sub, eval_pow, eval_X, eval_one, one_pow]
      ring
  exact sub_eq_zero.mp hz

theorem actual_full_second_Green_normalization (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    quadraticGreen (actualLegendreJacobi p) (fullQField p hp) =
      4 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
        (actualLegendreJacobi p + 2 * X * (actualRankDividedField p (by omega)).derivative +
          actualRankDividedField p (by omega)) + 4 * (X ^ (2 * p) - 1) := by
  have hs := actual_full_discriminant_field_source_four p hp
  rw [actual_full_divided_discriminant_normalization p hp] at hs
  have h5 : (5 : (ZMod p)[X]) ≠ 0 := C_ne_zero.mpr
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  apply mul_left_cancel₀ h5
  linear_combination -hs

theorem actual_half_divided_two_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (M : (integralRationals p)[X])
    (hM : M.map (integralRationals p).subtype = C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p) :
    (M.map (residueHom p)).derivative = C (-8 * residueHom p (nativeHalfDivPrime p hp)) *
      X * (1 - X ^ 2) ^ ((p - 1) / 2) * actualLegendreJacobi p ^ 2 := by
  have hi : M.derivative = C (2 * (9 * (p : integralRationals p) ^ 2 - 4) * nativeHalfDivPrime p hp) *
      X * (1 - X ^ 2) ^ ((p - 1) / 2) * integralNativeJacobi p hp := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [← derivative_map, hM, derivative_C_mul, weightedNativeDiscriminant,
      actual_half_native_weighted_source p hp]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, integralNativeJacobi_rational,
      Subring.subtype_apply]
    have hpq : (p : ℚ) ≠ 0 := by positivity
    have hc : (1 / (p : ℚ) ^ 2) * (2 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2)) =
      2 * (9 * (p : ℚ) ^ 2 - 4) * (nativeHalfDivPrime p hp).val := by
      change _ = 2 * (9 * (p : ℚ) ^ 2 - 4) * (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ))
      field_simp [hpq]
    have he := congrArg (C : ℚ → ℚ[X]) hc
    simp only [Subring.coe_mul, integral_sub_value, Subring.coe_pow, Subring.coe_natCast,
      show (2 : integralRationals p).val = (2 : ℚ) by rfl,
      show (9 : integralRationals p).val = (9 : ℚ) by rfl,
      show (4 : integralRationals p).val = (4 : ℚ) by rfl]
    simp only [_root_.map_mul, _root_.map_sub, _root_.map_pow, _root_.map_ofNat, _root_.map_natCast] at he ⊢
    linear_combination (X * (1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p) * he
  rw [derivative_map, hi]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat,
    Polynomial.map_natCast, field_prime_zero, integralNativeJacobi_field, _root_.map_mul, _root_.map_sub,
    _root_.map_pow, _root_.map_ofNat, _root_.map_neg, _root_.map_natCast,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_sub]
  ring

theorem actual_full_minus_half_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (M : (integralRationals p)[X])
    (hM : M.map (integralRationals p).subtype = C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p) :
    ((fullDividedDiscriminantIntegral p hp).map (residueHom p) - M.map (residueHom p)).derivative =
      C (8 * residueHom p (nativeHalfDivPrime p hp)) *
        X * (1 - X ^ 2) ^ ((p - 1) / 2) * actualLegendreJacobi p ^ 2 := by
  rw [derivative_sub, actual_full_divided_discriminant_derivative_zero,
    actual_half_divided_two_derivative p hp M hM]
  simp only [_root_.map_mul, _root_.map_neg, _root_.map_ofNat]
  ring

end WPFieldAssembly.NativeFullGreen
