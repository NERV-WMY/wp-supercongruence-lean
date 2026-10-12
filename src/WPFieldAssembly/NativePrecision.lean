import WPFieldAssembly.NativeDiscriminant
import WPNativeCutoff
import WPHasseIntegralTransport
import Mathlib.Algebra.Polynomial.Lifts
import WPActualNativeCubicInvariant

open scoped Polynomial
open Polynomial WPFieldAssembly.TerminatingSquare WPFieldAssembly.NativeDiscriminant
  WPPIntegralReduction WPActualNativeFirstIntegral

namespace WPFieldAssembly.NativePrecision

set_option maxHeartbeats 800000

theorem rational_native_degree (n : ℕ) :
    (WPReview.nativePolynomial (n + 1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [WPReview.nativePolynomial_coeff, if_neg (by omega)]
  · rw [WPReview.nativePolynomial_coeff, if_pos (by omega)]
    exact WPNativeMomentIntegrality.nativeCoefficient_ne_zero n

theorem quadratic_degree : (1 - X ^ 2 : ℚ[X]).natDegree = 2 := by
  compute_degree
  norm_num

theorem quadratic_leading : (1 - X ^ 2 : ℚ[X]).leadingCoeff = -1 := by
  rw [leadingCoeff, quadratic_degree]
  rw [coeff_sub, coeff_X_pow, coeff_one]
  norm_num

/-- The entire finite source retains the highest coefficient of both factors. -/
theorem half_native_product_top (p : ℕ) :
    ((1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p).coeff
      (4 * ((p - 1) / 2)) = WPReview.nativeCoefficient ((p - 1) / 2) := by
  let n := (p - 1) / 2
  have hf : (halfNativeJacobi p).natDegree ≤ 2 * n := by
    rw [halfNativeJacobi, natDegree_comp, rational_native_degree, quadratic_degree]
    omega
  have hq : ((1 - X ^ 2 : ℚ[X]) ^ n).natDegree ≤ 2 * n := by
    rw [natDegree_pow, quadratic_degree]
    omega
  have hfc : (halfNativeJacobi p).coeff (2 * n) =
      WPReview.nativeCoefficient n * (-1 : ℚ) ^ n := by
    have hc := coeff_comp_degree_mul_degree
      (p := WPReview.nativePolynomial (n + 1))
      (q := (1 - X ^ 2 : ℚ[X])) (by rw [quadratic_degree]; norm_num)
    rw [rational_native_degree, quadratic_degree, leadingCoeff,
      rational_native_degree, WPReview.nativePolynomial_coeff,
      if_pos (by omega), quadratic_leading] at hc
    simpa only [halfNativeJacobi, n, Nat.mul_comm] using hc
  have hqc : ((1 - X ^ 2 : ℚ[X]) ^ n).coeff (2 * n) = (-1 : ℚ) ^ n := by
    have hc := coeff_pow_mul_natDegree (p := (1 - X ^ 2 : ℚ[X])) n
    rw [quadratic_degree, quadratic_leading] at hc
    simpa only [Nat.mul_comm] using hc
  rw [show 4 * ((p - 1) / 2) = 2 * n + 2 * n by dsimp [n]; omega,
    coeff_mul_add_eq_of_natDegree_le hq hf, hqc, hfc]
  have hs : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℚ) ^ n * (WPReview.nativeCoefficient n * (-1 : ℚ) ^ n) =
        WPReview.nativeCoefficient n * ((-1 : ℚ) ^ n * (-1 : ℚ) ^ n) := by ring
    _ = _ := by rw [hs, mul_one]

noncomputable def weightedNativeDiscriminant (p : ℕ) : ℚ[X] :=
  (1 - X ^ 2) * jacobiDiscriminant 0 (halfNativeJacobi p)

/-- The literal 2p coefficient is forced before any p-division or reduction. -/
theorem actual_native_discriminant_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (weightedNativeDiscriminant p).coeff (2 * p) =
      (9 * (p : ℚ) ^ 2 - 4) * WPReview.nativeCoefficient ((p - 1) / 2) ^ 2 := by
  let n := (p - 1) / 2
  have hpn := WPFiniteWSource.half_exponent p hp
  have hindex : 4 * n + 1 + 1 = 2 * p := by dsimp [n]; omega
  have he := actual_half_native_weighted_source p hp
  have hr : C (2 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
      WPReview.nativeCoefficient ((p - 1) / 2)) * X *
      (1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p =
      C (2 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2)) *
      (X * ((1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p)) := by ring
  rw [hr] at he
  have hc := congrArg (fun P : ℚ[X] => P.coeff (4 * n + 1)) he
  rw [coeff_derivative, hindex, coeff_C_mul, coeff_X_mul,
    half_native_product_top] at hc
  have hc' : (2 * (p : ℚ)) * (weightedNativeDiscriminant p).coeff (2 * p) =
      (2 * (p : ℚ)) * ((9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2) ^ 2) := by
    dsimp only [weightedNativeDiscriminant]
    push_cast at hc
    have hq := congrArg (fun k : ℕ => (k : ℚ)) hindex
    push_cast at hq
    rw [hq] at hc
    linear_combination hc
  exact mul_left_cancel₀ (by positivity : (2 * (p : ℚ)) ≠ 0) hc'

theorem actual_native_half_valuation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    padicValRat p (WPReview.nativeCoefficient ((p - 1) / 2)) = 1 := by
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hn : (p - 1) / 2 < p := by omega
  have h6 : 6 * ((p - 1) / 2) / p = 2 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * ((p - 1) / 2) / p = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime
    p ((p - 1) / 2) (by omega) hn, h6, h3]
  norm_num

theorem actual_native_half_div_prime_valuation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    padicValRat p (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ)) = 0 := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicValRat.div (WPNativeMomentIntegrality.nativeCoefficient_ne_zero _) hpq,
    padicValRat.self (Fact.out : p.Prime).one_lt, actual_native_half_valuation p hp]
  norm_num

noncomputable def nativeHalfDivPrime (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  ⟨WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ), by
    change 0 ≤ padicValRat p (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ))
    rw [actual_native_half_div_prime_valuation p hp]⟩

theorem actual_native_half_div_prime_residue_ne_zero
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (nativeHalfDivPrime p hp) ≠ 0 := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro hz
  have hcong := (integral_residue_zero_iff p _ (nativeHalfDivPrime p hp).property).mp hz
  simp only [WPReview.RationalCongruent, sub_zero, Nat.cast_one] at hcong
  rcases hcong with hq0 | hv
  · exact (div_ne_zero (WPNativeMomentIntegrality.nativeCoefficient_ne_zero _) hpq) hq0
  · change 1 ≤ padicValRat p
      (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ)) at hv
    rw [actual_native_half_div_prime_valuation p hp] at hv
    omega

/-- Division is performed on the actual rational polynomial before its residue is taken. -/
theorem exists_integral_polynomial_div_prime (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[X]) (hres : P.map (residueHom p) = 0) :
    ∃ Q : (integralRationals p)[X],
      Q.map (integralRationals p).subtype =
        C (1 / (p : ℚ)) * P.map (integralRationals p).subtype ∧
      Q.natDegree = P.natDegree := by
  let F : ℚ[X] := C (1 / (p : ℚ)) * P.map (integralRationals p).subtype
  have hF : F ∈ Polynomial.lifts (integralRationals p).subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts
      (f := (integralRationals p).subtype) F).mpr
    intro n
    have hr : ((P.coeff n).val : ZMod p) = 0 := by
      have hn := congrArg (fun A : (ZMod p)[X] => A.coeff n) hres
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
      exact hn
    have hi := WPActualChiSource.divide_prime_integral p
      (P.coeff n).val (P.coeff n).property hr
    refine ⟨⟨(P.coeff n).val / (p : ℚ), hi⟩, ?_⟩
    change (P.coeff n).val / (p : ℚ) =
      (C (1 / (p : ℚ)) * P.map (integralRationals p).subtype).coeff n
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    change (P.coeff n).val / (p : ℚ) = (1 / (p : ℚ)) * (P.coeff n).val
    ring
  obtain ⟨Q, hQ, hdeg⟩ := Polynomial.exists_natDegree_eq_of_mem_lifts hF
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨Q, hQ, ?_⟩
  calc
    Q.natDegree = F.natDegree := hdeg
    _ = (P.map (integralRationals p).subtype).natDegree := by
      dsimp only [F]
      exact Polynomial.natDegree_C_mul (div_ne_zero one_ne_zero hpq)
    _ = P.natDegree := Polynomial.natDegree_map_eq_of_injective
      (Subring.subtype_injective (integralRationals p)) P

theorem jacobiDiscriminant_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (G : R[X]) :
    (jacobiDiscriminant t G).map f = jacobiDiscriminant (f t) (G.map f) := by
  simp only [jacobiDiscriminant, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_ofNat, ← derivative_map]
  simp only [map_add, map_mul, map_one, map_ofNat]

/-- The top coefficient is supplied explicitly before the derivative kernel is used. -/
theorem even_derivative_zero_two_digits_eq_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (hdeg : P.natDegree ≤ 2 * p) (hder : P.derivative = 0)
    (heven : P.comp (-X) = P) (htop : P.coeff (2 * p) = 0) (hone : P.eval 1 = 0) :
    P = 0 := by
  by_cases hz : P = 0
  · exact hz
  have hstrict : P.natDegree < 2 * p := by
    by_contra hn
    have hd : P.natDegree = 2 * p := by omega
    apply (leadingCoeff_ne_zero.mpr hz)
    rw [← coeff_natDegree, hd, htop]
  have hshape : P = C (P.coeff 0) + C (P.coeff p) * X ^ p :=
    WPActualNativeCubicInvariant.derivative_zero_two_digits p P hstrict hder
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hnegpow : (-1 : ZMod p) ^ p = -1 := by rw [hodd.neg_pow, one_pow]
  have hminus : P.eval (-1) = P.coeff 0 - P.coeff p := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval (-1)) hshape
    simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X,
      hnegpow, mul_neg, mul_one, sub_eq_add_neg] using he
  have hplus : P.eval 1 = P.coeff 0 + P.coeff p := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hshape
    simpa only [eval_add, eval_C, eval_mul, eval_pow, eval_X,
      one_pow, mul_one] using he
  have hpair : P.eval (-1) = P.eval 1 := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) heven
    simpa only [eval_comp, eval_neg, eval_X] using he
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
    have hl := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  have hpcoeff : P.coeff p = 0 := by
    have he : P.coeff 0 - P.coeff p = P.coeff 0 + P.coeff p :=
      hminus.symm.trans (hpair.trans hplus)
    have hk : (2 : ZMod p) * P.coeff p = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hk).resolve_left h2
  have hconstant : P.coeff 0 = 0 := by
    have he := hplus
    rw [hone, hpcoeff, add_zero] at he
    exact he.symm
  simpa only [hconstant, hpcoeff, map_zero, zero_mul, add_zero] using hshape

noncomputable def integralNativeJacobi (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (WPHasseIntegralTransport.nativeIntegral p ((p - 1) / 2) (by omega) (by omega)).comp
    (1 - X ^ 2)

theorem integralNativeJacobi_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralNativeJacobi p hp).map (integralRationals p).subtype = halfNativeJacobi p := by
  rw [integralNativeJacobi, Polynomial.map_comp,
    WPHasseIntegralTransport.nativeIntegral_map_rational]
  simp only [halfNativeJacobi, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X]

theorem integralNativeJacobi_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralNativeJacobi p hp).map (residueHom p) =
      WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2 := by
  rw [integralNativeJacobi, Polynomial.map_comp,
    WPHasseIntegralTransport.nativeIntegral_map_field,
    WPActualNativeHasse.actual_full_native_field_cutoff p ((p - 1) / 2)
      (by omega) (by omega) (by
        have := Nat.div_mul_le_self p 6
        have := WPFiniteWSource.half_exponent p hp
        omega)]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  exact WPActualNativeQuadraticSquare.actual_native_Jacobi_square p hp

theorem integralTerm_discriminant_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    jacobiDiscriminant 0 (integralJacobiTerm p hp) =
      C (p : integralRationals p) * integralDiscriminantCarry p hp := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [jacobiDiscriminant_map, integralJacobiTerm_rational, Polynomial.map_mul,
    Polynomial.map_C, integralDiscriminantCarry_rational]
  simp only [map_zero, map_natCast]
  rw [← mul_assoc, ← C_eq_natCast, ← C_mul, mul_one_div_cancel (by positivity : (p : ℚ) ≠ 0),
    C_1, one_mul]

noncomputable def integralNativeDiscriminant (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (1 - X ^ 2) * jacobiDiscriminant 0 (integralNativeJacobi p hp)

theorem integralNativeDiscriminant_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralNativeDiscriminant p hp).map (integralRationals p).subtype =
      weightedNativeDiscriminant p := by
  rw [integralNativeDiscriminant, Polynomial.map_mul, jacobiDiscriminant_map,
    integralNativeJacobi_rational]
  simp only [weightedNativeDiscriminant, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, map_zero]

theorem integralNativeDiscriminant_field_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralNativeDiscriminant p hp).map (residueHom p) = 0 := by
  have he := congrArg (Polynomial.map (residueHom p)) (integralTerm_discriminant_source p hp)
  rw [jacobiDiscriminant_map, integralJacobiTerm_field, Polynomial.map_mul,
    Polynomial.map_C] at he
  simp only [map_zero, map_natCast, ZMod.natCast_self, zero_mul] at he
  rw [integralNativeDiscriminant, Polynomial.map_mul, jacobiDiscriminant_map,
    integralNativeJacobi_field, map_zero, he, mul_zero]

theorem jacobiDiscriminant_zero_degree_bound {K : Type*} [CommRing K]
    (G : K[X]) (n : ℕ) (hn : 1 ≤ n) (hG : G.natDegree ≤ 2 * n) :
    (jacobiDiscriminant 0 G).natDegree ≤ 4 * n := by
  have hD : G.derivative.natDegree ≤ 2 * n - 1 := by
    have hd := natDegree_derivative_le G
    omega
  have hDD : G.derivative.derivative.natDegree ≤ 2 * n - 2 := by
    have hd := natDegree_derivative_le G.derivative
    omega
  have h1 : (1 : K[X]).natDegree ≤ 0 := by simp
  have h2 : (2 : K[X]).natDegree ≤ 0 := by simp
  have h9 : (9 : K[X]).natDegree ≤ 0 := by simp
  have h36 : (36 : K[X]).natDegree ≤ 0 := by simp
  have hX : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
  have hX2 : (X ^ 2 : K[X]).natDegree ≤ 2 := by
    simpa using natDegree_pow_le_of_le 2 hX
  have hQ : (1 - X ^ 2 : K[X]).natDegree ≤ 2 :=
    (natDegree_sub_le_of_le h1 hX2).trans (by omega)
  have hprod : (2 * G * G.derivative.derivative).natDegree ≤ 4 * n - 2 :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le h2 hG) hDD).trans (by omega)
  have hsqD : (G.derivative ^ 2).natDegree ≤ 4 * n - 2 :=
    (natDegree_pow_le_of_le 2 hD).trans (by omega)
  have hbox : (2 * G * G.derivative.derivative - G.derivative ^ 2).natDegree ≤
      4 * n - 2 := by
    simpa only [max_self] using natDegree_sub_le_of_le hprod hsqD
  have hfirst : (9 * (1 - X ^ 2) *
      (2 * G * G.derivative.derivative - G.derivative ^ 2)).natDegree ≤ 4 * n :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le h9 hQ) hbox).trans (by omega)
  have hC1 : (C (1 + (0 : K)) : K[X]).natDegree ≤ 0 := by simp
  have hmiddle : (36 * C (1 + (0 : K)) * X * G * G.derivative).natDegree ≤ 4 * n :=
    (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le h36 hC1) hX) hG) hD).trans (by omega)
  have hC5 : (C ((1 + 6 * (0 : K)) * (5 + 6 * 0)) : K[X]).natDegree ≤ 0 := by simp
  have hsqG : (G ^ 2).natDegree ≤ 4 * n :=
    (natDegree_pow_le_of_le 2 hG).trans (by omega)
  have hlast : (C ((1 + 6 * (0 : K)) * (5 + 6 * 0)) * G ^ 2).natDegree ≤ 4 * n :=
    (natDegree_mul_le_of_le hC5 hsqG).trans (by omega)
  unfold jacobiDiscriminant
  simpa only [max_self] using natDegree_sub_le_of_le
    (natDegree_sub_le_of_le hfirst hmiddle) hlast

theorem weightedNativeDiscriminant_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (weightedNativeDiscriminant p).natDegree ≤ 2 * p := by
  have hpn := WPFiniteWSource.half_exponent p hp
  have hn : 1 ≤ (p - 1) / 2 := by omega
  have hG : (halfNativeJacobi p).natDegree ≤ 2 * ((p - 1) / 2) := by
    rw [halfNativeJacobi, natDegree_comp, rational_native_degree, quadratic_degree]
    omega
  have hQ : (1 - X ^ 2 : ℚ[X]).natDegree ≤ 2 := quadratic_degree.le
  exact (natDegree_mul_le_of_le hQ
    (jacobiDiscriminant_zero_degree_bound (halfNativeJacobi p) ((p - 1) / 2) hn hG)).trans
      (by omega)

theorem weightedNativeDiscriminant_even (p : ℕ) :
    (weightedNativeDiscriminant p).comp (-X) = weightedNativeDiscriminant p := by
  let F := WPReview.nativePolynomial ((p - 1) / 2 + 1)
  have hq : (1 - X ^ 2 : ℚ[X]).comp (-X) = 1 - X ^ 2 := by simp
  have he : 2 * weightedNativeDiscriminant p =
      (1 - X ^ 2) * (nativeDiscriminant F).comp (1 - X ^ 2) := by
    have hd := native_discriminant_quadratic F
    dsimp only [weightedNativeDiscriminant, halfNativeJacobi, F] at hd ⊢
    linear_combination (1 - X ^ 2) * hd
  apply mul_left_cancel₀ (by norm_num : (2 : ℚ[X]) ≠ 0)
  calc
    2 * (weightedNativeDiscriminant p).comp (-X) =
        (2 * weightedNativeDiscriminant p).comp (-X) := by simp
    _ = ((1 - X ^ 2) * (nativeDiscriminant F).comp (1 - X ^ 2)).comp (-X) := by rw [he]
    _ = (1 - X ^ 2) * (nativeDiscriminant F).comp (1 - X ^ 2) := by
      rw [mul_comp, hq, comp_assoc, hq]
    _ = 2 * weightedNativeDiscriminant p := he.symm

end WPFieldAssembly.NativePrecision
