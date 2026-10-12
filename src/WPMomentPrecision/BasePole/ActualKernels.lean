import WPActualResonanceReduction
import WPFiniteEntropy

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualMomentDefect WPActualEtaIntegration WPActualEtaSupport
  WPActualEtaIntegrality WPActualChiSource WPPIntegralReduction

namespace WPMomentPrecision.BasePole

/-- The original integer Fermat quotient, cast only after its integer division. -/
def fermatQ (p a : ℕ) : ℚ :=
  (WPFiniteInversion.integerFermatQuotient p (a : ℤ) : ℚ)

def fermatUnit (p a : ℕ) : ℚ := (a : ℚ) ^ (p - 1)

theorem fermatUnit_eq (p a : ℕ) [Fact p.Prime]
    (ha : ((a : ℤ) : ZMod p) ≠ 0) :
    fermatUnit p a = 1 + (p : ℚ) * fermatQ p a := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (WPFiniteInversion.integerFermatQuotient_mul p (a : ℤ) ha)
  push_cast at h
  unfold fermatUnit fermatQ
  linear_combination -h

theorem fermatUnit_two_ne_zero (p : ℕ) : fermatUnit p 2 ≠ 0 := by
  unfold fermatUnit
  positivity

theorem actual_endpoint_coefficients (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    endpointA p ((p - 1) / 2) = fermatQ p 2 / fermatUnit p 2 ∧
      endpointB p ((p - 1) / 2) = -fermatQ p 2 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hu := fermatUnit_eq p 2 (by simpa using h2)
  have hN := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hfour : (4 : ℚ) ^ ((p - 1) / 2) = fermatUnit p 2 := by
    unfold fermatUnit
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  have hquarter : (1 / 4 : ℚ) ^ ((p - 1) / 2) =
      (fermatUnit p 2)⁻¹ := by
    rw [one_div, inv_pow, hfour]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hu0 := fermatUnit_two_ne_zero p
  constructor
  · unfold endpointA
    rw [hquarter]
    field_simp [hpq, hu0]
    linear_combination hu
  · unfold endpointB
    rw [hfour]
    field_simp [hpq]
    linear_combination -hu

/-- Inversion reverses the original two rational square-root endpoints. -/
noncomputable def reflectedDensity : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] where
  toFun P := T (-2) * invert P
  map_add' P Q := by rw [map_add, mul_add]
  map_smul' a P := by
    simp only [smul_eq_C_mul, map_mul, invert_C, RingHom.id_apply]
    ring

theorem reflectedDensity_monomial (a : ℚ) (j : ℤ) :
    reflectedDensity (C a * T j) = C a * T (-j - 2) := by
  change T (-2) * invert (C a * T j) = _
  rw [map_mul, invert_C, invert_T]
  calc
    _ = C a * (T (-2) * T (-j)) := by ring
    _ = _ := by rw [← T_add]; congr 2; omega

theorem original_endpoints_neg_index (m : ℤ) :
    WPFiniteConductorReflection.monomialEndpoint (-m) (1 / 2) 2 =
      WPFiniteConductorReflection.monomialEndpoint m (1 / 2) 2 := by
  unfold WPFiniteConductorReflection.monomialEndpoint
  rw [WPFiniteConductorReflection.reciprocal_two_zpow,
    WPFiniteConductorReflection.reciprocal_two_zpow]
  simp only [neg_neg, Int.cast_neg, div_neg]
  ring

theorem reflectedDensity_integral (P : ℚ[T;T⁻¹]) :
    endpointIntegral (1 / 2) 2 (reflectedDensity P) =
      endpointIntegral (1 / 2) 2 P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | C_mul_T j a =>
    rw [reflectedDensity_monomial, integral_monomial, integral_monomial]
    rw [show -j - 2 + 1 = -(j + 1) by omega, original_endpoints_neg_index]

theorem reflectedDensity_C_mul (a : ℚ) (P : ℚ[T;T⁻¹]) :
    reflectedDensity (C a * P) = C a * reflectedDensity P := by
  change T (-2) * invert (C a * P) = _
  rw [map_mul, invert_C]
  change T (-2) * (C a * invert P) = C a * (T (-2) * invert P)
  ring

theorem actual_Vpull_reciprocal : invert Vpull = Qpull := by
  have hV : Vpull = C (1 / 125) * (4 * T 2 - 1) ^ 2 * (4 - T 2) := by
    simp only [Vpull, substitute, Vpolynomial, Xpull, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
      Polynomial.eval₂_one]
  have hT : (T 2 : ℚ[T;T⁻¹]) * T (-2) = 1 := by
    rw [← T_add]
    norm_num
  have hfirst : (4 * T (-2) - 1 : ℚ[T;T⁻¹]) = (4 - T 2) * T (-2) := by
    rw [sub_mul, hT]
  have hsecond : (4 - T (-2) : ℚ[T;T⁻¹]) = (4 * T 2 - 1) * T (-2) := by
    rw [sub_mul, mul_assoc, hT, mul_one, one_mul]
  have hcube : (T (-2) : ℚ[T;T⁻¹]) ^ 3 = T (-6) := by
    rw [T_pow]
    norm_num
  rw [hV, map_mul, map_mul, map_pow, map_sub, map_mul, map_ofNat,
    invert_T, map_one, map_sub, map_ofNat, invert_T, invert_C, hfirst, hsecond]
  unfold Qpull Xpull
  calc
    _ = (C (1 / 125) * (4 * T 2 - 1) * (4 - T 2) ^ 2 * T (-2) ^ 3 :
        ℚ[T;T⁻¹]) := by ring
    _ = _ := by rw [hcube]

/-- The entire actual base kernel after inversion, with both ordered ends. -/
noncomputable def baseKernel (p : ℕ) : ℚ[T;T⁻¹] := Qpull ^ p * T ((p : ℤ) - 1)

theorem actual_baseMoment_kernel (p : ℕ) (hp : 1 ≤ p) :
    baseMoment p = (p : ℚ) / 9 * endpointIntegral (1 / 2) 2 (baseKernel p) := by
  have hI : endpointIntegral (1 / 2) 2 (baseDensity p) =
      endpointIntegral (1 / 2) 2 (Vpull ^ p * T (-(p : ℤ) - 1)) := by
    have h := logarithmicSDensity_zero_integral p hp
    rw [logarithmicSDensity, map_sub] at h
    linear_combination h
  have hr : reflectedDensity (Vpull ^ p * T (-(p : ℤ) - 1)) = baseKernel p := by
    change T (-2) * invert (Vpull ^ p * T (-(p : ℤ) - 1)) = _
    rw [map_mul, map_pow, actual_Vpull_reciprocal, invert_T]
    unfold baseKernel
    calc
      _ = Qpull ^ p * (T (-2) * T (-(-(p : ℤ) - 1))) := by ring
      _ = _ := by rw [← T_add]; congr 2; omega
  rw [baseMoment, hI, ← reflectedDensity_integral, hr]

noncomputable def originalAKernel (p : ℕ) : ℚ[T;T⁻¹] :=
  T (-(p : ℤ)) * Vpull ^ (p - 1) * C 2 * T 1 * factorA

noncomputable def originalBKernel (p : ℕ) : ℚ[T;T⁻¹] :=
  T (-(p : ℤ)) * Vpull ^ (p - 1) * C 2 * T 1 * factorB

/-- The endpoint F-kernel is defined from the actual canceled pole source. -/
noncomputable def endpointFKernel (p : ℕ) : ℚ[T;T⁻¹] :=
  C 2 * reflectedDensity (originalAKernel p)

noncomputable def endpointGKernel (p : ℕ) : ℚ[T;T⁻¹] :=
  -reflectedDensity (originalBKernel p)

noncomputable def endpointFPeriod (p : ℕ) : ℚ :=
  (p : ℚ) * endpointIntegral (1 / 2) 2 (endpointFKernel p)

noncomputable def endpointGPeriod (p : ℕ) : ℚ :=
  (p : ℚ) * endpointIntegral (1 / 2) 2 (endpointGKernel p)

theorem integral_C_mul (a : ℚ) (P : ℚ[T;T⁻¹]) :
    endpointIntegral (1 / 2) 2 (C a * P) =
      a * endpointIntegral (1 / 2) 2 P := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem actual_base_endpoint_sources (p : ℕ) :
    reflectedDensity (baseDensity p) = endpointFKernel p - endpointGKernel p := by
  have h : baseDensity p = C 2 * originalAKernel p + originalBKernel p := by
    rw [baseDensity, Vpull_derivative_factors]
    unfold originalAKernel originalBKernel
    ring
  rw [h, map_add, reflectedDensity_C_mul]
  unfold endpointFKernel endpointGKernel
  ring

theorem actual_endpoint_period_difference (p : ℕ) :
    endpointFPeriod p - endpointGPeriod p = 9 * baseMoment p := by
  have h := congrArg (endpointIntegral (1 / 2) 2) (actual_base_endpoint_sources p)
  rw [reflectedDensity_integral, map_sub] at h
  unfold endpointFPeriod endpointGPeriod baseMoment
  linear_combination -(p : ℚ) * h

/-- Exact SB1 for the canonical pole period, before any digit selection. -/
theorem actual_polePeriod_coupled (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    polePeriod p ((p - 1) / 2) = fermatQ p 2 *
      ((1 + (fermatUnit p 2)⁻¹) * endpointFPeriod p - 9 * baseMoment p) := by
  let N := (p - 1) / 2
  have hsource : endpointDensity p N =
      C (2 * endpointA p N) * originalAKernel p +
        C (endpointB p N) * originalBKernel p := by
    unfold endpointDensity originalAKernel originalBKernel
    simp only [map_mul]
    ring
  have href : reflectedDensity (endpointDensity p N) =
      C (endpointA p N) * endpointFKernel p -
        C (endpointB p N) * endpointGKernel p := by
    rw [hsource, map_add, reflectedDensity_C_mul, reflectedDensity_C_mul]
    unfold endpointFKernel endpointGKernel
    rw [map_mul]
    ring
  have hI : (p : ℚ) * endpointIntegral (1 / 2) 2 (endpointDensity p N) =
      endpointA p N * endpointFPeriod p - endpointB p N * endpointGPeriod p := by
    rw [← reflectedDensity_integral, href, map_sub, integral_C_mul, integral_C_mul]
    unfold endpointFPeriod endpointGPeriod
    ring
  have hdiff := actual_endpoint_period_difference p
  have hcoeff := actual_endpoint_coefficients p hp
  change endpointA p N = _ ∧ endpointB p N = _ at hcoeff
  rw [hcoeff.1, hcoeff.2] at hI
  change (p : ℚ) * endpointIntegral (1 / 2) 2 (endpointDensity p N) = _
  linear_combination hI - fermatQ p 2 * hdiff

/-- The exact integer numerator for the base and its paired endpoint F-kernel. -/
noncomputable def integerF : ℤ[X] := 4 - Polynomial.X
noncomputable def integerG : ℤ[X] := 4 * Polynomial.X - 1
noncomputable def baseNumerator (p : ℕ) : ℤ[X] := integerF ^ (2 * p) * integerG ^ p
noncomputable def endpointNumerator (p : ℕ) : ℤ[X] :=
  integerF ^ (2 * p - 1) * integerG ^ p

noncomputable def rootPolynomial (P : ℤ[X]) : ℚ[T;T⁻¹] :=
  squareX (Polynomial.toLaurent (P.map (Int.castRingHom ℚ)))

theorem rootPolynomial_monomial (n : ℕ) (a : ℤ) :
    rootPolynomial (Polynomial.monomial n a) = C (a : ℚ) * T (2 * (n : ℤ)) := by
  rw [rootPolynomial, Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T,
    squareX_monomial]
  rfl

theorem rootPolynomial_mul (P Q : ℤ[X]) :
    rootPolynomial (P * Q) = rootPolynomial P * rootPolynomial Q := by
  simp only [rootPolynomial, Polynomial.map_mul, map_mul]

theorem rootPolynomial_pow (P : ℤ[X]) (n : ℕ) :
    rootPolynomial (P ^ n) = rootPolynomial P ^ n := by
  simp only [rootPolynomial, Polynomial.map_pow, map_pow]

theorem rootPolynomial_F : rootPolynomial integerF = 4 - T 2 := by
  rw [rootPolynomial, squareX_toLaurent]
  simp only [integerF, Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X,
    substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_X]

theorem rootPolynomial_G : rootPolynomial integerG = 4 * T 2 - 1 := by
  rw [rootPolynomial, squareX_toLaurent]
  simp only [integerG, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_one, substitute, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_ofNat,
    Polynomial.eval₂_X, Polynomial.eval₂_one]

theorem Qpull_integer_factors : Qpull =
    C (1 / 125) * rootPolynomial integerG * rootPolynomial integerF ^ 2 * T (-6) := by
  rw [rootPolynomial_F, rootPolynomial_G]
  rfl

theorem rootPolynomial_sum (P : ℤ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    rootPolynomial P = ∑ n ∈ Finset.range (d + 1), C (P.coeff n : ℚ) * T (2 * (n : ℤ)) := by
  conv_lhs => rw [Polynomial.as_sum_range' P (d + 1) (by omega)]
  simp only [rootPolynomial, Polynomial.map_sum, map_sum, Polynomial.map_monomial,
    Polynomial.toLaurent_C_mul_T, squareX_monomial, Int.coe_castRingHom]

theorem rootPolynomial_integral (p : ℕ) [Fact p.Prime] (P : ℤ[X]) :
    rootPolynomial P ∈ integralLaurent p := by
  rw [rootPolynomial_sum P P.natDegree le_rfl]
  apply (integralLaurent p).sum_mem
  intro n _hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (by rw [padicValRat.of_int]; exact Int.natCast_nonneg _))
    (integral_T p _)

theorem rootPolynomial_bounded (P : ℤ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    bounded (rootPolynomial P) 0 (2 * (d : ℤ)) := by
  rw [rootPolynomial_sum P d hd]
  apply bounded_sum
  intro n hn
  have hn' := Finset.mem_range.mp hn
  exact bounded_mono (bounded_monomial _ _) (by omega) (by omega)

/-- Every original finite coefficient is retained in this auxiliary source. -/
noncomputable def numeratorDensity (p : ℕ) (P : ℤ[X]) : ℚ[T;T⁻¹] :=
  C (1 / (125 : ℚ) ^ p) * rootPolynomial P * T (-5 * (p : ℤ) - 1)

noncomputable def numeratorPeriod (p : ℕ) (P : ℤ[X]) : ℚ :=
  rationalPrimitive p (numeratorDensity p P)

theorem numeratorDensity_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (P : ℤ[X]) :
    numeratorDensity p P ∈ integralLaurent p := by
  have hc : (1 / (125 : ℚ) ^ p) ∈ integralRationals p := by
    simpa only [one_div, inv_pow] using
      (integralRationals p).pow_mem (WPHasseIntegralTransport.one_over_125_integral p hp) p
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem (integral_C p _ hc) (rootPolynomial_integral p P))
    (integral_T p _)

theorem numeratorDensity_no_log (p : ℕ) (hp : Odd p) (P : ℤ[X]) :
    (numeratorDensity p P).coeff (-1) = 0 := by
  have hform : numeratorDensity p P =
      C (1 / (125 : ℚ) ^ p) * T (-5 * (p : ℤ) - 1) * rootPolynomial P := by
    unfold numeratorDensity
    ring
  rw [hform, WPFiniteCartier.coefficient_monomial_mul]
  have hz : -1 - (-5 * (p : ℤ) - 1) = 5 * (p : ℤ) := by ring
  rw [hz]
  have hodd : Odd (5 * (p : ℤ)) := by
    have hpz : Odd (p : ℤ) := by exact_mod_cast hp
    exact (show Odd (5 : ℤ) by decide).mul hpz
  rw [rootPolynomial, WPActualResonanceReduction.squareX_odd_coefficient _ _ hodd, mul_zero]

theorem numeratorDensity_primitive_bounds (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (hP : P.natDegree ≤ 3 * p) (j : ℤ)
    (hj : j ∈ (numeratorDensity p P).coeff.support) :
    j + 1 ≠ 0 ∧ (j + 1).natAbs < p ^ 2 := by
  have hne := Finsupp.mem_support_iff.mp hj
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hzero : j + 1 ≠ 0 := by
    intro hz
    have hj1 : j = -1 := by omega
    rw [hj1, numeratorDensity_no_log p hodd P] at hne
    exact hne rfl
  have hb := bounded_mul
    (bounded_mul (bounded_C (1 / (125 : ℚ) ^ p)) (rootPolynomial_bounded P (3 * p) hP))
    (bounded_T (-5 * (p : ℤ) - 1)) j hne
  have habs : (j + 1).natAbs ≤ 5 * p := by
    push_cast at hb
    omega
  exact ⟨hzero, habs.trans_lt (by nlinarith)⟩

theorem numeratorPeriod_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (hP : P.natDegree ≤ 3 * p) :
    0 ≤ padicValRat p (numeratorPeriod p P) := by
  exact WPActualResonanceReduction.rationalPrimitive_integral p (by omega) _
    (numeratorDensity_integral p (by omega) P)
    (fun j hj => (numeratorDensity_primitive_bounds p hp P hP j hj).1)
    (fun j hj => (numeratorDensity_primitive_bounds p hp P hP j hj).2)

theorem rationalPrimitive_sum (p : ℕ) {ι : Type*} (s : Finset ι)
    (P : ι → ℚ[T;T⁻¹]) :
    rationalPrimitive p (∑ i ∈ s, P i) = ∑ i ∈ s, rationalPrimitive p (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalPrimitive]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      WPActualResonanceReduction.rationalPrimitive_add, ih]

/-- Full finite Laurent coefficient formula, with the original signed primitive indices. -/
theorem numeratorPeriod_coefficient_formula (p : ℕ) (P : ℤ[X]) (d : ℕ)
    (hd : P.natDegree ≤ d) :
    numeratorPeriod p P = 1 / (125 : ℚ) ^ p *
      ∑ n ∈ Finset.range (d + 1), (P.coeff n : ℚ) *
        WPNativeMomentIntegrality.primitiveWeight p (2 * (n : ℤ) - 5 * (p : ℤ)) := by
  have hsource : numeratorDensity p P =
      ∑ n ∈ Finset.range (d + 1),
        C ((1 / (125 : ℚ) ^ p) * (P.coeff n : ℚ)) *
          T (2 * (n : ℤ) - 5 * (p : ℤ) - 1) := by
    rw [numeratorDensity, rootPolynomial_sum P d hd, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [show C (1 / (125 : ℚ) ^ p) * (C (P.coeff n : ℚ) * T (2 * (n : ℤ))) *
        T (-5 * (p : ℤ) - 1) =
      C ((1 / (125 : ℚ) ^ p) * (P.coeff n : ℚ)) *
        (T (2 * (n : ℤ)) * T (-5 * (p : ℤ) - 1)) by rw [map_mul]; ring,
      ← T_add]
    congr 2
    ring
  rw [numeratorPeriod, hsource, rationalPrimitive_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [WPActualResonanceReduction.rationalPrimitive_monomial,
    show 2 * (n : ℤ) - 5 * (p : ℤ) - 1 + 1 = 2 * (n : ℤ) - 5 * (p : ℤ) by omega]
  ring

theorem baseNumerator_degree (p : ℕ) : (baseNumerator p).natDegree ≤ 3 * p := by
  have hF : integerF.natDegree ≤ 1 := by unfold integerF; compute_degree
  have hG : integerG.natDegree ≤ 1 := by unfold integerG; compute_degree
  have hf := Polynomial.natDegree_pow_le_of_le (2 * p) hF
  have hg := Polynomial.natDegree_pow_le_of_le p hG
  have hm := Polynomial.natDegree_mul_le (p := integerF ^ (2 * p)) (q := integerG ^ p)
  unfold baseNumerator
  omega

theorem endpointNumerator_degree (p : ℕ) : (endpointNumerator p).natDegree ≤ 3 * p := by
  have hF : integerF.natDegree ≤ 1 := by unfold integerF; compute_degree
  have hG : integerG.natDegree ≤ 1 := by unfold integerG; compute_degree
  have hf := Polynomial.natDegree_pow_le_of_le (2 * p - 1) hF
  have hg := Polynomial.natDegree_pow_le_of_le p hG
  have hm := Polynomial.natDegree_mul_le (p := integerF ^ (2 * p - 1)) (q := integerG ^ p)
  unfold endpointNumerator
  omega

/-- The actual inverse base density equals its entire integer numerator source. -/
theorem actual_baseKernel_numerator (p : ℕ) :
    baseKernel p = numeratorDensity p (baseNumerator p) := by
  have hc : (C (1 / 125 : ℚ) : ℚ[T;T⁻¹]) ^ p = C (1 / (125 : ℚ) ^ p) := by
    rw [← map_pow]
    simp only [one_div, inv_pow]
  have ht : (T (-6) : ℚ[T;T⁻¹]) ^ p * T ((p : ℤ) - 1) =
      T (-5 * (p : ℤ) - 1) := by
    rw [T_pow, ← T_add]
    congr 1
    ring
  rw [baseKernel, Qpull_integer_factors]
  simp only [mul_pow]
  rw [← pow_mul, hc]
  unfold numeratorDensity baseNumerator
  rw [rootPolynomial_mul, rootPolynomial_pow, rootPolynomial_pow]
  calc
    _ = C (1 / (125 : ℚ) ^ p) * rootPolynomial integerF ^ (2 * p) *
        rootPolynomial integerG ^ p * (T (-6) ^ p * T ((p : ℤ) - 1)) := by ring
    _ = _ := by rw [ht]; ring

theorem actual_baseMoment_numerator (p : ℕ) (hp : 1 ≤ p) :
    baseMoment p = numeratorPeriod p (baseNumerator p) / 9 := by
  rw [actual_baseMoment_kernel p hp, actual_baseKernel_numerator,
    numeratorPeriod, WPActualResonanceReduction.rationalPrimitive_eq_endpointIntegral]
  ring

theorem actual_baseMoment_full_coefficients (p : ℕ) (hp : 1 ≤ p) :
    baseMoment p = 1 / (9 * (125 : ℚ) ^ p) *
      ∑ n ∈ Finset.range (3 * p + 1), ((baseNumerator p).coeff n : ℚ) *
        WPNativeMomentIntegrality.primitiveWeight p (2 * (n : ℤ) - 5 * (p : ℤ)) := by
  rw [actual_baseMoment_numerator p hp,
    numeratorPeriod_coefficient_formula p _ (3 * p) (baseNumerator_degree p)]
  ring

theorem actual_baseMoment_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (baseMoment p) := by
  rw [actual_baseMoment_numerator p (by omega)]
  have h3 : (1 / 3 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 3 (by omega) (by omega)
  have h9 : (1 / 9 : ℚ) ∈ integralRationals p := by
    simpa only [show (1 / 3 : ℚ) ^ 2 = 1 / 9 by norm_num] using
      (integralRationals p).pow_mem h3 2
  change numeratorPeriod p (baseNumerator p) / 9 ∈ integralRationals p
  rw [div_eq_mul_inv]
  exact (integralRationals p).mul_mem
    (numeratorPeriod_integral p hp _ (baseNumerator_degree p))
    (by simpa only [one_div] using h9)

theorem inverse_factorA : invert factorA =
    C (4 / 125) * rootPolynomial integerF * rootPolynomial integerG * T (-4) := by
  have ht : (T 2 : ℚ[T;T⁻¹]) * T (-2) = 1 := by rw [← T_add]; norm_num
  have hf : (4 * T (-2) - 1 : ℚ[T;T⁻¹]) = (4 - T 2) * T (-2) := by
    rw [sub_mul, ht]
  have hg : (4 - T (-2) : ℚ[T;T⁻¹]) = (4 * T 2 - 1) * T (-2) := by
    rw [sub_mul, mul_assoc, ht, mul_one, one_mul]
  have hpow : (T (-2) : ℚ[T;T⁻¹]) ^ 2 = T (-4) := by rw [T_pow]; norm_num
  simp only [factorA, map_mul, map_sub, map_ofNat, map_one, invert_C, invert_T]
  rw [hf, hg, rootPolynomial_F, rootPolynomial_G]
  calc
    _ = (C (4 / 125) * (4 - T 2) * (4 * T 2 - 1) * T (-2) ^ 2 :
        ℚ[T;T⁻¹]) := by ring
    _ = _ := by rw [hpow]

theorem inverse_factorB : invert factorB =
    C (-1 / 125) * rootPolynomial integerF ^ 2 * T (-4) := by
  have ht : (T 2 : ℚ[T;T⁻¹]) * T (-2) = 1 := by rw [← T_add]; norm_num
  have hf : (4 * T (-2) - 1 : ℚ[T;T⁻¹]) = (4 - T 2) * T (-2) := by
    rw [sub_mul, ht]
  have hpow : (T (-2) : ℚ[T;T⁻¹]) ^ 2 = T (-4) := by rw [T_pow]; norm_num
  simp only [factorB, map_mul, map_pow, map_sub, map_ofNat, map_one, invert_C, invert_T]
  rw [hf, rootPolynomial_F]
  calc
    _ = (C (-1 / 125) * (4 - T 2) ^ 2 * T (-2) ^ 2 : ℚ[T;T⁻¹]) := by ring
    _ = _ := by rw [hpow]

theorem endpointFKernel_normalform (p : ℕ) : endpointFKernel p =
    C (16 / 125) * Qpull ^ (p - 1) * rootPolynomial integerF *
      rootPolynomial integerG * T ((p : ℤ) - 7) := by
  have ht : (T (-2) * T (p : ℤ) * T (-1) * T (-4) : ℚ[T;T⁻¹]) =
      T ((p : ℤ) - 7) := by
    rw [← T_add, ← T_add, ← T_add]
    congr 1
    omega
  have hc : (C 2 * C 2 * C (4 / 125) : ℚ[T;T⁻¹]) = C (16 / 125) := by
    rw [← map_mul, ← map_mul]
    congr 1
    norm_num
  unfold endpointFKernel originalAKernel
  change C 2 * (T (-2) * invert
    (T (-(p : ℤ)) * Vpull ^ (p - 1) * C 2 * T 1 * factorA)) = _
  simp only [map_mul, map_pow, invert_T, neg_neg, invert_C,
    actual_Vpull_reciprocal, inverse_factorA]
  calc
    _ = (C 2 * C 2 * C (4 / 125)) * Qpull ^ (p - 1) *
        rootPolynomial integerF * rootPolynomial integerG *
          (T (-2) * T (p : ℤ) * T (-1) * T (-4)) := by ring
    _ = _ := by rw [hc, ht]

theorem endpointGKernel_normalform (p : ℕ) : endpointGKernel p =
    C (2 / 125) * Qpull ^ (p - 1) * rootPolynomial integerF ^ 2 *
      T ((p : ℤ) - 7) := by
  have ht : (T (-2) * T (p : ℤ) * T (-1) * T (-4) : ℚ[T;T⁻¹]) =
      T ((p : ℤ) - 7) := by
    rw [← T_add, ← T_add, ← T_add]
    congr 1
    omega
  have hc : (-C 2 * C (-1 / 125) : ℚ[T;T⁻¹]) = C (2 / 125) := by
    rw [← map_neg, ← map_mul]
    congr 1
    norm_num
  unfold endpointGKernel originalBKernel
  change -(T (-2) * invert
    (T (-(p : ℤ)) * Vpull ^ (p - 1) * C 2 * T 1 * factorB)) = _
  simp only [map_mul, map_pow, invert_T, neg_neg, invert_C,
    actual_Vpull_reciprocal, inverse_factorB]
  calc
    _ = (-C 2 * C (-1 / 125)) * Qpull ^ (p - 1) * rootPolynomial integerF ^ 2 *
        (T (-2) * T (p : ℤ) * T (-1) * T (-4)) := by ring
    _ = _ := by rw [hc, ht]

/-- The original endpoint F-kernel has the actual finite numerator F^(2p-1)G^p. -/
theorem actual_endpointFKernel_numerator (p : ℕ) (hp : 1 ≤ p) :
    endpointFKernel p = C 16 * numeratorDensity p (endpointNumerator p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hexp : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hc : (C (16 / 125) * C (1 / 125 : ℚ) ^ n : ℚ[T;T⁻¹]) =
      C 16 * C (1 / (125 : ℚ) ^ (n + 1)) := by
    rw [← map_pow, ← map_mul, ← map_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul, inv_pow, pow_succ, mul_inv_rev]
    ring
  have ht : (T (-6) : ℚ[T;T⁻¹]) ^ n * T (((n + 1 : ℕ) : ℤ) - 7) =
      T (-5 * (((n + 1 : ℕ) : ℤ)) - 1) := by
    rw [T_pow, ← T_add]
    congr 1
    push_cast
    ring
  rw [endpointFKernel_normalform, Nat.succ_sub_one, Qpull_integer_factors]
  simp only [mul_pow]
  rw [← pow_mul]
  unfold numeratorDensity endpointNumerator
  rw [rootPolynomial_mul, rootPolynomial_pow, rootPolynomial_pow, hexp,
    pow_succ (rootPolynomial integerF) (2 * n), pow_succ (rootPolynomial integerG) n]
  calc
    _ = (C (16 / 125) * C (1 / 125 : ℚ) ^ n) *
        (rootPolynomial integerF ^ (2 * n) * rootPolynomial integerF) *
        (rootPolynomial integerG ^ n * rootPolynomial integerG) *
        (T (-6) ^ n * T (((n + 1 : ℕ) : ℤ) - 7)) := by ring
    _ = _ := by rw [hc, ht]; ring

theorem actual_endpointFPeriod_numerator (p : ℕ) (hp : 1 ≤ p) :
    endpointFPeriod p = 16 * numeratorPeriod p (endpointNumerator p) := by
  rw [endpointFPeriod, actual_endpointFKernel_numerator p hp, integral_C_mul,
    numeratorPeriod, WPActualResonanceReduction.rationalPrimitive_eq_endpointIntegral]
  ring

theorem actual_endpointFPeriod_full_coefficients (p : ℕ) (hp : 1 ≤ p) :
    endpointFPeriod p = 16 / (125 : ℚ) ^ p *
      ∑ n ∈ Finset.range (3 * p + 1), ((endpointNumerator p).coeff n : ℚ) *
        WPNativeMomentIntegrality.primitiveWeight p (2 * (n : ℤ) - 5 * (p : ℤ)) := by
  rw [actual_endpointFPeriod_numerator p hp,
    numeratorPeriod_coefficient_formula p _ (3 * p) (endpointNumerator_degree p)]
  ring

theorem actual_endpointFPeriod_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (endpointFPeriod p) := by
  rw [actual_endpointFPeriod_numerator p (by omega)]
  exact (integralRationals p).mul_mem (natCast_mem _ 16)
    (numeratorPeriod_integral p hp _ (endpointNumerator_degree p))

theorem actual_polePeriod_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (polePeriod p ((p - 1) / 2)) := by
  rw [actual_polePeriod_coupled p hp]
  let R := integralRationals p
  have hQ : fermatQ p 2 ∈ R := by
    change 0 ≤ padicValRat p (fermatQ p 2)
    unfold fermatQ
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  have hu : (fermatUnit p 2)⁻¹ ∈ R := by
    change 0 ≤ padicValRat p ((fermatUnit p 2)⁻¹)
    rw [padicValRat.inv]
    unfold fermatUnit
    rw [padicValRat.pow]
    have htwo := WPNativeMomentIntegrality.two_zpow_unit p (by omega) 1
    norm_num only [zpow_one] at htwo
    norm_num only [Nat.cast_ofNat]
    rw [htwo]
    simp
  exact R.mul_mem hQ (R.sub_mem
    (R.mul_mem (R.add_mem R.one_mem hu) (actual_endpointFPeriod_integral p hp))
    (R.mul_mem (natCast_mem R 9) (actual_baseMoment_integral p hp)))

end WPMomentPrecision.BasePole
