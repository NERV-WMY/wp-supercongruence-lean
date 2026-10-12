import WPActualEtaPrimitive

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
open WPActualMomentDefect WPActualEtaPole WPActualEtaPrimitive

namespace WPActualEtaIntegration

private def doubleIndex : ℤ →+ ℤ where
  toFun j := 2 * j
  map_zero' := by ring
  map_add' := by intros; ring

/-- Complete rational Laurent substitution, including every negative power. -/
noncomputable def squareX : ℚ[T;T⁻¹] →+* ℚ[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainRingHom ℚ doubleIndex

theorem squareX_monomial (a : ℚ) (j : ℤ) :
    squareX (C a * T j) = C a * T (2 * j) := by
  simp [squareX, doubleIndex, ← LaurentPolynomial.single_eq_C_mul_T]

@[simp] theorem squareX_C (a : ℚ) : squareX (C a) = C a := by
  simpa using squareX_monomial a 0

@[simp] theorem squareX_T (j : ℤ) : squareX (T j) = T (2 * j) := by
  simpa using squareX_monomial 1 j

theorem squareX_substitute (P : ℚ[X]) (L : ℚ[T;T⁻¹]) :
    squareX (substitute P L) = substitute P (squareX L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hs (A B : ℚ[X]) (U : ℚ[T;T⁻¹]) : substitute (A + B) U =
        substitute A U + substitute B U := by simp only [substitute, map_add]
    rw [hs, hs, map_add, hP, hQ]
  | monomial n a => simp [substitute, Polynomial.eval₂_monomial]

theorem squareX_toLaurent (P : ℚ[X]) : squareX (Polynomial.toLaurent P) = substitute P (T 2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hs : substitute (P + Q) (T 2) = substitute P (T 2) + substitute Q (T 2) :=
      by simp only [substitute, map_add]
    rw [map_add, map_add, hs, hP, hQ]
  | monomial n a =>
    simp [substitute, ← Polynomial.C_mul_X_pow_eq_monomial]
    left
    congr 1
    ring

theorem squareX_derivative (P : ℚ[T;T⁻¹]) :
    derivative (squareX P) = C 2 * T 1 * squareX (derivative P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, map_add, mul_add, hP, hQ]
  | C_mul_T j a =>
    rw [squareX_monomial, derivative_monomial, derivative_monomial, squareX_monomial]
    have hindex : 1 + 2 * (j - 1) = 2 * j - 1 := by omega
    have hcoef : (a * ((2 * j : ℤ) : ℚ)) = 2 * (a * (j : ℚ)) := by push_cast; ring
    rw [hcoef, map_mul, show T (2 * j - 1) = T (1 + 2 * (j - 1)) by rw [hindex], T_add]
    ring

theorem squareX_Vx : squareX Vx = Vpull := squareX_toLaurent Vpolynomial

theorem squareX_Qx : squareX Qx = Qpull := by
  simp only [Qx, Qpull, Xpull, map_mul, map_sub, map_pow, map_ofNat, map_one,
    squareX_C, squareX_T, Int.reduceMul]

theorem squareX_Fpull (e : ℕ) (L : ℚ[T;T⁻¹]) :
    squareX (Fpull e L) = Fpull e (squareX L) := squareX_substitute _ _

theorem squareX_Hpull (e : ℕ) (L : ℚ[T;T⁻¹]) :
    squareX (Hpull e L) = Hpull e (squareX L) := squareX_substitute _ _

theorem squareX_chiX (p N e : ℕ) : squareX (chiX p N e) = chi p N e := by
  simp only [chiX, chi, map_mul, map_sub, squareX_C, squareX_T,
    squareX_Fpull, squareX_Vx, squareX_Qx]

theorem squareX_HX (e : ℕ) : squareX (HX e) = Hpull e Vpull := by
  rw [HX, squareX_Hpull, squareX_Vx]

theorem squareX_AX (p N e : ℕ) : squareX (AX p N e) = chi p N e + Hpull e Vpull := by
  rw [AX, map_add, squareX_chiX, squareX_HX]

noncomputable def actualCanonicalPullback (p N e : ℕ) : ℚ[T;T⁻¹] := squareX (Aeta p N e)

theorem actual_canonical_pullback_derivative (p N e : ℕ) :
    derivative (actualCanonicalPullback p N e) =
      C 2 * T 1 * squareX (Peta p N e - actualResonantSource p N e) := by
  rw [actualCanonicalPullback, squareX_derivative, actual_Aeta_derivative]

/-- The exact product derivative, before any integral or arithmetic reduction. -/
theorem actual_canonical_product_derivative (p N e : ℕ) (hp : 1 ≤ p) :
    derivative (Spull ^ p * actualCanonicalPullback p N e) =
      C (p : ℚ) * logarithmicSDensity p * actualCanonicalPullback p N e +
        Spull ^ p * C 2 * T 1 * squareX (Peta p N e - actualResonantSource p N e) := by
  rw [derivative_mul, derivative_Spull_power p hp, actual_canonical_pullback_derivative]
  ring

theorem actual_canonical_product_endpoints (p N e : ℕ) (hp : 1 ≤ p) :
    evaluate 2 (by norm_num) (Spull ^ p * actualCanonicalPullback p N e) = 0 ∧
      evaluate (1 / 2) (by norm_num) (Spull ^ p * actualCanonicalPullback p N e) = 0 := by
  have hleft : evaluate (1 / 2) (by norm_num) Spull = 0 := by
    rw [evaluate_Spull, evaluate_Vpull]; norm_num
  have hright : evaluate 2 (by norm_num) Spull = 0 := by
    rw [evaluate_Spull, evaluate_Vpull]; norm_num
  have hp0 : p ≠ 0 := by omega
  constructor
  · rw [map_mul, map_pow, hright, zero_pow hp0, zero_mul]
  · rw [map_mul, map_pow, hleft, zero_pow hp0, zero_mul]

theorem actual_canonical_integration_by_parts (p N e : ℕ) (hp : 1 ≤ p) :
    endpointIntegral (1 / 2) 2 (Spull ^ p * C 2 * T 1 * squareX (Peta p N e)) =
      endpointIntegral (1 / 2) 2 (Spull ^ p * C 2 * T 1 * squareX (actualResonantSource p N e)) -
        (p : ℚ) * endpointIntegral (1 / 2) 2
          (logarithmicSDensity p * actualCanonicalPullback p N e) := by
  have h := congrArg (endpointIntegral (1 / 2) 2) (actual_canonical_product_derivative p N e hp)
  rw [integral_derivative _ (1 / 2) 2 (by norm_num) (by norm_num),
    (actual_canonical_product_endpoints p N e hp).1,
    (actual_canonical_product_endpoints p N e hp).2, sub_self] at h
  have hs (a : ℚ) (L : ℚ[T;T⁻¹]) : endpointIntegral (1 / 2) 2 (C a * L) =
      a * endpointIntegral (1 / 2) 2 L := by rw [← smul_eq_C_mul, map_smul]; rfl
  simp only [map_sub, mul_sub, map_add] at h
  rw [show C (p : ℚ) * logarithmicSDensity p * actualCanonicalPullback p N e =
      C (p : ℚ) * (logarithmicSDensity p * actualCanonicalPullback p N e) by ring, hs] at h
  linear_combination -h

noncomputable def factorA : ℚ[T;T⁻¹] := C (4 / 125) * (4 * T 2 - 1) * (4 - T 2)
noncomputable def factorB : ℚ[T;T⁻¹] := C (-1 / 125) * (4 * T 2 - 1) ^ 2

theorem factorA_evaluate (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy factorA = 4 / 125 * (4 * y ^ 2 - 1) * (4 - y ^ 2) := by
  have hT : evaluate y hy (T 2) = y ^ (2 : ℕ) := by simpa using evaluate_monomial 2 1 y hy
  simp only [factorA, map_mul, map_sub, map_ofNat, map_one, evaluate_C, hT]

theorem factorB_evaluate (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy factorB = -1 / 125 * (4 * y ^ 2 - 1) ^ 2 := by
  have hT : evaluate y hy (T 2) = y ^ (2 : ℕ) := by simpa using evaluate_monomial 2 1 y hy
  simp only [factorB, map_mul, map_sub, map_pow, map_ofNat, map_one, evaluate_C, hT]

theorem Vpull_factorA : Vpull = (T 2 - C (1 / 4)) * factorA := by
  apply ext_positive_integers
  intro j
  let y : ℚ := (j : ℚ) + 3
  have hy : y ≠ 0 := by dsimp [y]; positivity
  have hT : evaluate y hy (T 2) = y ^ (2 : ℕ) := by simpa using evaluate_monomial 2 1 y hy
  change evaluate y hy _ = evaluate y hy _
  rw [evaluate_Vpull, map_mul, map_sub, hT, evaluate_C, factorA_evaluate]
  ring

theorem Vpull_factorB : Vpull = (T 2 - C 4) * factorB := by
  apply ext_positive_integers
  intro j
  let y : ℚ := (j : ℚ) + 3
  have hy : y ≠ 0 := by dsimp [y]; positivity
  have hT : evaluate y hy (T 2) = y ^ (2 : ℕ) := by simpa using evaluate_monomial 2 1 y hy
  change evaluate y hy _ = evaluate y hy _
  rw [evaluate_Vpull, map_mul, map_sub, hT, evaluate_C, factorB_evaluate]
  ring

theorem Vpull_derivative_factors : derivative Vpull = C 2 * T 1 * (C 2 * factorA + factorB) := by
  apply ext_positive_integers
  intro j
  let y : ℚ := (j : ℚ) + 3
  have hy : y ≠ 0 := by dsimp [y]; positivity
  have hT : evaluate y hy (T 1) = y := by simpa using evaluate_monomial 1 1 y hy
  change evaluate y hy _ = evaluate y hy _
  rw [evaluate_derivative_Vpull]
  simp only [map_mul, map_add, evaluate_C, hT, factorA_evaluate, factorB_evaluate]
  ring

noncomputable def endpointA (p N : ℕ) : ℚ := (1 - (1 / 4 : ℚ) ^ N) / p
noncomputable def endpointB (p N : ℕ) : ℚ := (1 - (4 : ℚ) ^ N) / p

/-- Both original endpoint poles multiplied by S^p and canceled exactly. -/
noncomputable def endpointDensity (p N : ℕ) : ℚ[T;T⁻¹] :=
  T (-(p : ℤ)) * Vpull ^ (p - 1) * C 2 * T 1 *
    (C (2 * endpointA p N) * factorA + C (endpointB p N) * factorB)

theorem actual_Peta_weighted_source (p N e : ℕ) (hp : 1 ≤ p) :
    Spull ^ p * C 2 * T 1 * squareX (Peta p N e) =
      weightedEta p N e - endpointDensity p N := by
  have hda := congrArg squareX (dividedDifference_identity (1 / 4) (by norm_num) (AX p N e))
  have hdb := congrArg squareX (dividedDifference_identity 4 (by norm_num) (AX p N e))
  rw [(actual_AX_endpoints p N e).1] at hda
  rw [(actual_AX_endpoints p N e).2] at hdb
  simp only [map_mul, map_sub, squareX_T, squareX_C, squareX_AX, Int.reduceMul] at hda hdb
  have hVa : Vpull * squareX (dividedDifference (1 / 4) (AX p N e)) =
      factorA * (chi p N e + Hpull e Vpull - C (endpointA p N)) := by
    conv_lhs => rw [Vpull_factorA]
    calc
      _ = factorA * ((T 2 - C (1 / 4)) * squareX (dividedDifference (1 / 4) (AX p N e))) := by ring
      _ = _ := by rw [hda]; rfl
  have hVb : Vpull * squareX (dividedDifference 4 (AX p N e)) =
      factorB * (chi p N e + Hpull e Vpull - C (endpointB p N)) := by
    conv_lhs => rw [Vpull_factorB]
    calc
      _ = factorB * ((T 2 - C 4) * squareX (dividedDifference 4 (AX p N e))) := by ring
      _ = _ := by rw [hdb]; rfl
  have hVp : Vpull ^ p = Vpull ^ (p - 1) * Vpull := by
    rw [← pow_succ]
    congr 1
    omega
  have hP : Vpull * squareX (Peta p N e) =
      C 2 * factorA * (chi p N e + Hpull e Vpull - C (endpointA p N)) +
        factorB * (chi p N e + Hpull e Vpull - C (endpointB p N)) -
          C (1 / 2) * Vpull * Hpull e Vpull * T (-2) := by
    simp only [Peta, map_sub, map_add, map_mul, squareX_C, squareX_HX, squareX_T, Int.reduceMul]
    linear_combination C 2 * hVa + hVb
  have hhalf : (C 2 * C (1 / 2) : ℚ[T;T⁻¹]) = 1 := by rw [← map_mul]; norm_num
  have hcancel : C 2 * T 1 * (C (1 / 2) * Vpull * Hpull e Vpull * T (-2)) =
      Vpull * Hpull e Vpull * T (-1) := by
    calc
      _ = (C 2 * C (1 / 2)) * Vpull * Hpull e Vpull * (T 1 * T (-2)) := by ring
      _ = _ := by rw [hhalf, ← T_add]; norm_num
  rw [Spull_power, hVp]
  calc
    _ = T (-(p : ℤ)) * Vpull ^ (p - 1) * (C 2 * T 1 * (Vpull * squareX (Peta p N e))) := by ring
    _ = _ := by
      rw [hP, mul_sub, hcancel]
      unfold weightedEta logarithmicSDensity baseDensity endpointDensity
      rw [hVp, Vpull_derivative_factors]
      simp only [map_mul]
      have hT : (T (-(p : ℤ) - 1) : ℚ[T;T⁻¹]) = T (-(p : ℤ)) * T (-1) := by
        rw [← T_add]
        congr 1
      rw [hT]
      ring

noncomputable def polePeriod (p N : ℕ) : ℚ :=
  (p : ℚ) * endpointIntegral (1 / 2) 2 (endpointDensity p N)

noncomputable def canonicalPeriod (p N e : ℕ) : ℚ :=
  (p : ℚ) * endpointIntegral (1 / 2) 2
    (logarithmicSDensity p * actualCanonicalPullback p N e)

/-- The exact signed resonant source, with no coefficient window removed. -/
noncomputable def resonancePeriod (p : ℕ) (k : ℤ) : ℚ :=
  (p : ℚ) * endpointIntegral (1 / 2) 2
    (Spull ^ p * C 2 * T 1 * T (2 * (k * (p : ℤ) - 1)))

private theorem integral_C_mul (a : ℚ) (L : ℚ[T;T⁻¹]) :
    endpointIntegral (1 / 2) 2 (C a * L) = a * endpointIntegral (1 / 2) 2 L := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem actual_resonant_period_decomposition (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (p : ℚ) * endpointIntegral (1 / 2) 2
      (Spull ^ p * C 2 * T 1 * squareX
        (actualResonantSource p ((p - 1) / 2) (p - 1 - p / 6))) =
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) * resonancePeriod p (-1) +
        actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 * resonancePeriod p 0 +
        actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 1 * resonancePeriod p 1 +
        actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 2 * resonancePeriod p 2 := by
  rw [actual_cutoff_resonant_decomposition p hp]
  simp only [map_add, squareX_monomial, mul_add, map_add]
  have hs (a : ℚ) (j : ℤ) : endpointIntegral (1 / 2) 2
      (Spull ^ p * C 2 * T 1 * (C a * T j)) =
        a * endpointIntegral (1 / 2) 2 (Spull ^ p * C 2 * T 1 * T j) := by
    rw [show Spull ^ p * C 2 * T 1 * (C a * T j) =
      C a * (Spull ^ p * C 2 * T 1 * T j) by ring, integral_C_mul]
  simp only [hs, resonancePeriod, neg_one_mul, zero_mul, one_mul, zero_sub]
  ring

/-- NC63 for the original full eta, with all four actual canonical resonance coefficients. -/
theorem actual_NC63_period_decomposition (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    etaPeriod p ((p - 1) / 2) (p - 1 - p / 6) = polePeriod p ((p - 1) / 2) +
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) * resonancePeriod p (-1) +
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 * resonancePeriod p 0 +
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 1 * resonancePeriod p 1 +
      actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 2 * resonancePeriod p 2 -
        (p : ℚ) * canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) := by
  let N := (p - 1) / 2
  let e := p - 1 - p / 6
  have hsource := actual_Peta_weighted_source p N e (by omega)
  have hw : weightedEta p N e = endpointDensity p N +
      Spull ^ p * C 2 * T 1 * squareX (Peta p N e) := by linear_combination -hsource
  change etaPeriod p N e = _
  rw [etaPeriod, etaIntegral, hw, map_add, actual_canonical_integration_by_parts p N e (by omega)]
  have hr := actual_resonant_period_decomposition p hp
  change (p : ℚ) * endpointIntegral (1 / 2) 2
    (Spull ^ p * C 2 * T 1 * squareX (actualResonantSource p N e)) = _ at hr
  unfold polePeriod canonicalPeriod
  linear_combination hr

theorem Spull_power_endpoints (p : ℕ) (hp : 1 ≤ p) :
    evaluate 2 (by norm_num) (Spull ^ p) = 0 ∧
      evaluate (1 / 2) (by norm_num) (Spull ^ p) = 0 := by
  have hp0 : p ≠ 0 := by omega
  constructor
  · rw [map_pow, evaluate_Spull, evaluate_Vpull]
    norm_num [zero_pow hp0]
  · rw [map_pow, evaluate_Spull, evaluate_Vpull]
    norm_num [zero_pow hp0]

theorem logarithmicSDensity_zero_integral (p : ℕ) (hp : 1 ≤ p) :
    endpointIntegral (1 / 2) 2 (logarithmicSDensity p) = 0 := by
  have h : endpointIntegral (1 / 2) 2 (derivative (Spull ^ p)) = 0 := by
    rw [integral_derivative _ (1 / 2) 2 (by norm_num) (by norm_num),
      (Spull_power_endpoints p hp).1, (Spull_power_endpoints p hp).2, sub_self]
  rw [derivative_Spull_power p hp, integral_C_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by positivity : (p : ℚ) ≠ 0)

theorem resonance_zero_base_moment (p : ℕ) (hp : 1 ≤ p) :
    resonancePeriod p 0 = 18 * baseMoment p := by
  have hT : (T (-(p : ℤ)) * T 1 * T (-2) : ℚ[T;T⁻¹]) = T (-(p : ℤ) - 1) := by
    rw [← T_add, ← T_add]
    congr 1
    omega
  have hsource : Spull ^ p * C 2 * T 1 * T (-2) =
      C 2 * (Vpull ^ p * T (-(p : ℤ) - 1)) := by
    rw [Spull_power]
    calc
      _ = C 2 * Vpull ^ p * (T (-(p : ℤ)) * T 1 * T (-2)) := by ring
      _ = _ := by rw [hT]; ring
  have hL : endpointIntegral (1 / 2) 2 (baseDensity p) =
      endpointIntegral (1 / 2) 2 (Vpull ^ p * T (-(p : ℤ) - 1)) := by
    have h := logarithmicSDensity_zero_integral p hp
    rw [logarithmicSDensity, map_sub] at h
    linear_combination h
  unfold resonancePeriod
  norm_num only [zero_mul, zero_sub, Int.reduceMul]
  rw [hsource, integral_C_mul, ← hL]
  unfold baseMoment
  ring

/-- Original NC64, before replacing any actual resonance coefficient by a first digit. -/
theorem actual_NC64_short_moment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualShortMoment p (p - 1 - p / 6) =
      (1 - 2 * (p : ℚ) * actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0) * baseMoment p -
      (p : ℚ) / 9 * polePeriod p ((p - 1) / 2) -
      (p : ℚ) / 9 *
        (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1) * resonancePeriod p (-1) +
          actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 1 * resonancePeriod p 1 +
          actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 2 * resonancePeriod p 2) +
        (p : ℚ) ^ 2 / 9 * canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hN : p = 2 * ((p - 1) / 2) + 1 := by obtain ⟨k, hk⟩ := hodd; omega
  rw [actual_short_moment_period_decomposition p ((p - 1) / 2) _ (by omega) hN,
    actual_NC63_period_decomposition p hp, resonance_zero_base_moment p (by omega)]
  ring

end WPActualEtaIntegration
