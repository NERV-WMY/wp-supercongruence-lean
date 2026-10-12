import WPFieldAssembly.NativeChiCovariance
import WPFieldAssembly.NativeQuadraticInverse
import WPLaurentIntegralResidue

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential
  WPActualChiSource WPActualEtaIntegrality WPLaurentIntegralResidue
  WPPIntegralReduction WPHasseIntegralTransport WPActualEtaPole
  WPActualPullbackSource WPHasseCubicSource
  WPFieldAssembly.NativeChiCovariance
  WPFieldAssembly.NativeQuadraticInverse

namespace WPFieldAssembly.NativeChiResidue

set_option maxHeartbeats 1000000

theorem integral_D (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    D P ∈ integralLaurent p := by
  intro j
  rw [D_coeff]
  exact (integralRationals p).mul_mem
    (intCast_mem (integralRationals p) (j + 1)) (hP (j + 1))

theorem integral_invert (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    invert P ∈ integralLaurent p := by
  intro j
  rw [invert_apply]
  exact hP (-j)

theorem integral_toLaurent_derivative (p : ℕ) [Fact p.Prime]
    (P : ℚ[X]) (hP : P.toLaurent ∈ integralLaurent p) :
    P.derivative.toLaurent ∈ integralLaurent p := by
  rw [← D_toLaurent]
  exact integral_D p _ hP

theorem covariance_coefficients_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    c2.toLaurent ∈ integralLaurent p ∧ c1.toLaurent ∈ integralLaurent p ∧
    c0.toLaurent ∈ integralLaurent p ∧ r0 ∈ integralLaurent p ∧
    r1 ∈ integralLaurent p ∧ metric ∈ integralLaurent p := by
  let R := integralRationals p
  let L := integralLaurent p
  have hx : (T 1 : ℚ[T;T⁻¹]) ∈ L := integral_T p 1
  have h125 : (1 / 125 : ℚ) ∈ R := one_over_125_integral p hp
  have h4125 : (4 / 125 : ℚ) ∈ R := by
    convert R.mul_mem (natCast_mem R 4) h125 using 1; norm_num
  have h2125 : (2 / 125 : ℚ) ∈ R := by
    convert R.mul_mem (natCast_mem R 2) h125 using 1; norm_num
  have h25 : (1 / 25 : ℚ) ∈ R := by
    convert R.mul_mem (natCast_mem R 5) h125 using 1; norm_num
  have hhalf : (1 / 2 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hquarter : (1 / 4 : ℚ) ∈ R := by
    simpa only [show (1 / 2 : ℚ) ^ 2 = 1 / 4 by norm_num] using R.pow_mem hhalf 2
  have hd : (cubicDiscriminant : ℚ[X]).toLaurent ∈ L := by
    simp only [cubicDiscriminant, map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X, map_one]
    exact L.mul_mem (L.sub_mem (natCast_mem L 4) hx)
      (L.sub_mem (L.mul_mem (natCast_mem L 4) hx) L.one_mem)
  have hn : (cubicNumerator : ℚ[X]).toLaurent ∈ L := by
    simp only [cubicNumerator, map_mul, map_pow, map_sub, map_ofNat, Polynomial.toLaurent_X, map_one]
    exact L.mul_mem
      (L.pow_mem (L.sub_mem (L.mul_mem (natCast_mem L 4) hx) L.one_mem) 2)
      (L.sub_mem (natCast_mem L 4) hx)
  have hc2 : c2.toLaurent ∈ L := by
    simp only [c2, map_mul, map_pow, map_add, Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_one]
    exact L.mul_mem (L.mul_mem (integral_C p _ h4125) (L.add_mem hx L.one_mem)) (L.pow_mem hd 2)
  have hc1 : c1.toLaurent ∈ L := by
    simp only [c1, map_add, map_mul, map_pow, map_sub, map_ofNat,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_one]
    exact L.add_mem (L.mul_mem (integral_C p _ h2125) (L.pow_mem hd 2))
      (L.mul_mem (L.mul_mem (L.mul_mem (integral_C p _ h4125) (L.add_mem hx L.one_mem)) hd)
        (L.sub_mem (natCast_mem L 17) (L.mul_mem (natCast_mem L 8) hx)))
  have hc0 : c0.toLaurent ∈ L := by
    simp only [c0, map_mul, map_neg, Polynomial.toLaurent_C]
    exact L.mul_mem (L.neg_mem (integral_C p _ h25)) hn
  refine ⟨hc2, hc1, hc0, ?_, ?_, ?_⟩
  · exact L.mul_mem (integral_C p _ hhalf)
      (L.sub_mem (L.mul_mem (integral_T p (-1)) hc1)
        (L.mul_mem (L.pow_mem (integral_T p (-1)) 2) hc2))
  · exact L.mul_mem (L.mul_mem (integral_C p _ hhalf) (integral_T p (-1))) hc2
  · exact L.mul_mem (L.mul_mem (integral_C p _ hquarter) (L.pow_mem (integral_T p (-1)) 2)) hc2

theorem concomitant_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    {f g : ℚ[T;T⁻¹]} (hf : f ∈ integralLaurent p) (hg : g ∈ integralLaurent p) :
    concomitant f g ∈ integralLaurent p := by
  let L := integralLaurent p
  obtain ⟨hc2, hc1, hc0, _, _, _⟩ := covariance_coefficients_integral p hp
  have hDf := integral_D p f hf
  have hDg := integral_D p g hg
  have hDDf := integral_D p (D f) hDf
  have hDDg := integral_D p (D g) hDg
  exact L.add_mem
    (L.add_mem
      (L.mul_mem hc2 (L.sub_mem (L.add_mem (L.mul_mem hf hDDg) (L.mul_mem hg hDDf))
        (L.mul_mem hDf hDg)))
      (L.mul_mem hc1 (L.add_mem (L.mul_mem hf hDg) (L.mul_mem hg hDf))))
    (L.mul_mem (L.mul_mem hc0 hf) hg)

theorem forcing_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    {f : ℚ[T;T⁻¹]} (hf : f ∈ integralLaurent p) : forcing f ∈ integralLaurent p := by
  let L := integralLaurent p
  obtain ⟨_, _, _, hr0, hr1, _⟩ := covariance_coefficients_integral p hp
  exact L.add_mem (L.mul_mem hr0 (L.pow_mem hf 2))
    (L.mul_mem (L.mul_mem hr1 hf) (integral_D p f hf))

theorem forcingCross_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    {f g : ℚ[T;T⁻¹]} (hf : f ∈ integralLaurent p) (hg : g ∈ integralLaurent p) :
    forcingCross f g ∈ integralLaurent p := by
  let L := integralLaurent p
  obtain ⟨_, _, _, hr0, hr1, _⟩ := covariance_coefficients_integral p hp
  exact L.add_mem (L.mul_mem (L.mul_mem (L.mul_mem (natCast_mem L 2) hr0) hf) hg)
    (L.mul_mem hr1 (L.add_mem (L.mul_mem hf (integral_D p g hg))
      (L.mul_mem hg (integral_D p f hf))))

theorem actual_Fpull_integral (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (he : e < p) :
    Fpull e Vx ∈ integralLaurent p := by
  have h := coefficientMap_subtype_integral p
    (((nativeIntegral p e hp he).comp (integralV p hp)).toLaurent)
  rw [coefficientMap_toLaurent, Polynomial.map_comp, nativeIntegral_map_rational,
    integralV_map_rational, ← Fpull_toLaurent] at h
  exact h

theorem actual_half_self_concomitant_quotient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    ∃ K : integralLaurent p, concomitant (Fpull N Vx) (Fpull N Vx) = C ((p : ℚ) ^ 2) * K.val := by
  let N := (p - 1) / 2
  let f := Fpull N Vx
  change ∃ K : integralLaurent p, concomitant f f = C ((p : ℚ) ^ 2) * K.val
  have hp7 : 7 ≤ p := by omega
  have hpq : (p : ℚ) ≠ 0 := by positivity
  obtain ⟨H, hH⟩ := actual_nativeH_divided_two_witness p hp
  let U := (H.comp (integralV p hp7)).toLaurent
  let Kraw := coefficientMap (integralRationals p).subtype U
  have hKi : Kraw ∈ integralLaurent p := coefficientMap_subtype_integral p U
  have hK : Kraw = C (1 / (p : ℚ) ^ 2) * concomitant f f := by
    change coefficientMap (integralRationals p).subtype
      ((H.comp (integralV p hp7)).toLaurent) = _
    rw [coefficientMap_toLaurent, Polynomial.map_comp, integralV_map_rational, hH,
      Polynomial.mul_comp, Polynomial.C_comp, map_mul, Polynomial.toLaurent_C]
    congr 1
    simpa only [nativeH, f, Fpull_toLaurent, N] using
      (self_native_pullback (WPReview.nativePolynomial (N + 1))).symm
  refine ⟨⟨Kraw, hKi⟩, ?_⟩
  change concomitant f f = C ((p : ℚ) ^ 2) * Kraw
  rw [hK, ← mul_assoc, ← map_mul, mul_one_div_cancel (pow_ne_zero 2 hpq), map_one, one_mul]

theorem actual_half_covariance_remainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    let f := Fpull N Vx
    let χ := chiX p N N
    let w := T (N : ℤ) * Fpull N Qx
    concomitant χ χ + 2 * forcingCross f χ - C (2 * (p : ℚ)) * forcing χ + metric * w ^ 2
      ∈ integralLaurent p := by
  let N := (p - 1) / 2
  let f := Fpull N Vx
  let χ := chiX p N N
  let w := T (N : ℤ) * Fpull N Qx
  let R := integralRationals p
  let L := integralLaurent p
  change concomitant χ χ + 2 * forcingCross f χ - C (2 * (p : ℚ)) * forcing χ + metric * w ^ 2 ∈ L
  have hp7 : 7 ≤ p := by omega
  have he : N < p := by dsimp [N]; omega
  have hd : p / 6 ≤ N := by dsimp [N]; omega
  have hf : f ∈ L := actual_Fpull_integral p N hp7 he
  have hχ : χ ∈ L := actual_chiX_integral p N hp7 he hd
  have hq : Fpull N Qx ∈ L := by
    rw [← Fpull_reciprocal]
    exact integral_invert p _ hf
  have hw : w ∈ L := L.mul_mem (integral_T p _) hq
  obtain ⟨_, _, _, _, _, hm⟩ := covariance_coefficients_integral p hp7
  have hCp : C (2 * (p : ℚ)) ∈ L :=
    integral_C p _ (R.mul_mem (natCast_mem R 2) (natCast_mem R p))
  exact L.add_mem (L.sub_mem
    (L.add_mem (concomitant_integral p hp7 hχ hχ)
      (L.mul_mem (natCast_mem L 2) (forcingCross_integral p hp7 hf hχ)))
    (L.mul_mem hCp (forcing_integral p hp7 hχ))) (L.mul_mem hm (L.pow_mem hw 2))

/-- Cancellation precedes reduction and uses the unchanged literal half-cutoff chi. -/
theorem actual_half_chi_source_residueZero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    residueZero p (concomitant (Fpull N Vx) (chiX p N N) + forcing (Fpull N Vx)) := by
  let N := (p - 1) / 2
  let f := Fpull N Vx
  let χ := chiX p N N
  let w := T (N : ℤ) * Fpull N Qx
  let E := concomitant χ χ + 2 * forcingCross f χ - C (2 * (p : ℚ)) * forcing χ + metric * w ^ 2
  let S := concomitant f χ + forcing f
  let R := integralRationals p
  let L := integralLaurent p
  change residueZero p S
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have h2p : 2 * (p : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hpq
  obtain ⟨K, hK⟩ := actual_half_self_concomitant_quotient p hp
  change concomitant f f = C ((p : ℚ) ^ 2) * K.val at hK
  let J := K.val - T (p : ℤ) * invert K.val + E
  have hEi : E ∈ L := actual_half_covariance_remainder_integral p hp
  have hJi : J ∈ L := L.add_mem
    (L.sub_mem K.property (L.mul_mem (integral_T p _) (integral_invert p K.val K.property))) hEi
  have hcov : C (2 * (p : ℚ)) * S = C ((p : ℚ) ^ 2) * J := by
    have hc := actual_chi_concomitant_cleared p N N hpq (WPFiniteWSource.half_exponent p hp)
    change C (2 * (p : ℚ)) * S = concomitant f f - T (p : ℤ) * invert (concomitant f f) +
      C ((p : ℚ) ^ 2) * E at hc
    rw [hK] at hc
    simp only [map_mul, invert_C] at hc
    calc
      C (2 * (p : ℚ)) * S = C ((p : ℚ) ^ 2) * K.val -
          T (p : ℤ) * (C ((p : ℚ) ^ 2) * invert K.val) + C ((p : ℚ) ^ 2) * E := by
            simpa only [map_mul, mul_assoc] using hc
      _ = C ((p : ℚ) ^ 2) * J := by dsimp [J]; ring
  have hcancel : (C (1 / (2 * (p : ℚ))) : ℚ[T;T⁻¹]) * C (2 * (p : ℚ)) = 1 := by
    rw [mul_comm, ← map_mul, mul_one_div_cancel h2p, map_one]
  have hscale : (C (1 / (2 * (p : ℚ))) : ℚ[T;T⁻¹]) * C ((p : ℚ) ^ 2) = C ((p : ℚ) / 2) := by
    rw [← map_mul]
    congr 1
    field_simp [hpq]
  have hS : S = C ((p : ℚ) / 2) * J := by
    calc
      S = C (1 / (2 * (p : ℚ))) * (C (2 * (p : ℚ)) * S) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ = C (1 / (2 * (p : ℚ))) * (C ((p : ℚ) ^ 2) * J) := by rw [hcov]
      _ = (C (1 / (2 * (p : ℚ))) * C ((p : ℚ) ^ 2)) * J := by ring
      _ = C ((p : ℚ) / 2) * J := by rw [hscale]
  have hhalf : (1 / 2 : ℚ) ∈ R :=
    WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hscalar : residueZero p (C ((p : ℚ) / 2)) := by
    have hz := residueZero_mul_integral p
      (residueZero_C p (p : ℚ) (natCast_mem R p) (by simp)) (integral_C p (1 / 2) hhalf)
    simpa only [← map_mul, show (p : ℚ) * (1 / 2) = (p : ℚ) / 2 by ring] using hz
  rw [hS]
  exact residueZero_mul_integral p hscalar hJi

end WPFieldAssembly.NativeChiResidue
