import WPLiteralAdapter.EndpointPrecision
import WPOriginalConductorMoment

open scoped BigOperators
open WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

/-- The honest full moment retains every literal index n<p. -/
def fullActualMoment (p : ℕ) : ℚ :=
  ∑ n∈Finset.range p, WPReview.nativeCoefficient n*
    WPNativeMomentIntegrality.actualMonomialMoment p n

private theorem congruent_iff_precisionZero (p k : ℕ) (a b : ℚ) :
    WPReview.RationalCongruent p k a b ↔ precisionZero p k (a-b) := by
  simp only [WPReview.RationalCongruent, precisionZero, sub_eq_zero]

theorem actual_extended_gamma_valuation (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    padicValRat p (WPReview.gamma (3*p-1))=-1 := by
  have hq₁ : (3*p-1)/p=2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq₂ : (2*(3*p-1)+1)/p=5 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [WPReview.gamma_valuation_formula p (3*p-1) Fact.out (by omega) le_rfl, hq₁, hq₂]
  norm_num

/-- The restoring 3p factor is included before the upper endpoint is removed. -/
theorem actual_literal_upper_endpoint_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    precisionZero p 6 (6750*(3*(p : ℚ))*WPReview.gamma (3*p-1)*
      actualRationalCoefficient (actualTotalPrimitive p) ((3*p : ℕ) : ℤ)) := by
  let R := integralSubring p
  have hpq : (p : ℚ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hg : WPReview.gamma (3*p-1)≠0 := by
    rw [WPReview.gamma_helper_eq]
    exact WPGammaArithmetic.gamma_ne_zero _
  have hpg : (p : ℚ)*WPReview.gamma (3*p-1)∈R := by
    change 0≤padicValRat p ((p : ℚ)*WPReview.gamma (3*p-1))
    rw [padicValRat.mul hpq hg, padicValRat.self (Fact.out : p.Prime).one_lt,
      actual_extended_gamma_valuation p hp]
    norm_num
  have hu : (20250 : ℚ)*((p : ℚ)*WPReview.gamma (3*p-1))∈R :=
    R.mul_mem (natCast_mem R 20250) hpg
  convert precisionZero_mul_integral p 6 _ _
    (actual_total_primitive_endpoint_precision p hp) hu using 1
  ring

/-- Actual Beta Gamma agrees with the full actual moment at precision five. -/
theorem actual_beta_gamma_full_moment_precision
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    precisionZero p 5 (WPReview.nativeEndpoint p*WPReview.Gamma (3*p-1)
      (fun k => actualRationalCoefficient (actualBetaFunctional p) k)-
      (p : ℚ)^2*WPReview.nativeCoefficient p*fullActualMoment p) := by
  let R := integralSubring p
  let C : ℚ := ∑ n∈Finset.range (p-1-p/6+1), WPReview.nativeCoefficient n*
    WPNativeMomentIntegrality.actualMonomialMoment p n
  let Q : ℚ := WPReview.Gamma (3*p-1) (fun k => (Be p (p-1-p/6)).coeff k)
  let K : ℚ := (p : ℚ)^2*WPReview.nativeCoefficient p
  have hβ : precisionZero p 5 (WPReview.nativeEndpoint p*WPReview.Gamma (3*p-1)
      (fun k => actualRationalCoefficient (actualBetaFunctional p) k)-
      WPReview.nativeEndpoint p*Q) := by
    apply (congruent_iff_precisionZero p 5 _ _).mp
    simpa only [actual_beta_full_natural_coefficient p (by omega)] using
      actual_full_short_conductor_Gamma_precision p hp
  have hQ : (p : ℚ)*Q=C :=
    WPOriginalConductorMoment.original_p_Gamma_eq_native_cutoff p hp
  have hA : WPReview.nativeEndpoint p*Q=K*C := by
    rw [WPReview.nativeEndpoint_eq p (by omega)]
    calc
      (p : ℚ)^3*WPReview.nativeCoefficient p*Q=K*((p : ℚ)*Q) := by dsimp only [K]; ring
      _=K*C := by rw [hQ]
  have hcut : precisionZero p 3 (fullActualMoment p-C) := by
    rcases WPNativeMomentIntegrality.actual_full_literal_cutoff_moment_precision
        p (by omega) with h | h
    · exact Or.inl (sub_eq_zero.mpr h)
    · exact Or.inr h
  have hcut' : precisionZero p 3 (C-fullActualMoment p) := by
    convert precisionZero_neg p 3 (fullActualMoment p-C) hcut using 1
    ring
  have hcp : WPReview.nativeCoefficient p∈R := by
    change 0≤padicValRat p (WPReview.nativeCoefficient p)
    rw [native_coefficient_at_prime_valuation p (by omega)]
  have hp₂ : precisionZero p 2 ((p : ℚ)^2) := by
    apply Or.inr
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hK : precisionZero p 2 K := precisionZero_mul_integral p 2 _ _ hp₂ hcp
  have htail : precisionZero p 5 (WPReview.nativeEndpoint p*Q-K*fullActualMoment p) := by
    rw [hA]
    convert precisionZero_mul p 2 3 K (C-fullActualMoment p) hK hcut' using 1
    ring
  have h := precisionZero_add p 5 _ _ hβ htail
  convert h using 1
  dsimp only [K]
  ring

/-- The actual literal adapter has no source, residue, endpoint or moment premise. -/
theorem actual_literal_native_moment_adapter
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p)
      (3375*(p : ℚ)^2*WPReview.nativeCoefficient p*fullActualMoment p) := by
  let R := integralSubring p
  let S : ℚ := WPReview.Gamma (3*p-1)
    (fun k => actualRationalCoefficient (actualTotalSource p) k)
  let B : ℚ := WPReview.Gamma (3*p-1)
    (fun k => actualRationalCoefficient (actualBetaFunctional p) k)
  let J : ℚ := WPReview.Gamma (3*p-1)
    (fun k => actualRationalCoefficient (nativeSquareForcing p) k)
  let E : ℚ := 6750*(3*(p : ℚ))*WPReview.gamma (3*p-1)*
    actualRationalCoefficient (actualTotalPrimitive p) ((3*p : ℕ) : ℤ)
  let K : ℚ := (p : ℚ)^2*WPReview.nativeCoefficient p
  have hs : precisionZero p 5 (S-WPReview.nativeEndpoint p*B) :=
    (congruent_iff_precisionZero p 5 _ _).mp (actual_source_gamma_precision p hp)
  have hb : precisionZero p 5 (WPReview.nativeEndpoint p*B-K*fullActualMoment p) :=
    actual_beta_gamma_full_moment_precision p hp
  have hsfull : precisionZero p 5 (S-K*fullActualMoment p) := by
    convert precisionZero_add p 5 _ _ hs hb using 1
    ring
  have hs3375 : precisionZero p 5 ((S-K*fullActualMoment p)*3375) :=
    precisionZero_mul_integral p 5 _ _ hsfull (natCast_mem R 3375)
  have hj : precisionZero p 5 J := by
    have h := (congruent_iff_precisionZero p 5 _ _).mp (actual_square_forcing_gamma_precision p hp)
    simpa only [sub_zero] using h
  have he₆ : precisionZero p 6 E := actual_literal_upper_endpoint_precision p hp
  have he : precisionZero p 5 E := by
    rcases he₆ with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hStokes : WPReview.literalSum p=E+3375*S+J := by
    have h := actual_literal_extended_stokes p (by omega)
    rw [actual_total_primitive_constant_zero p (by omega)] at h
    simpa only [mul_zero, neg_zero, zero_add] using h
  apply (congruent_iff_precisionZero p 5 _ _).mpr
  have h := precisionZero_add p 5 _ _ (precisionZero_add p 5 _ _ he hs3375) hj
  convert h using 1
  rw [hStokes]
  dsimp only [K]
  ring

theorem actual_literal_adapter_and_normalization
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p)
      (3375*(p : ℚ)^2*WPReview.nativeCoefficient p*fullActualMoment p) ∧
    WPReview.RationalCongruent p 3 (WPReview.nativeCoefficient p) (120/(1728 : ℚ)^p) := by
  exact ⟨actual_literal_native_moment_adapter p hp, native_factorial_normalization p hp⟩

end

end WPLiteralAdapter
