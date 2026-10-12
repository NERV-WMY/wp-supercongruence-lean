import WPLiteralAdapter.EscapeTailOrigin
import WPRationalPolynomialPart
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

open scoped LaurentSeries
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

noncomputable def escapeSquareRemainder (N : ℚ[X]) : ℚ[X] := N%escape^2
noncomputable def escapeSquareTailOne (N : ℚ[X]) : ℚ := (escapeSquareRemainder N).coeff 1/99
noncomputable def escapeSquareTailTwo (N : ℚ[X]) : ℚ :=
  (escapeSquareRemainder N).coeff 0+50*escapeSquareTailOne N

theorem escape_polynomial_nonzero : escape≠0 := by
  intro hz
  have hc := congrArg (fun P : ℚ[X] => P.coeff 0) hz
  norm_num [escape] at hc

theorem escape_square_degree : (escape^2).natDegree=2 := by
  unfold escape
  compute_degree!

theorem escape_square_nonzero : escape^2≠0 := pow_ne_zero 2 escape_polynomial_nonzero

theorem escape_square_remainder_linear (N : ℚ[X]) :
    escapeSquareRemainder N=C (escapeSquareTailOne N)*escape+C (escapeSquareTailTwo N) := by
  have hdeg : (escapeSquareRemainder N).natDegree<2 := by
    have h := Polynomial.natDegree_mod_lt N (q:=escape^2)
      (by rw [escape_square_degree]; decide)
    rw [escape_square_degree] at h
    exact h
  have hlin := eq_X_add_C_of_natDegree_le_one
    (show (escapeSquareRemainder N).natDegree≤1 by omega)
  calc
    escapeSquareRemainder N=C ((escapeSquareRemainder N).coeff 1)*X+
      C ((escapeSquareRemainder N).coeff 0) := hlin
    _=C (escapeSquareTailOne N)*escape+C (escapeSquareTailTwo N) := by
      unfold escapeSquareTailTwo escapeSquareTailOne
      ext k
      cases k with
      | zero => norm_num [escape, coeff_add, coeff_sub, coeff_C_mul]; ring
      | succ k =>
        cases k with
        | zero => norm_num [escape, coeff_add, coeff_sub, coeff_C_mul]
        | succ k => simp [escape, coeff_add, coeff_sub, coeff_C_mul, coeff_X]

/-- Exact polynomial quotient plus both tails of the honest escape-square fraction. -/
theorem escape_square_fraction_decomposition (N : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) N/algebraMap ℚ[X] (RatFunc ℚ) (escape^2) =
      algebraMap ℚ[X] (RatFunc ℚ)
        (rationalPolynomialPart (algebraMap ℚ[X] (RatFunc ℚ) N/
          algebraMap ℚ[X] (RatFunc ℚ) (escape^2)))+
      actualEscapeTail (escapeSquareTailOne N) (escapeSquareTailTwo N) := by
  have hpoly : escape^2*(N/escape^2)+C (escapeSquareTailOne N)*escape+
      C (escapeSquareTailTwo N)=N := by
    calc
      _=escape^2*(N/escape^2)+escapeSquareRemainder N := by
        rw [escape_square_remainder_linear]
        ring
      _=N := EuclideanDomain.div_add_mod N (escape^2)
  have hm := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) hpoly
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_C] at hm
  have he : algebraMap ℚ[X] (RatFunc ℚ) escape=99*symbol-50 := by
    norm_num [escape, symbol, map_sub, map_mul, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, _root_.map_ofNat]
  have hen : algebraMap ℚ[X] (RatFunc ℚ) escape≠0 :=
    RatFunc.algebraMap_ne_zero escape_polynomial_nonzero
  rw [rationalPolynomialPart_fraction N (escape^2) escape_square_nonzero]
  unfold actualEscapeTail
  rw [← he]
  simp only [map_pow]
  field_simp [hen]
  linear_combination -hm

theorem escape_square_polynomialPart_degree (N : ℚ[X]) (B : ℕ)
    (hN : N.natDegree≤B) :
    (rationalPolynomialPart (algebraMap ℚ[X] (RatFunc ℚ) N/
      algebraMap ℚ[X] (RatFunc ℚ) (escape^2))).natDegree≤B-2 := by
  rw [rationalPolynomialPart_fraction N (escape^2) escape_square_nonzero,
    ordinary_quotient_natDegree N (escape^2) escape_square_nonzero, escape_square_degree]
  omega

theorem rational_fraction_origin_powerSeries (N D : ℚ[X]) (hD0 : D.coeff 0≠0) :
    actualRationalSeries (algebraMap ℚ[X] (RatFunc ℚ) N/algebraMap ℚ[X] (RatFunc ℚ) D) =
      HahnSeries.ofPowerSeries ℤ ℚ ((N : PowerSeries ℚ)*(D : PowerSeries ℚ)⁻¹) := by
  rw [div_eq_mul_inv]
  simp only [actualRationalSeries, map_mul]
  change actualRationalSeries (algebraMap ℚ[X] (RatFunc ℚ) N)*
    actualRationalSeries ((algebraMap ℚ[X] (RatFunc ℚ) D)⁻¹) = _
  rw [actual_rational_series_polynomial, actual_polynomial_inverse_series D hD0]

theorem rational_fraction_origin_negative (N D : ℚ[X]) (hD0 : D.coeff 0≠0)
    (k : ℤ) (hk : k<0) :
    actualRationalCoefficient (algebraMap ℚ[X] (RatFunc ℚ) N/
      algebraMap ℚ[X] (RatFunc ℚ) D) k=0 := by
  rw [actualRationalCoefficient, rational_fraction_origin_powerSeries N D hD0,
    PowerSeries.coeff_coe, if_pos hk]

theorem rational_fraction_origin_zero (N D : ℚ[X]) (hD0 : D.coeff 0≠0) :
    actualRationalCoefficient (algebraMap ℚ[X] (RatFunc ℚ) N/
      algebraMap ℚ[X] (RatFunc ℚ) D) 0=N.coeff 0/D.coeff 0 := by
  rw [actualRationalCoefficient, rational_fraction_origin_powerSeries N D hD0,
    PowerSeries.coeff_coe]
  norm_num only [Int.reduceLT, if_false, Int.natAbs_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [map_mul, PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe, div_eq_mul_inv]

theorem escape_square_polynomialPart_constant (N : ℚ[X]) (hXN : (X : ℚ[X])∣N) :
    (rationalPolynomialPart (algebraMap ℚ[X] (RatFunc ℚ) N/
      algebraMap ℚ[X] (RatFunc ℚ) (escape^2))).coeff 0 =
      escapeSquareTailOne N/50-escapeSquareTailTwo N/2500 := by
  have hN0 : N.coeff 0=0 := X_dvd_iff.mp hXN
  have he0 : (escape^2).coeff 0=(2500 : ℚ) := by
    rw [pow_two, mul_coeff_zero]
    norm_num [escape]
  have hc := congrArg (fun P : ℚ[X] => P.coeff 0) (EuclideanDomain.div_add_mod N (escape^2))
  simp only [coeff_add, mul_coeff_zero, he0, hN0] at hc
  rw [rationalPolynomialPart_fraction N (escape^2) escape_square_nonzero]
  unfold escapeSquareTailTwo escapeSquareTailOne escapeSquareRemainder
  linear_combination (1/2500 : ℚ)*hc

/-- The actual lower endpoint is zero whenever its proved numerator has a factor X. -/
theorem escape_square_actual_constant_zero (N : ℚ[X]) (hXN : (X : ℚ[X])∣N) :
    actualRationalCoefficient (algebraMap ℚ[X] (RatFunc ℚ) N/
      algebraMap ℚ[X] (RatFunc ℚ) (escape^2)) 0=0 := by
  have hD : (escape^2).coeff 0≠0 := by norm_num [escape, mul_coeff_zero, pow_two]
  rw [rational_fraction_origin_zero N (escape^2) hD, X_dvd_iff.mp hXN, zero_div]

/-- beta preserves six-digit origin precision of both genuine escape tails. -/
theorem actual_escape_tail_beta_origin_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (a₁ a₂ : ℚ) (ha₁ : precisionZero p 6 a₁) (ha₂ : precisionZero p 6 a₂)
    (k : ℕ) : precisionZero p 6 (actualRationalCoefficient
      ((1-symbol)*rationalDerivative (actualEscapeTail a₁ a₂)-actualEscapeTail a₁ a₂/2) k) := by
  let R := integralSubring p
  have h2 : (1/2 : ℚ)∈R := small_inverse_integral p 2 (by norm_num) (by omega)
  rw [actual_beta_coefficient]
  have he : ((k : ℤ)+1 : ℤ)=((k+1 : ℕ) : ℤ) := by omega
  rw [he]
  have hfirst := precisionZero_mul_integral p 6 _ _
    (actual_escape_tail_origin_precision p hp a₁ a₂ ha₁ ha₂ (k+1)) (natCast_mem R (k+1))
  have hsecond := precisionZero_mul_integral p 6 _ _
    (actual_escape_tail_origin_precision p hp a₁ a₂ ha₁ ha₂ k)
      (R.neg_mem (R.add_mem (natCast_mem R k) h2))
  convert precisionZero_add p 6 _ _ hfirst hsecond using 1
  push_cast
  ring

end

end WPLiteralAdapter
