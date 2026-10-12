import WPActualConductorEscape
import WPRationalDifferential

open Polynomial
open WPFiniteConductorPolynomial

namespace WPForcedSourceStokes

noncomputable section

noncomputable def actualEscapeTail (a₁ a₂ : ℚ) : RatFunc ℚ :=
  RatFunc.C a₁ / (99*symbol-50) + RatFunc.C a₂ / (99*symbol-50)^2

theorem actual_escape_tail_beta (a₁ a₂ : ℚ) :
    (1-symbol)*rationalDerivative (actualEscapeTail a₁ a₂) -
        actualEscapeTail a₁ a₂/2 =
      -98*RatFunc.C a₂/(99*symbol-50)^3 +
        (-49*RatFunc.C a₁+(3/2)*RatFunc.C a₂)/(99*symbol-50)^2 +
        RatFunc.C a₁/(2*(99*symbol-50)) := by
  let E : ℚ[X] := 99*X-50
  have hEp : E≠0 := by
    intro h
    have hc := congrArg (fun P : ℚ[X] => P.coeff 1) h
    norm_num [E] at hc
  have hE : algebraMap ℚ[X] (RatFunc ℚ) E=99*symbol-50 := by
    norm_num [E, symbol, map_ratCast, _root_.map_ofNat]
  have he : 99*symbol-50 ≠ 0 := hE ▸ RatFunc.algebraMap_ne_zero hEp
  have ht1 (a : ℚ) : RatFunc.C a/(99*symbol-50)=
      algebraMap ℚ[X] (RatFunc ℚ) (C a)/algebraMap ℚ[X] (RatFunc ℚ) E := by
    rw [RatFunc.algebraMap_C, hE]
  have ht2 (a : ℚ) : RatFunc.C a/(99*symbol-50)^2=
      algebraMap ℚ[X] (RatFunc ℚ) (C a)/algebraMap ℚ[X] (RatFunc ℚ) (E^2) := by
    rw [map_pow, RatFunc.algebraMap_C, hE]
  unfold actualEscapeTail
  rw [rationalDerivative_add, ht1, ht2, rationalDerivative_fraction _ _ hEp,
    rationalDerivative_fraction _ _ (pow_ne_zero _ hEp)]
  norm_num [E, derivative_pow_succ, map_mul, map_sub, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, _root_.map_ofNat]
  have heX : 99*RatFunc.X-50≠(0 : RatFunc ℚ) := by
    simpa only [symbol, RatFunc.algebraMap_X] using he
  simp only [symbol, RatFunc.algebraMap_X]
  field_simp [heX]
  ring

theorem precisionZero_escape_pole_elimination (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (a₁ a₂ : ℚ)
    (h₃ : precisionZero p 6 (-6750*98*a₂))
    (h₂ : precisionZero p 6 (6750*(-49*a₁+(3/2)*a₂))) :
    precisionZero p 6 a₁ ∧ precisionZero p 6 a₂ := by
  let R := integralSubring p
  have h2 : (1/2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h3 : (1/3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have h7 : (1/7 : ℚ) ∈ R := small_inverse_integral p 7 (by norm_num) (by omega)
  have hi₃ : (-6750*98 : ℚ)⁻¹ ∈ R := by
    rw [show (-6750*98 : ℚ)⁻¹ =
      -((1/2)^2*(1/3)^3*(1/5)^3*(1/7)^2) by norm_num]
    exact R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem h2 2)
      (R.pow_mem h3 3)) (R.pow_mem h5 3)) (R.pow_mem h7 2))
  have ha₂ : precisionZero p 6 a₂ := by
    have h := precisionZero_mul_integral p 6 _ _ h₃ hi₃
    convert h using 1
    field_simp
  have hc : precisionZero p 6 (-(10125*a₂)) := by
    have h := precisionZero_mul_integral p 6 _ _ ha₂ (R.neg_mem (natCast_mem R 10125))
    convert h using 1
    ring
  have ha₁' : precisionZero p 6 (-6750*49*a₁) := by
    have h := precisionZero_add p 6 _ _ h₂ hc
    convert h using 1
    ring
  have hi₂ : (-6750*49 : ℚ)⁻¹ ∈ R := by
    rw [show (-6750*49 : ℚ)⁻¹ =
      -((1/2)*(1/3)^3*(1/5)^3*(1/7)^2) by norm_num]
    exact R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem h2
      (R.pow_mem h3 3)) (R.pow_mem h5 3)) (R.pow_mem h7 2))
  have ha₁ : precisionZero p 6 a₁ := by
    have h := precisionZero_mul_integral p 6 _ _ ha₁' hi₂
    convert h using 1
    field_simp
  exact ⟨ha₁, ha₂⟩

end

end WPForcedSourceStokes
