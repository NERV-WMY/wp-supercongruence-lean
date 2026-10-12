import WPActualRankTwoCarrySource
import WPActualEvenLogCarry
import WPFiniteZSource
import WPFiniteLVSource
import WPFieldAssembly.NativeQuadraticInverse

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualSigmaFiniteEvenSource

set_option maxHeartbeats 1200000

/- This is the original rational finite logarithm in its squared variable.
The actual JointGreen attachment is proved separately by its existing exact
finiteEvenLogQ_eq_actual equality. No coefficient or endpoint is truncated. -/

noncomputable def finiteEvenSquaredQ (p : ℕ) : ℚ[X] := contract 2 (rationalEvenLog p)

noncomputable def finiteEvenSquaredIntegral (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  contract 2 (Polynomial.C (smallIntegralInverse p 2) *
    (integralLogPolynomial p + (integralLogPolynomial p).comp (-X)))

private theorem rationalEvenLog_even (p : ℕ) :
    (rationalEvenLog p).comp (-X) = rationalEvenLog p := by
  simp only [rationalEvenLog, mul_comp, C_comp, add_comp, comp_assoc,
    neg_comp, X_comp, neg_neg, comp_X]
  ring

/-- The squared polynomial retains exactly the original full finite logarithm. -/
theorem finiteEvenSquaredQ_pullback (p : ℕ) :
    (finiteEvenSquaredQ p).comp (X ^ 2) = rationalEvenLog p := by
  rw [finiteEvenSquaredQ, ← expand_eq_comp_X_pow]
  ext j
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hj]
  · rw [if_neg hj]
    have hm : j % 2 = 1 := by
      have hlt := Nat.mod_lt j (by norm_num : 0 < (2 : ℕ))
      have hne : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hj
      omega
    have ho : Odd j := ⟨j / 2, by have hh := Nat.mod_add_div j 2; omega⟩
    have hc := congrArg (fun P : ℚ[X] => P.coeff j) (rationalEvenLog_even p)
    rw [WPActualEvenLogCarry.coeff_comp_neg, ho.neg_one_pow] at hc
    linarith

/-- The full finite derivative used in SB95, before characteristic-p reduction. -/
theorem finiteEvenSquaredQ_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * (1 - X) * (finiteEvenSquaredQ p).derivative = 1 - X ^ ((p - 1) / 2) := by
  let E : ℚ[X] := 2 * (1 - X) * (finiteEvenSquaredQ p).derivative -
    (1 - X ^ ((p - 1) / 2))
  have hd := congrArg Polynomial.derivative (finiteEvenSquaredQ_pullback p)
  simp only [derivative_comp, derivative_X_pow, map_ofNat, Nat.cast_ofNat] at hd
  norm_num at hd
  have hs := WPActualRankTwoCarrySource.rationalEvenLog_source p (by omega)
  have hn := WPFiniteWSource.half_exponent p hp
  have hpow : (X : ℚ[X]) ^ p = X * (X ^ 2) ^ ((p - 1) / 2) := by
    calc
      _ = X ^ (2 * ((p - 1) / 2) + 1) := congrArg (fun n => (X : ℚ[X]) ^ n) hn
      _ = _ := by rw [pow_succ, pow_mul]; ring
  rw [hpow] at hs
  have hm : X * E.comp (X ^ 2) = 0 := by
    simp only [E, sub_comp, mul_comp, ofNat_comp, one_comp, X_comp, pow_comp]
    linear_combination (1 - X ^ 2) * hd + hs
  have hc : E.comp (X ^ 2) = 0 := (mul_eq_zero.mp hm).resolve_left X_ne_zero
  have he : E = 0 := by
    rw [← expand_eq_comp_X_pow] at hc
    have hh := congrArg (contract 2) hc
    rw [contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)] at hh
    simpa [contract] using hh
  dsimp only [E] at he
  exact sub_eq_zero.mp he

theorem finiteEvenSquaredIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (finiteEvenSquaredIntegral p).map (integralRationals p).subtype = finiteEvenSquaredQ p := by
  rw [finiteEvenSquaredIntegral, Polynomial.map_contract (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    integralLogPolynomial_value p, finiteEvenSquaredQ, rationalEvenLog]
  have hi : (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ) :=
    smallIntegralInverse_value p 2 (by omega) (by omega)
  rw [hi]

theorem finiteEvenSquaredIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (finiteEvenSquaredIntegral p).map (residueHom p) =
      (WPFiniteLVSource.evenSquared p : (ZMod p)[X]) := by
  rw [finiteEvenSquaredIntegral, Polynomial.map_contract (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    integralLogPolynomial_field p]
  rw [smallIntegralInverse_field p 2 (by omega) (by omega)]
  change contract 2 (WPFiniteKSource.EP p : (ZMod p)[X]) = WPFiniteLVSource.evenSquared p
  have he := WPFiniteLVSource.evenSquared_square (K := ZMod p) p hp
  rw [← Polynomial.expand_eq_comp_X_pow] at he
  rw [← he, Polynomial.contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)]

end WPFieldAssembly.ActualSigmaFiniteEvenSource
