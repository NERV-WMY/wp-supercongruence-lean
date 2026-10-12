import WPActualSourceRows

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

noncomputable section

local instance angularIntAlgebra {K : Type*} [Field K] : Algebra ℤ (RatFunc K) :=
  Ring.toIntAlgebra (RatFunc K)

@[simp] theorem bivariate_derivation_ofNat_zero
    (D : Derivation ℤ (RatFunc (RatFunc ℚ)) (RatFunc (RatFunc ℚ)))
    (n : ℕ) [n.AtLeastTwo] : D (ofNat(n)) = 0 := D.map_natCast n

macro "prove_actual_angular_entry" : tactic =>
  `(tactic| (
    have hx := bivX_ne_zero
    have hs := bivS_ne_zero
    have he := biv_escape_ne_zero
    have hm := biv_collision_ne_zero
    have h1 : bivS - 1 ≠ 0 := by simpa using bivS_sub_coefficient_ne_zero 1
    have hN : 1 - bivS ≠ 0 := by
      simpa only [neg_sub] using neg_ne_zero.mpr h1
    have hl : bivS - bivLambda ≠ 0 := bivS_sub_coefficient_ne_zero lambda
    have hLambda : bivLambda = (729 / 15625) * bivX ^ 3 := by
      simp only [bivLambda, lambda, map_mul, map_pow, map_div₀, _root_.map_ofNat, bivX]
    have hb : 1 - bivLambda / bivS ≠ 0 := by
      have hfrac : 1 - bivLambda / bivS = (bivS - bivLambda) / bivS := by
        field_simp [hs]
      rw [hfrac]
      exact div_ne_zero hl hs
    have hnum : 15625 * bivS - 729 * bivX ^ 3 ≠ 0 := by
      intro h
      apply hl
      rw [hLambda]
      have hfrac : bivS - (729 / 15625) * bivX ^ 3 =
          (15625 * bivS - 729 * bivX ^ 3) / 15625 := by ring
      rw [hfrac, h]
      norm_num
    simp only [bivX, bivS, bivLambda, lambda, symbol, map_mul, map_pow, map_div₀,
      _root_.map_ofNat, RatFunc.algebraMap_X] at hx hs he hm h1 hN hl hb hnum
    let z : RatFunc (RatFunc ℚ) := RatFunc.C (RatFunc.X : RatFunc ℚ)
    have hE0 : (-125000 + z*742500 - z^2*1470150 + z^3*970299) = (99*z-50)^3 := by ring
    have hM0 : (3125000 - z*19687500 + z^2*43436250 - z^3*37488825 + z^4*8732691) =
        (9*z-25)*(99*z-50)^3 := by ring
    have hM02 : (-62500 + z*270000 - z^2*334125 + z^3*88209) =
        (9*z-25)*(99*z-50)^2 := by ring
    have hM01 : (1250 - z*2925 + z^2*891) = (9*z-25)*(99*z-50) := by ring
    have hM02N : (-62500 + z*270000 - z^2*334125 + z^3*88209) ≠ 0 := by
      rw [hM02]
      exact mul_ne_zero hm (pow_ne_zero 2 he)
    have hM01N : (1250 - z*2925 + z^2*891) ≠ 0 := by
      rw [hM01]
      exact mul_ne_zero hm he
    dsimp only [z] at hM02 hM01 hM02N hM01N
    have hEr (r : ℕ) : (-(z^r*125000) + z^(r+1)*742500 - z^(r+2)*1470150 +
        z^(r+3)*970299) = z^r*(99*z-50)^3 := by simp only [pow_add]; ring
    have hMr (r : ℕ) : (z^r*3125000 - z^(r+1)*19687500 + z^(r+2)*43436250 -
        z^(r+3)*37488825 + z^(r+4)*8732691) = z^r*(9*z-25)*(99*z-50)^3 := by
      simp only [pow_add]; ring
    have hnum' : -(z^3*729) + (RatFunc.X : RatFunc (RatFunc ℚ))*15625 ≠ 0 := by
      convert hnum using 1 <;> dsimp [z] <;> ring
    have hb' : 15625 - z^3*(RatFunc.X : RatFunc (RatFunc ℚ))⁻¹*729 ≠ 0 := by
      have heq : 15625 - z^3*(RatFunc.X : RatFunc (RatFunc ℚ))⁻¹*729 =
          15625*(1-729/15625*z^3/(RatFunc.X : RatFunc (RatFunc ℚ))) := by ring
      rw [heq]
      exact mul_ne_zero (by norm_num) hb
    dsimp only [z] at hE0 hM0 hEr hMr hnum' hb'
    have hE0N : (-125000 + RatFunc.C (RatFunc.X : RatFunc ℚ)*742500 -
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^2*1470150 + (RatFunc.C (RatFunc.X : RatFunc ℚ))^3*970299) ≠ 0 := by
      rw [hE0]
      exact pow_ne_zero 3 he
    have hM0N : (3125000 - RatFunc.C (RatFunc.X : RatFunc ℚ)*19687500 +
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^2*43436250 - (RatFunc.C (RatFunc.X : RatFunc ℚ))^3*37488825 +
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^4*8732691) ≠ 0 := by
      rw [hM0]
      exact mul_ne_zero hm (pow_ne_zero 3 he)
    have hErN (r : ℕ) : (-((RatFunc.C (RatFunc.X : RatFunc ℚ))^r*125000) +
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+1)*742500 - (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+2)*1470150 +
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+3)*970299) ≠ 0 := by
      rw [hEr]
      exact mul_ne_zero (pow_ne_zero r hx) (pow_ne_zero 3 he)
    have hMrN (r : ℕ) : ((RatFunc.C (RatFunc.X : RatFunc ℚ))^r*3125000 -
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+1)*19687500 + (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+2)*43436250 -
        (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+3)*37488825 + (RatFunc.C (RatFunc.X : RatFunc ℚ))^(r+4)*8732691) ≠ 0 := by
      rw [hMr]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero r hx) hm) (pow_ne_zero 3 he)
    have hE2N := hErN 2
    have hE5N := hErN 5
    have hM2N := hMrN 2
    have hM5N := hMrN 5
    have heN : (-50 + RatFunc.C (RatFunc.X : RatFunc ℚ)*99 : RatFunc (RatFunc ℚ)) ≠ 0 := by
      convert he using 1 <;> ring
    have hmN : (-25 + RatFunc.C (RatFunc.X : RatFunc ℚ)*9 : RatFunc (RatFunc ℚ)) ≠ 0 := by
      convert hm using 1 <;> ring
    have h1N : (-1 + RatFunc.X : RatFunc (RatFunc ℚ)) ≠ 0 := by
      convert h1 using 1 <;> ring
    ring_nf at hE0N hM0N hE2N hE5N hM2N hM5N heN hmN h1N hnum' hb' hM02N hM01N
    all_goals
      simp [bivSourceQ, bivNormalSource, bivEta, bivRowConnection, bivNativeMatrix,
        bivWeight, Fin.sum_univ_succ, sourceEntry, sourceNumerator, sourceDenominator,
        bivB, bivLambda, lambda, bivX, bivS, symbol,
        Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
        smul_eq_mul, nsmul_eq_mul, map_add, map_sub, map_mul, map_neg, map_pow,
        RatFunc.algebraMap_X, map_div₀, _root_.map_ofNat]
      field_simp (discharger := first | assumption | norm_num | (ring_nf; assumption) | (simp_all only [mul_ne_zero, pow_ne_zero, inv_ne_zero]))
      try ring_nf
      try simp only [hE0, hM0, mul_inv_rev, ← inv_pow]
      try field_simp (discharger := first | assumption | norm_num | (ring_nf; assumption) | (simp_all only [mul_ne_zero, pow_ne_zero, inv_ne_zero]))
      try ring_nf
      try field_simp (discharger := first | assumption | norm_num | (ring_nf; assumption) | (simp_all only [mul_ne_zero, pow_ne_zero, inv_ne_zero]))
      try ring
  ))

theorem actual_angular_source_entry_00 :
    bivSourceQ 0 0 = bivNormalSource 0 0 + partialS (bivEta 0 0) +
      bivRowConnection bivEta 0 0 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_01 :
    bivSourceQ 0 1 = bivNormalSource 0 1 + partialS (bivEta 0 1) +
      bivRowConnection bivEta 0 1 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_02 :
    bivSourceQ 0 2 = bivNormalSource 0 2 + partialS (bivEta 0 2) +
      bivRowConnection bivEta 0 2 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_10 :
    bivSourceQ 1 0 = bivNormalSource 1 0 + partialS (bivEta 1 0) +
      bivRowConnection bivEta 1 0 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_11 :
    bivSourceQ 1 1 = bivNormalSource 1 1 + partialS (bivEta 1 1) +
      bivRowConnection bivEta 1 1 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_12 :
    bivSourceQ 1 2 = bivNormalSource 1 2 + partialS (bivEta 1 2) +
      bivRowConnection bivEta 1 2 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_20 :
    bivSourceQ 2 0 = bivNormalSource 2 0 + partialS (bivEta 2 0) +
      bivRowConnection bivEta 2 0 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_21 :
    bivSourceQ 2 1 = bivNormalSource 2 1 + partialS (bivEta 2 1) +
      bivRowConnection bivEta 2 1 := by
  prove_actual_angular_entry

theorem actual_angular_source_entry_22 :
    bivSourceQ 2 2 = bivNormalSource 2 2 + partialS (bivEta 2 2) +
      bivRowConnection bivEta 2 2 := by
  prove_actual_angular_entry

/-- All nine literal s12 entries satisfy the actual angular reduction identity. -/
theorem actual_angular_source_row_identity (i j : Fin 3) :
    bivSourceQ i j = bivNormalSource i j + partialS (bivEta i j) +
      bivRowConnection bivEta i j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact actual_angular_source_entry_00
    | exact actual_angular_source_entry_01
    | exact actual_angular_source_entry_02
    | exact actual_angular_source_entry_10
    | exact actual_angular_source_entry_11
    | exact actual_angular_source_entry_12
    | exact actual_angular_source_entry_20
    | exact actual_angular_source_entry_21
    | exact actual_angular_source_entry_22

end

end WPForcedSourceStokes
