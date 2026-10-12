import WPActualAngularSourceIdentity

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 15000000
set_option maxRecDepth 20000

local instance conductorIntAlgebra {K : Type*} [Field K] : Algebra ℤ (RatFunc K) :=
  Ring.toIntAlgebra (RatFunc K)

@[simp] theorem conductor_symbol_derivative : rationalDerivative symbol = 1 := by
  rw [symbol, rationalDerivative_polynomial, derivative_X, map_one]

@[simp] theorem conductor_ratfuncX_derivative :
    rationalDerivative (RatFunc.X : RatFunc ℚ) = 1 := by
  simpa only [symbol, RatFunc.algebraMap_X] using conductor_symbol_derivative

noncomputable def bivMean : RatFunc (RatFunc ℚ) :=
  (27 / 1000) * bivX * (80 - 99 * bivX + 27 * bivX ^ 2)

noncomputable def bivEll : RatFunc (RatFunc ℚ) := (27 / 1000) * bivX * (9 * bivX - 16)

noncomputable def bivMeanX : RatFunc (RatFunc ℚ) :=
  (27 / 1000) * (80 - 198 * bivX + 81 * bivX ^ 2)

noncomputable def bivEllX : RatFunc (RatFunc ℚ) := (27 / 1000) * (18 * bivX - 16)

noncomputable def bivLam : RatFunc (RatFunc ℚ) := (729 / 15625) * bivX ^ 3

noncomputable def bivCollision : RatFunc (RatFunc ℚ) := 25 - 9 * bivX

noncomputable def bivEscape : RatFunc (RatFunc ℚ) := 99 * bivX - 50

noncomputable def bivConductor : RatFunc (RatFunc ℚ) :=
  bivS ^ 2 - 2 * bivMean * bivS + bivLam

noncomputable def bivConductorX : RatFunc (RatFunc ℚ) :=
  -2 * bivMeanX * bivS + (2187 / 15625) * bivX ^ 2

noncomputable def bivSourceDivisor : RatFunc (RatFunc ℚ) :=
  bivX ^ 4 * bivCollision * bivEscape ^ 2

/-- The complete ordinary-state s row divided by U. -/
noncomputable def bivBsDivU (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  2 * (bivLP i j * (bivS - bivMean) + bivEll * bivCollision * bivRP i j) /
    (bivSourceDivisor * bivConductor)

/-- The complete ordinary-state U row, after eliminating U squared. -/
noncomputable def bivBU (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  (-2 * (1 - bivX) * bivLP i j * bivConductorX +
    4 * (1 - bivX) * bivEll * bivCollision * bivRP i j * bivMeanX -
    2 * bivRP i j * (bivS - bivMean) *
      ((bivEll - 2 * (1 - bivX) * bivEllX) * bivCollision + 9 * (1 - bivX) * bivEll)) /
    (bivSourceDivisor * bivConductor)

noncomputable def bivJCG (q : RatFunc (RatFunc ℚ)) :
    Fin 3 → Fin 3 → RatFunc (RatFunc ℚ) :=
  ![![-5*q/72, 0, 2*q^2*(1-q)], ![-q/2, q*(q-1), 0], ![1-q, 0, 0]]

/-- Both matrices are actual transformed original witnesses. -/
noncomputable def bivConductorR (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    bivJCG bivS i a * bivBsDivU a b * bivJCG bivB j b

noncomputable def bivConductorBU (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    bivJCG bivS i a * bivBU a b * bivJCG bivB j b

noncomputable def bivSecondConnection
    (r : Fin 3 → Fin 3 → RatFunc (RatFunc ℚ)) (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  ∑ v : Fin 3, r i v * bivNativeMatrix bivB v j

theorem bivLam_literal : bivLam = bivLambda := by
  simp only [bivLam, bivLambda, lambda, map_mul, map_pow, map_div₀,
    _root_.map_ofNat, bivX]

theorem partialX_bivMean : partialX bivMean = bivMeanX := by
  norm_num [bivMean, bivMeanX, bivX, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.map_natCast, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul]
  ring

theorem partialX_bivEll : partialX bivEll = bivEllX := by
  norm_num [bivEll, bivEllX, bivX, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.map_natCast, Derivation.map_one_eq_zero,
    smul_eq_mul, nsmul_eq_mul]
  ring

theorem partialX_bivConductor : partialX bivConductor = bivConductorX := by
  norm_num [bivConductor, bivConductorX, bivLam, bivS, bivX,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    Derivation.map_natCast, Derivation.map_one_eq_zero,
    partialX_bivMean, smul_eq_mul, nsmul_eq_mul]
  ring

theorem bivS_quadratic_ne_zero (a b : RatFunc ℚ) :
    bivS ^ 2 - 2 * RatFunc.C a * bivS + RatFunc.C b ≠ 0 := by
  have hP : (X ^ 2 - C (2 * a) * X + C b : Polynomial (RatFunc ℚ)) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : Polynomial (RatFunc ℚ) => P.coeff 2) h
    norm_num at hc
  have h := RatFunc.algebraMap_ne_zero hP
  simpa only [bivS, map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, _root_.map_ofNat] using h

theorem bivConductor_ne_zero : bivConductor ≠ 0 := by
  have hm : bivMean = RatFunc.C
      ((27 / 1000) * symbol * (80 - 99 * symbol + 27 * symbol ^ 2)) := by
    simp only [bivMean, bivX, map_mul, map_sub, map_add, map_div₀, map_pow,
      _root_.map_ofNat]
  rw [bivConductor, hm, bivLam_literal, bivLambda]
  exact bivS_quadratic_ne_zero _ _

/-- Collecting the original transformed witness before differentiation avoids
repeating the same quadratic denominator in every matrix summand. -/
noncomputable def bivConductorRNum (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  2 * ∑ a : Fin 3, ∑ b : Fin 3, bivJCG bivS i a *
    (bivLP a b * (bivS-bivMean) + bivEll*bivCollision*bivRP a b) * bivJCG bivB j b

noncomputable def bivConductorBUNum (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  ∑ a : Fin 3, ∑ b : Fin 3, bivJCG bivS i a *
    (-2*(1-bivX)*bivLP a b*bivConductorX +
      4*(1-bivX)*bivEll*bivCollision*bivRP a b*bivMeanX -
      2*bivRP a b*(bivS-bivMean)*
        ((bivEll-2*(1-bivX)*bivEllX)*bivCollision+9*(1-bivX)*bivEll)) *
    bivJCG bivB j b

theorem actual_conductor_r_fraction (i j : Fin 3) :
    bivConductorR i j = bivConductorRNum i j/(bivSourceDivisor*bivConductor) := by
  simp only [bivConductorR, bivConductorRNum, bivBsDivU, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

theorem actual_conductor_bu_fraction (i j : Fin 3) :
    bivConductorBU i j = bivConductorBUNum i j/(bivSourceDivisor*bivConductor) := by
  simp only [bivConductorBU, bivConductorBUNum, bivBU, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

@[simp] theorem partialS_bivConductor : partialS bivConductor = 2*bivS-2*bivMean := by
  have hm : partialS bivMean = 0 := by
    norm_num [bivMean, bivX, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.leibniz_div, smul_eq_mul, nsmul_eq_mul]
  have hl : partialS bivLam = 0 := by
    norm_num [bivLam, bivX, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.leibniz_div, smul_eq_mul, nsmul_eq_mul]
  norm_num [bivConductor, bivS, hm, hl, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]

@[simp] theorem partialX_bivSourceDivisor : partialX bivSourceDivisor =
    4*bivX^3*bivCollision*bivEscape^2 - 9*bivX^4*bivEscape^2 +
      198*bivX^4*bivCollision*bivEscape := by
  norm_num [bivSourceDivisor, bivCollision, bivEscape, bivX,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  ring

@[simp] theorem partialS_bivSourceDivisor : partialS bivSourceDivisor = 0 := by
  norm_num [bivSourceDivisor, bivCollision, bivEscape, bivX,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]

macro "prove_actual_conductor_entry" : tactic =>
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
    have hf := bivConductor_ne_zero
    have hFC := bivConductor_ne_zero
    have hDC : bivSourceDivisor ≠ 0 := by
      unfold bivSourceDivisor bivCollision bivEscape
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 bivX_ne_zero)
        (by simpa only [neg_sub] using neg_ne_zero.mpr biv_collision_ne_zero))
        (pow_ne_zero 2 biv_escape_ne_zero)
    let w : RatFunc (RatFunc ℚ) := RatFunc.X
    have hFeq : 62500 * bivConductor = 62500*w^2 - 270000*z*w +
        334125*z^2*w - 91125*z^3*w + 2916*z^3 := by
      simp only [bivConductor, bivMean, bivLam, bivX, bivS, symbol, RatFunc.algebraMap_X]
      dsimp only [z, w]
      ring
    have hFn : (62500*w^2 - 270000*z*w + 334125*z^2*w - 91125*z^3*w + 2916*z^3) ≠ 0 := by
      rw [← hFeq]
      exact mul_ne_zero (by norm_num) hf
    dsimp only [z, w] at hFn
    simp only [bivConductor, bivMean, bivLam, bivX, bivS, symbol, RatFunc.algebraMap_X] at hf
    ring_nf at hFn hf
    all_goals
      simp [bivSourceQ, actual_conductor_r_fraction, actual_conductor_bu_fraction,
        bivConductorRNum, bivConductorBUNum, bivSecondConnection,
        bivRowConnection, bivNativeMatrix, bivJCG, partialX_bivConductor,
        partialX_bivMean, partialX_bivEll, partialS_bivConductor,
        bivLP, bivRP, partialX_bivSourceDivisor, partialS_bivSourceDivisor,
        bivConductorX,
        bivMean, bivMeanX, bivEll, bivEllX, bivCollision, bivEscape, bivLam,
        Fin.sum_univ_succ, bivB, bivLambda, lambda, bivX, bivS, symbol,
        Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
        smul_eq_mul, nsmul_eq_mul, map_add, map_sub, map_mul, map_neg, map_pow,
        RatFunc.algebraMap_X, map_div₀, _root_.map_ofNat]
      try field_simp (discharger := first | assumption | norm_num | (ring_nf; assumption) | (simp_all only [mul_ne_zero, pow_ne_zero, inv_ne_zero]))
      try simp only [bivSourceDivisor, bivConductor, bivMean, bivLam, bivCollision,
        bivEscape, bivX, bivS, symbol, RatFunc.algebraMap_X]
      try ring_nf
      try field_simp (discharger := first | assumption | norm_num | (ring_nf; assumption) | (simp_all only [mul_ne_zero, pow_ne_zero, inv_ne_zero]))
      try ring
  ))

theorem actual_positive_conductor_entry_00 :
    bivSourceQ 0 0 = -bivConductorR 0 0 +
      2 * (1 - bivX) * partialX (bivConductorR 0 0) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 0 0 +
      partialS (bivConductorBU 0 0) + bivRowConnection bivConductorBU 0 0 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_01 :
    bivSourceQ 0 1 = -bivConductorR 0 1 +
      2 * (1 - bivX) * partialX (bivConductorR 0 1) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 0 1 +
      partialS (bivConductorBU 0 1) + bivRowConnection bivConductorBU 0 1 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_02 :
    bivSourceQ 0 2 = -bivConductorR 0 2 +
      2 * (1 - bivX) * partialX (bivConductorR 0 2) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 0 2 +
      partialS (bivConductorBU 0 2) + bivRowConnection bivConductorBU 0 2 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_10 :
    bivSourceQ 1 0 = -bivConductorR 1 0 +
      2 * (1 - bivX) * partialX (bivConductorR 1 0) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 1 0 +
      partialS (bivConductorBU 1 0) + bivRowConnection bivConductorBU 1 0 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_11 :
    bivSourceQ 1 1 = -bivConductorR 1 1 +
      2 * (1 - bivX) * partialX (bivConductorR 1 1) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 1 1 +
      partialS (bivConductorBU 1 1) + bivRowConnection bivConductorBU 1 1 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_12 :
    bivSourceQ 1 2 = -bivConductorR 1 2 +
      2 * (1 - bivX) * partialX (bivConductorR 1 2) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 1 2 +
      partialS (bivConductorBU 1 2) + bivRowConnection bivConductorBU 1 2 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_20 :
    bivSourceQ 2 0 = -bivConductorR 2 0 +
      2 * (1 - bivX) * partialX (bivConductorR 2 0) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 2 0 +
      partialS (bivConductorBU 2 0) + bivRowConnection bivConductorBU 2 0 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_21 :
    bivSourceQ 2 1 = -bivConductorR 2 1 +
      2 * (1 - bivX) * partialX (bivConductorR 2 1) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 2 1 +
      partialS (bivConductorBU 2 1) + bivRowConnection bivConductorBU 2 1 := by
  prove_actual_conductor_entry

theorem actual_positive_conductor_entry_22 :
    bivSourceQ 2 2 = -bivConductorR 2 2 +
      2 * (1 - bivX) * partialX (bivConductorR 2 2) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR 2 2 +
      partialS (bivConductorBU 2 2) + bivRowConnection bivConductorBU 2 2 := by
  prove_actual_conductor_entry

/-- The positive source equation for all nine actual original conductor entries. -/
theorem actual_positive_conductor_row_identity (i j : Fin 3) :
    bivSourceQ i j = -bivConductorR i j +
      2 * (1 - bivX) * partialX (bivConductorR i j) +
      (6 * (1 - bivX) / bivX) * bivSecondConnection bivConductorR i j +
      partialS (bivConductorBU i j) + bivRowConnection bivConductorBU i j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact actual_positive_conductor_entry_00
    | exact actual_positive_conductor_entry_01
    | exact actual_positive_conductor_entry_02
    | exact actual_positive_conductor_entry_10
    | exact actual_positive_conductor_entry_11
    | exact actual_positive_conductor_entry_12
    | exact actual_positive_conductor_entry_20
    | exact actual_positive_conductor_entry_21
    | exact actual_positive_conductor_entry_22

end

end WPForcedSourceStokes
