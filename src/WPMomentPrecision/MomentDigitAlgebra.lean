import WPMomentPrecision.BasePole.PeriodPrecision

open WPPIntegralReduction
open WPMomentPrecision.BasePole

namespace WPMomentPrecision.MomentDigitAlgebra

theorem reviewCongruent_iff_sub_zero (p k : ℕ) (a b : ℚ) :
    WPReview.RationalCongruent p k a b ↔ WPReview.RationalCongruent p k (a - b) 0 := by
  unfold WPReview.RationalCongruent
  simp only [sub_zero, sub_eq_zero]

theorem reviewCongruent_zero_add (p k : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : WPReview.RationalCongruent p k a 0)
    (hb : WPReview.RationalCongruent p k b 0) :
    WPReview.RationalCongruent p k (a + b) 0 := by
  change WPGammaArithmetic.RationalCongruent p k (a + b) 0
  change WPGammaArithmetic.RationalCongruent p k a 0 at ha
  change WPGammaArithmetic.RationalCongruent p k b 0 at hb
  exact WPGammaArithmetic.rationalCongruent_zero_add p k (Fact.out : p.Prime) a b ha hb

/-
Statement fidelity: the NC69 coefficient calculation in
NORMALIZED_DEFECT_CONTRACTION.md, NC68--NC69, is expressed below over arbitrary
rational parameters. `normalizedTruncation` is the displayed NC64 expression
after the supplied base, pole and kernel substitutions; it is not the actual
native moment. `arithmeticDigit` and `resonanceDigit` are exactly the printed
P_p and R_p. The cubic remainder is a finite explicit polynomial. The only
actual arithmetic objects used here are the retained canonical Fermat units
and integer Fermat quotients in the final unit Taylor lemmas. This file does
not attach the actual residues or assert the remaining moment value.
The helper delivery is source-only; executable verification belongs to the
sole emitter for this package.
-/

def baseNormalizer : ℚ := 24 / 625

def baseFirstCoefficient (q2 q5 : ℚ) : ℚ := (32 / 3) * q2 - 3 * q5

def baseSecondCoefficient (q2 q5 alpha : ℚ) : ℚ :=
  (97 / 2) * q2 ^ 2 - 32 * q2 * q5 + 6 * q5 ^ 2 + (5 / 12) * alpha

def residueBaseline (q2 q3 q5 : ℚ) : ℚ :=
  -2 * q2 - (3 / 2) * q3 - (3 / 2) * q5

def poleFirstCoefficient (q2 : ℚ) : ℚ := (36 / 625) * q2 * 52

def poleSecondCoefficient (q2 q3 q5 : ℚ) : ℚ :=
  (36 / 625) * q2 * (-151 * q2 + 150 * q3 - 6 * q5)

def arithmeticDigit (q2 q3 q5 alpha : ℚ) : ℚ :=
  (304 / 3) * q2 ^ 2 - 11 * q2 * q3 - 11 * q2 * q5 - 9 * q3 * q5 -
    3 * q3 ^ 2 - 3 * q5 ^ 2 + (5 / 12) * alpha

def resonanceDigit (rho sminus s1 s2 : ℚ) : ℚ :=
  2 * rho + (5 / 4) * sminus + (113 / 28) * s1 + (1067 / 112) * s2

def unitSecondCoefficient (q2 q3 : ℚ) : ℚ :=
  15 * q2 ^ 2 + 18 * q2 * q3 + 3 * q3 ^ 2

def unitTarget (P q2 q3 : ℚ) : ℚ := (1 + P * q2) ^ 6 * (1 + P * q3) ^ 3

/-- Every term beyond the second coefficient of the degree-nine unit product. -/
def unitTaylorRemainder (P q2 q3 : ℚ) : ℚ :=
  (20 * q2 ^ 3 + 45 * q2 ^ 2 * q3 + 18 * q2 * q3 ^ 2 + q3 ^ 3) +
    P * (15 * q2 ^ 4 + 60 * q2 ^ 3 * q3 + 45 * q2 ^ 2 * q3 ^ 2 +
      6 * q2 * q3 ^ 3) +
    P ^ 2 * (6 * q2 ^ 5 + 45 * q2 ^ 4 * q3 + 60 * q2 ^ 3 * q3 ^ 2 +
      15 * q2 ^ 2 * q3 ^ 3) +
    P ^ 3 * (q2 ^ 6 + 18 * q2 ^ 5 * q3 + 45 * q2 ^ 4 * q3 ^ 2 +
      20 * q2 ^ 3 * q3 ^ 3) +
    P ^ 4 * (3 * q2 ^ 6 * q3 + 18 * q2 ^ 5 * q3 ^ 2 +
      15 * q2 ^ 4 * q3 ^ 3) +
    P ^ 5 * (3 * q2 ^ 6 * q3 ^ 2 + 6 * q2 ^ 5 * q3 ^ 3) +
    P ^ 6 * q2 ^ 6 * q3 ^ 3

def normalizedTruncation
    (P q2 q3 q5 alpha rho sminus s1 s2 u : ℚ) : ℚ :=
  ((1 - 2 * P * (residueBaseline q2 q3 q5 + P * rho)) *
      baseNormalizer *
      (1 + P * baseFirstCoefficient q2 q5 +
        P ^ 2 * baseSecondCoefficient q2 q5 alpha) -
    P / 9 * (poleFirstCoefficient q2 + P * poleSecondCoefficient q2 q3 q5) -
    P ^ 2 / 9 *
      (sminus * (54 / 125) + s1 * (6102 / 4375) + s2 * (28809 / 8750)) +
    P ^ 2 * baseNormalizer * u) / baseNormalizer

/-- The two remaining coefficients of the normalized degree-four truncation. -/
def truncationCubicRemainder (P q2 q3 q5 alpha rho : ℚ) : ℚ :=
  -2 * residueBaseline q2 q3 q5 * baseSecondCoefficient q2 q5 alpha -
    2 * rho * baseFirstCoefficient q2 q5 -
    2 * P * rho * baseSecondCoefficient q2 q5 alpha

/-- The exact NC69 remainder; its denominator primes are only 2 and 3. -/
def momentDigitRemainder (P q2 q3 q5 alpha rho : ℚ) : ℚ :=
  truncationCubicRemainder P q2 q3 q5 alpha rho - unitTaylorRemainder P q2 q3

theorem pole_first_coefficient_normalized (q2 : ℚ) :
    poleFirstCoefficient q2 / (9 * baseNormalizer) = (26 / 3) * q2 := by
  norm_num [poleFirstCoefficient, baseNormalizer]; ring

theorem pole_second_coefficient_normalized (q2 q3 q5 : ℚ) :
    poleSecondCoefficient q2 q3 q5 / (9 * baseNormalizer) =
      -(151 / 6) * q2 ^ 2 + 25 * q2 * q3 - q2 * q5 := by
  norm_num [poleSecondCoefficient, baseNormalizer]; ring

theorem kernel_coefficients_normalized (sminus s1 s2 : ℚ) :
    (sminus * (54 / 125) + s1 * (6102 / 4375) + s2 * (28809 / 8750)) /
        (9 * baseNormalizer) =
      (5 / 4) * sminus + (113 / 28) * s1 + (1067 / 112) * s2 := by
  norm_num [baseNormalizer]; ring

/-- The endpoint correction cancels exactly to the first unit coefficient. -/
theorem normalized_first_coefficient (q2 q3 q5 : ℚ) :
    baseFirstCoefficient q2 q5 - 2 * residueBaseline q2 q3 q5 -
        poleFirstCoefficient q2 / (9 * baseNormalizer) = 6 * q2 + 3 * q3 := by
  rw [pole_first_coefficient_normalized]
  unfold baseFirstCoefficient residueBaseline
  ring

/-- The second base and endpoint coefficients give precisely the printed P_p. -/
theorem base_pole_second_difference (q2 q3 q5 alpha : ℚ) :
    baseSecondCoefficient q2 q5 alpha -
        2 * residueBaseline q2 q3 q5 * baseFirstCoefficient q2 q5 -
        poleSecondCoefficient q2 q3 q5 / (9 * baseNormalizer) -
        unitSecondCoefficient q2 q3 = arithmeticDigit q2 q3 q5 alpha := by
  rw [pole_second_coefficient_normalized]
  unfold baseSecondCoefficient residueBaseline baseFirstCoefficient
    unitSecondCoefficient arithmeticDigit
  ring

theorem normalized_second_coefficient (q2 q3 q5 alpha rho sminus s1 s2 u : ℚ) :
    baseSecondCoefficient q2 q5 alpha -
        2 * residueBaseline q2 q3 q5 * baseFirstCoefficient q2 q5 - 2 * rho -
        poleSecondCoefficient q2 q3 q5 / (9 * baseNormalizer) -
        (sminus * (54 / 125) + s1 * (6102 / 4375) + s2 * (28809 / 8750)) /
          (9 * baseNormalizer) + u =
      unitSecondCoefficient q2 q3 + arithmeticDigit q2 q3 q5 alpha -
        resonanceDigit rho sminus s1 s2 + u := by
  rw [pole_second_coefficient_normalized, kernel_coefficients_normalized]
  unfold baseSecondCoefficient residueBaseline baseFirstCoefficient
    unitSecondCoefficient arithmeticDigit resonanceDigit
  ring

theorem unitTarget_exact_taylor (P q2 q3 : ℚ) :
    unitTarget P q2 q3 = 1 + P * (6 * q2 + 3 * q3) +
      P ^ 2 * unitSecondCoefficient q2 q3 + P ^ 3 * unitTaylorRemainder P q2 q3 := by
  unfold unitTarget unitSecondCoefficient unitTaylorRemainder
  ring

theorem normalizedTruncation_exact_taylor
    (P q2 q3 q5 alpha rho sminus s1 s2 u : ℚ) :
    normalizedTruncation P q2 q3 q5 alpha rho sminus s1 s2 u =
      1 + P * (6 * q2 + 3 * q3) +
        P ^ 2 * (unitSecondCoefficient q2 q3 + arithmeticDigit q2 q3 q5 alpha -
          resonanceDigit rho sminus s1 s2 + u) +
        P ^ 3 * truncationCubicRemainder P q2 q3 q5 alpha rho := by
  norm_num [normalizedTruncation, baseNormalizer, baseFirstCoefficient,
    baseSecondCoefficient, residueBaseline, poleFirstCoefficient,
    poleSecondCoefficient, unitSecondCoefficient, arithmeticDigit,
    resonanceDigit, truncationCubicRemainder]
  ring

/-- This is an unconditional rational polynomial identity, before any residue attachment. -/
theorem normalizedTruncation_defect_exact
    (P q2 q3 q5 alpha rho sminus s1 s2 u : ℚ) :
    normalizedTruncation P q2 q3 q5 alpha rho sminus s1 s2 u - unitTarget P q2 q3 =
      P ^ 2 * (arithmeticDigit q2 q3 q5 alpha - resonanceDigit rho sminus s1 s2 + u) +
        P ^ 3 * momentDigitRemainder P q2 q3 q5 alpha rho := by
  rw [normalizedTruncation_exact_taylor, unitTarget_exact_taylor]
  unfold momentDigitRemainder
  ring

theorem baseFirstCoefficient_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q2 q5 : ℚ) (hq2 : 0 ≤ padicValRat p q2) (hq5 : 0 ≤ padicValRat p q5) :
    0 ≤ padicValRat p (baseFirstCoefficient q2 q5) := by
  let R := integralRationals p
  let qq2 : R := ⟨q2, hq2⟩
  let qq5 : R := ⟨q5, hq5⟩
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  have h := (32 * c3 * qq2 - 3 * qq5).property
  change 0 ≤ padicValRat p (32 * (1 / 3) * q2 - 3 * q5) at h
  convert h using 1
  unfold baseFirstCoefficient
  norm_num

theorem baseSecondCoefficient_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q2 q5 alpha : ℚ) (hq2 : 0 ≤ padicValRat p q2)
    (hq5 : 0 ≤ padicValRat p q5) (ha : 0 ≤ padicValRat p alpha) :
    0 ≤ padicValRat p (baseSecondCoefficient q2 q5 alpha) := by
  let R := integralRationals p
  let qq2 : R := ⟨q2, hq2⟩
  let qq5 : R := ⟨q5, hq5⟩
  let aa : R := ⟨alpha, ha⟩
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by omega) (by omega)⟩
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  have h := (97 * c2 * qq2 ^ 2 - 32 * qq2 * qq5 + 6 * qq5 ^ 2 +
    5 * c2 ^ 2 * c3 * aa).property
  change 0 ≤ padicValRat p
    (97 * (1 / 2) * q2 ^ 2 - 32 * q2 * q5 + 6 * q5 ^ 2 +
      5 * (1 / 2) ^ 2 * (1 / 3) * alpha) at h
  convert h using 1
  unfold baseSecondCoefficient
  norm_num

theorem residueBaseline_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q2 q3 q5 : ℚ) (hq2 : 0 ≤ padicValRat p q2)
    (hq3 : 0 ≤ padicValRat p q3) (hq5 : 0 ≤ padicValRat p q5) :
    0 ≤ padicValRat p (residueBaseline q2 q3 q5) := by
  let R := integralRationals p
  let qq2 : R := ⟨q2, hq2⟩
  let qq3 : R := ⟨q3, hq3⟩
  let qq5 : R := ⟨q5, hq5⟩
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by omega) (by omega)⟩
  have h := (-2 * qq2 - 3 * c2 * qq3 - 3 * c2 * qq5).property
  change 0 ≤ padicValRat p (-2 * q2 - 3 * (1 / 2) * q3 - 3 * (1 / 2) * q5) at h
  convert h using 1
  unfold residueBaseline
  norm_num

theorem arithmeticDigit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q2 q3 q5 alpha : ℚ) (hq2 : 0 ≤ padicValRat p q2)
    (hq3 : 0 ≤ padicValRat p q3) (hq5 : 0 ≤ padicValRat p q5)
    (ha : 0 ≤ padicValRat p alpha) :
    0 ≤ padicValRat p (arithmeticDigit q2 q3 q5 alpha) := by
  let R := integralRationals p
  let qq2 : R := ⟨q2, hq2⟩
  let qq3 : R := ⟨q3, hq3⟩
  let qq5 : R := ⟨q5, hq5⟩
  let aa : R := ⟨alpha, ha⟩
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by omega) (by omega)⟩
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  have h := (304 * c3 * qq2 ^ 2 - 11 * qq2 * qq3 - 11 * qq2 * qq5 -
    9 * qq3 * qq5 - 3 * qq3 ^ 2 - 3 * qq5 ^ 2 + 5 * c2 ^ 2 * c3 * aa).property
  change 0 ≤ padicValRat p
    (304 * (1 / 3) * q2 ^ 2 - 11 * q2 * q3 - 11 * q2 * q5 -
      9 * q3 * q5 - 3 * q3 ^ 2 - 3 * q5 ^ 2 + 5 * (1 / 2) ^ 2 * (1 / 3) * alpha) at h
  convert h using 1
  unfold arithmeticDigit
  norm_num

theorem resonanceDigit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (rho sminus s1 s2 : ℚ) (hrho : 0 ≤ padicValRat p rho)
    (hm : 0 ≤ padicValRat p sminus) (h1 : 0 ≤ padicValRat p s1)
    (h2 : 0 ≤ padicValRat p s2) :
    0 ≤ padicValRat p (resonanceDigit rho sminus s1 s2) := by
  let R := integralRationals p
  let rrho : R := ⟨rho, hrho⟩
  let sm : R := ⟨sminus, hm⟩
  let ss1 : R := ⟨s1, h1⟩
  let ss2 : R := ⟨s2, h2⟩
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by omega) (by omega)⟩
  let c7 : R := ⟨1 / 7, WPFiniteConductorPolynomial.small_inverse_integral p 7
    (by omega) (by omega)⟩
  have h := (2 * rrho + 5 * c2 ^ 2 * sm + 113 * c2 ^ 2 * c7 * ss1 +
    1067 * c2 ^ 4 * c7 * ss2).property
  change 0 ≤ padicValRat p
    (2 * rho + 5 * (1 / 2) ^ 2 * sminus + 113 * (1 / 2) ^ 2 * (1 / 7) * s1 +
      1067 * (1 / 2) ^ 4 * (1 / 7) * s2) at h
  convert h using 1
  unfold resonanceDigit
  norm_num

theorem unitTaylorRemainder_integral (p : ℕ) [Fact p.Prime]
    (P q2 q3 : ℚ) (hP : 0 ≤ padicValRat p P)
    (hq2 : 0 ≤ padicValRat p q2) (hq3 : 0 ≤ padicValRat p q3) :
    0 ≤ padicValRat p (unitTaylorRemainder P q2 q3) := by
  let R := integralRationals p
  let PP : R := ⟨P, hP⟩
  let qq2 : R := ⟨q2, hq2⟩
  let qq3 : R := ⟨q3, hq3⟩
  exact ((20 * qq2 ^ 3 + 45 * qq2 ^ 2 * qq3 + 18 * qq2 * qq3 ^ 2 + qq3 ^ 3) +
    PP * (15 * qq2 ^ 4 + 60 * qq2 ^ 3 * qq3 + 45 * qq2 ^ 2 * qq3 ^ 2 +
      6 * qq2 * qq3 ^ 3) +
    PP ^ 2 * (6 * qq2 ^ 5 + 45 * qq2 ^ 4 * qq3 + 60 * qq2 ^ 3 * qq3 ^ 2 +
      15 * qq2 ^ 2 * qq3 ^ 3) +
    PP ^ 3 * (qq2 ^ 6 + 18 * qq2 ^ 5 * qq3 + 45 * qq2 ^ 4 * qq3 ^ 2 +
      20 * qq2 ^ 3 * qq3 ^ 3) +
    PP ^ 4 * (3 * qq2 ^ 6 * qq3 + 18 * qq2 ^ 5 * qq3 ^ 2 +
      15 * qq2 ^ 4 * qq3 ^ 3) +
    PP ^ 5 * (3 * qq2 ^ 6 * qq3 ^ 2 + 6 * qq2 ^ 5 * qq3 ^ 3) +
    PP ^ 6 * qq2 ^ 6 * qq3 ^ 3).property

theorem truncationCubicRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P q2 q3 q5 alpha rho : ℚ) (hP : 0 ≤ padicValRat p P)
    (hq2 : 0 ≤ padicValRat p q2) (hq3 : 0 ≤ padicValRat p q3)
    (hq5 : 0 ≤ padicValRat p q5) (ha : 0 ≤ padicValRat p alpha)
    (hrho : 0 ≤ padicValRat p rho) :
    0 ≤ padicValRat p (truncationCubicRemainder P q2 q3 q5 alpha rho) := by
  let R := integralRationals p
  let PP : R := ⟨P, hP⟩
  let rrho : R := ⟨rho, hrho⟩
  let rr0 : R := ⟨residueBaseline q2 q3 q5,
    residueBaseline_integral p hp q2 q3 q5 hq2 hq3 hq5⟩
  let bb1 : R := ⟨baseFirstCoefficient q2 q5,
    baseFirstCoefficient_integral p hp q2 q5 hq2 hq5⟩
  let bb2 : R := ⟨baseSecondCoefficient q2 q5 alpha,
    baseSecondCoefficient_integral p hp q2 q5 alpha hq2 hq5 ha⟩
  exact (-2 * rr0 * bb2 - 2 * rrho * bb1 - 2 * PP * rrho * bb2).property

theorem momentDigitRemainder_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P q2 q3 q5 alpha rho : ℚ) (hP : 0 ≤ padicValRat p P)
    (hq2 : 0 ≤ padicValRat p q2) (hq3 : 0 ≤ padicValRat p q3)
    (hq5 : 0 ≤ padicValRat p q5) (ha : 0 ≤ padicValRat p alpha)
    (hrho : 0 ≤ padicValRat p rho) :
    0 ≤ padicValRat p (momentDigitRemainder P q2 q3 q5 alpha rho) :=
  (integralRationals p).sub_mem
    (truncationCubicRemainder_integral p hp P q2 q3 q5 alpha rho
      hP hq2 hq3 hq5 ha hrho)
    (unitTaylorRemainder_integral p P q2 q3 hP hq2 hq3)

/-- Arbitrary source parameters remain visible; no moment-value premise is used. -/
theorem normalizedTruncation_defect_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q2 q3 q5 alpha rho sminus s1 s2 u : ℚ)
    (hq2 : 0 ≤ padicValRat p q2) (hq3 : 0 ≤ padicValRat p q3)
    (hq5 : 0 ≤ padicValRat p q5) (ha : 0 ≤ padicValRat p alpha)
    (hrho : 0 ≤ padicValRat p rho) :
    WPReview.RationalCongruent p 3
      (normalizedTruncation p q2 q3 q5 alpha rho sminus s1 s2 u - unitTarget p q2 q3)
      ((p : ℚ) ^ 2 *
        (arithmeticDigit q2 q3 q5 alpha - resonanceDigit rho sminus s1 s2 + u)) := by
  have hP : 0 ≤ padicValRat p (p : ℚ) := by
    change (p : ℚ) ∈ integralRationals p
    exact natCast_mem (integralRationals p) p
  have hi := momentDigitRemainder_integral p hp p q2 q3 q5 alpha rho
    hP hq2 hq3 hq5 ha hrho
  have h := integral_prime_power_precision p 3
    (momentDigitRemainder p q2 q3 q5 alpha rho) hi
  apply (reviewCongruent_iff_sub_zero p 3 _ _).mpr
  rw [normalizedTruncation_defect_exact]
  simpa only [add_sub_cancel_left] using h

def actualUnitTaylorRemainder (p : ℕ) : ℚ :=
  unitTaylorRemainder p (fermatQ p 2) (fermatQ p 3)

/-- The actual canonical Fermat units have the same exact finite Taylor identity. -/
theorem actual_unitPower_exact_taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3 =
      1 + (p : ℚ) * (6 * fermatQ p 2 + 3 * fermatQ p 3) +
        (p : ℚ) ^ 2 * unitSecondCoefficient (fermatQ p 2) (fermatQ p 3) +
        (p : ℚ) ^ 3 * actualUnitTaylorRemainder p := by
  have h2 := WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 := WPFiniteInversion.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  rw [fermatUnit_eq p 2 (by simpa using h2), fermatUnit_eq p 3 (by simpa using h3)]
  exact unitTarget_exact_taylor p (fermatQ p 2) (fermatQ p 3)

theorem actualUnitTaylorRemainder_integral (p : ℕ) [Fact p.Prime] :
    0 ≤ padicValRat p (actualUnitTaylorRemainder p) := by
  have hP : 0 ≤ padicValRat p (p : ℚ) := by
    change (p : ℚ) ∈ integralRationals p
    exact natCast_mem (integralRationals p) p
  exact unitTaylorRemainder_integral p p (fermatQ p 2) (fermatQ p 3)
    hP (fermatQ_integral p 2) (fermatQ_integral p 3)

theorem actual_unitPower_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 ((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)
      (1 + (p : ℚ) * (6 * fermatQ p 2 + 3 * fermatQ p 3) +
        (p : ℚ) ^ 2 * unitSecondCoefficient (fermatQ p 2) (fermatQ p 3)) := by
  have h := integral_prime_power_precision p 3 (actualUnitTaylorRemainder p)
    (actualUnitTaylorRemainder_integral p)
  apply (reviewCongruent_iff_sub_zero p 3 _ _).mpr
  rw [actual_unitPower_exact_taylor p hp]
  simpa only [add_sub_cancel_left] using h

end WPMomentPrecision.MomentDigitAlgebra
