import WPMomentPrecision.BasePole.PrimitiveWeights
import WPMomentPrecision.BasePole.BinomialCarry
import WPMomentPrecision.BasePole.FieldContractions
import WPMomentPrecision.BasePole.EndpointQuotient

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeMomentIntegrality

namespace WPMomentPrecision.BasePole

/-- The divided unit band uses the actual two-end rational primitive. -/
noncomputable def unitBlockSum (p : ℕ) (P : ℤ[X]) (c : ℤ) : ℚ :=
  ∑ r ∈ Finset.Ico 1 p, (P.coeff r : ℚ) *
    (primitiveWeight p (primitiveBlockIndex p r c) / (p : ℚ))

theorem rootPolynomial_add (P Q : ℤ[X]) :
    rootPolynomial (P + Q) = rootPolynomial P + rootPolynomial Q := by
  simp only [rootPolynomial, Polynomial.map_add, map_add]

theorem rootPolynomial_sub (P Q : ℤ[X]) :
    rootPolynomial (P - Q) = rootPolynomial P - rootPolynomial Q := by
  simp only [rootPolynomial, Polynomial.map_sub, map_sub]

theorem rootPolynomial_C (a : ℤ) : rootPolynomial (C a) = LaurentPolynomial.C (a : ℚ) := by
  rw [show C a = monomial 0 a by simp, rootPolynomial_monomial]
  norm_num

theorem rootPolynomial_X_pow (n : ℕ) :
    rootPolynomial (X ^ n) = LaurentPolynomial.T (2 * (n : ℤ)) := by
  rw [show (X ^ n : ℤ[X]) = monomial n 1 by
      rw [← C_mul_X_pow_eq_monomial, map_one, one_mul],
    rootPolynomial_monomial]
  simp

theorem numeratorDensity_add (p : ℕ) (P Q : ℤ[X]) :
    numeratorDensity p (P + Q) = numeratorDensity p P + numeratorDensity p Q := by
  simp only [numeratorDensity, rootPolynomial_add, mul_add, add_mul]

theorem numeratorDensity_sub (p : ℕ) (P Q : ℤ[X]) :
    numeratorDensity p (P - Q) = numeratorDensity p P - numeratorDensity p Q := by
  simp only [numeratorDensity, rootPolynomial_sub, mul_sub, sub_mul]

theorem numeratorDensity_C_mul (p : ℕ) (a : ℤ) (P : ℤ[X]) :
    numeratorDensity p (C a * P) = LaurentPolynomial.C (a : ℚ) * numeratorDensity p P := by
  rw [numeratorDensity, rootPolynomial_mul, rootPolynomial_C, numeratorDensity]
  ring

theorem numeratorPeriod_add (p : ℕ) (P Q : ℤ[X]) :
    numeratorPeriod p (P + Q) = numeratorPeriod p P + numeratorPeriod p Q := by
  rw [numeratorPeriod, numeratorDensity_add,
    WPActualResonanceReduction.rationalPrimitive_add]
  rfl

theorem numeratorPeriod_sub (p : ℕ) (P Q : ℤ[X]) :
    numeratorPeriod p (P - Q) = numeratorPeriod p P - numeratorPeriod p Q := by
  simp only [numeratorPeriod, numeratorDensity_sub,
    WPActualResonanceReduction.rationalPrimitive_eq_endpointIntegral, map_sub]
  ring

theorem numeratorPeriod_C_mul (p : ℕ) (a : ℤ) (P : ℤ[X]) :
    numeratorPeriod p (C a * P) = (a : ℚ) * numeratorPeriod p P := by
  simp only [numeratorPeriod, numeratorDensity_C_mul,
    WPActualResonanceReduction.rationalPrimitive_eq_endpointIntegral, integral_C_mul]
  ring

/-- A zero constant and degree p-1 retain precisely the entire interior row. -/
theorem rootPolynomial_interior_sum (p : ℕ) (hp : 1 ≤ p) (P : ℤ[X])
    (hP : P.natDegree ≤ p - 1) (h0 : P.coeff 0 = 0) :
    rootPolynomial P = ∑ r ∈ Finset.Ico 1 p,
      LaurentPolynomial.C (P.coeff r : ℚ) * LaurentPolynomial.T (2 * (r : ℤ)) := by
  rw [rootPolynomial_sum P (p - 1) hP, Nat.sub_add_cancel hp,
    ← Finset.sum_range_add_sum_Ico _ hp]
  simp only [Finset.sum_range_one, h0, Int.cast_zero, map_zero, zero_mul, zero_add]

/-- Exact attachment of every shifted interior row to its original ordered ends. -/
theorem numeratorPeriod_unit_block (p : ℕ) [Fact p.Prime] (P : ℤ[X]) (c : ℕ)
    (hP : P.natDegree ≤ p - 1) (h0 : P.coeff 0 = 0) :
    numeratorPeriod p (P * X ^ (c * p)) =
      (p : ℚ) / (125 : ℚ) ^ p * unitBlockSum p P (c : ℤ) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h125 : (125 : ℚ) ^ p ≠ 0 := pow_ne_zero p (by norm_num)
  have hsource : numeratorDensity p (P * X ^ (c * p)) =
      ∑ r ∈ Finset.Ico 1 p,
        LaurentPolynomial.C ((1 / (125 : ℚ) ^ p) * (P.coeff r : ℚ)) *
          LaurentPolynomial.T (primitiveBlockIndex p r (c : ℤ) - 1) := by
    rw [numeratorDensity, rootPolynomial_mul, rootPolynomial_X_pow,
      rootPolynomial_interior_sum p hp1 P hP h0, Finset.sum_mul,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    calc
      _ = LaurentPolynomial.C ((1 / (125 : ℚ) ^ p) * (P.coeff r : ℚ)) *
          (LaurentPolynomial.T (2 * (r : ℤ)) * LaurentPolynomial.T (2 * ((c*p : ℕ) : ℤ)) *
            LaurentPolynomial.T (-5 * (p : ℤ) - 1)) := by rw [map_mul]; ring
      _ = _ := by
        rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
        congr 2
        unfold primitiveBlockIndex
        push_cast
        ring
  rw [numeratorPeriod, hsource, rationalPrimitive_sum, unitBlockSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [WPActualResonanceReduction.rationalPrimitive_monomial, sub_add_cancel]
  field_simp [hpq, h125]

theorem unitBlockSum_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (c : ℤ) : 0 ≤ padicValRat p (unitBlockSum p P c) := by
  apply (integralRationals p).sum_mem
  intro r hr
  exact (integralRationals p).mul_mem
    (by change 0 ≤ padicValRat p (P.coeff r : ℚ)
        rw [padicValRat.of_int]
        exact Int.natCast_nonneg _)
    (divided_primitive_block_integral p r hp hr c)

theorem fieldWeight_primitiveBlockIndex (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (c : ℤ) :
    fieldWeight p (primitiveBlockIndex p r c) =
      dividedBlockWeight c (r : ZMod p) ((4 : ZMod p) ^ r) := by
  unfold fieldWeight dividedBlockWeight
  rw [two_block_positive_endpoint p r hp c, two_block_negative_endpoint p r hp c,
    primitiveBlockIndex_cast]

/-- Reduction is applied after rational division by p, never to p^-1 in F_p. -/
theorem unitBlockSum_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (c : ℤ) :
    (unitBlockSum p P c : ZMod p) =
      ∑ r ∈ Finset.Ico 1 p, (P.coeff r : ZMod p) *
        dividedBlockWeight c (r : ZMod p) ((4 : ZMod p) ^ r) := by
  rw [unitBlockSum, divided_primitive_weighted_sum_residue p (by omega)
    (Finset.Ico 1 p) (fun r ↦ (P.coeff r : ℚ)) (fun r ↦ primitiveBlockIndex p r c)
    (by intro r _hr; rw [padicValRat.of_int]; exact Int.natCast_nonneg _)
    (by intro r hr; exact primitiveBlockIndex_nonresonant p r hp hr c)]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Rat.cast_intCast, fieldWeight_primitiveBlockIndex p r hp c]

theorem firstFCarry_integer_coefficient_cast (p r : ℕ) [Fact p.Prime] :
    ((firstFCarry p : ℤ[X]).coeff r : ZMod p) =
      (firstFCarry p : (ZMod p)[X]).coeff r := by
  have he := congrArg (fun P : (ZMod p)[X] ↦ P.coeff r)
    (binomialInterior_map (Int.castRingHom (ZMod p)) p (-1 : ℤ) 4)
  simpa only [firstFCarry, Polynomial.coeff_map, Int.coe_castRingHom,
    Int.cast_neg, Int.cast_one, Int.cast_ofNat] using he

theorem firstGCarry_integer_coefficient_cast (p r : ℕ) [Fact p.Prime] :
    ((firstGCarry p : ℤ[X]).coeff r : ZMod p) =
      (firstGCarry p : (ZMod p)[X]).coeff r := by
  have he := congrArg (fun P : (ZMod p)[X] ↦ P.coeff r)
    (binomialInterior_map (Int.castRingHom (ZMod p)) p (4 : ℤ) (-1))
  simpa only [firstGCarry, Polynomial.coeff_map, Int.coe_castRingHom,
    Int.cast_neg, Int.cast_one, Int.cast_ofNat] using he

theorem firstFCarry_integer_map (p : ℕ) [Fact p.Prime] :
    (firstFCarry p : ℤ[X]).map (Int.castRingHom (ZMod p)) = firstFCarry p := by
  ext r
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using
    firstFCarry_integer_coefficient_cast p r

theorem firstGCarry_integer_map (p : ℕ) [Fact p.Prime] :
    (firstGCarry p : ℤ[X]).map (Int.castRingHom (ZMod p)) = firstGCarry p := by
  ext r
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using
    firstGCarry_integer_coefficient_cast p r

theorem actual_F_unitBlockSum_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (c : ℤ) :
    (unitBlockSum p (firstFCarry p) c : ZMod p) =
      ∑ r ∈ Finset.Ico 1 p, firstFCoeff p r *
        dividedBlockWeight c (r : ZMod p) ((4 : ZMod p) ^ r) := by
  rw [unitBlockSum_residue p hp]
  apply Finset.sum_congr rfl
  intro r hr
  rw [firstFCarry_integer_coefficient_cast, actual_firstFCarry_field_coefficient p r
    (by omega) hr]
  rfl

theorem actual_G_unitBlockSum_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (c : ℤ) :
    (unitBlockSum p (firstGCarry p) c : ZMod p) =
      ∑ r ∈ Finset.Ico 1 p, firstGCoeff p r *
        dividedBlockWeight c (r : ZMod p) ((4 : ZMod p) ^ r) := by
  rw [unitBlockSum_residue p hp]
  apply Finset.sum_congr rfl
  intro r hr
  rw [firstGCarry_integer_coefficient_cast, actual_firstGCarry_field_coefficient p r
    (by omega) hr]
  rfl

/-- The six entire first-carry blocks, with the original integer 4^p. -/
noncomputable def actualFirstCarryUnitSum (p : ℕ) : ℚ :=
  -2 * (4 : ℚ) ^ p * unitBlockSum p (firstFCarry p) 0 +
    2 * (((4 : ℚ) ^ p) ^ 2 + 1) * unitBlockSum p (firstFCarry p) 1 -
    2 * (4 : ℚ) ^ p * unitBlockSum p (firstFCarry p) 2 +
    ((4 : ℚ) ^ p) ^ 2 * unitBlockSum p (firstGCarry p) 0 -
    2 * (4 : ℚ) ^ p * unitBlockSum p (firstGCarry p) 1 +
    unitBlockSum p (firstGCarry p) 2

theorem actualFirstCarryUnitSum_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualFirstCarryUnitSum p) := by
  let R := integralRationals p
  let a : R := ⟨(4 : ℚ) ^ p, R.pow_mem (natCast_mem R 4) p⟩
  let J (P : ℤ[X]) (c : ℤ) : R := ⟨unitBlockSum p P c, unitBlockSum_integral p hp P c⟩
  exact (-(2 : R) * a * J (firstFCarry p) 0 +
    2 * (a ^ 2 + 1) * J (firstFCarry p) 1 -
    2 * a * J (firstFCarry p) 2 +
    a ^ 2 * J (firstGCarry p) 0 -
    2 * a * J (firstGCarry p) 1 + J (firstGCarry p) 2).property

/-- All p-1 unit indices survive until the complete first-carry contraction. -/
theorem actualFirstCarryUnitSum_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualFirstCarryUnitSum p : ZMod p) = 0 := by
  let R := integralRationals p
  let a : R := ⟨(4 : ℚ) ^ p, R.pow_mem (natCast_mem R 4) p⟩
  let J (P : ℤ[X]) (c : ℤ) : R := ⟨unitBlockSum p P c, unitBlockSum_integral p hp P c⟩
  have ha : residueHom p a = (4 : ZMod p) := by
    change (((4 : ℚ) ^ p : ℚ) : ZMod p) = 4
    rw [Rat.cast_pow, Rat.cast_ofNat, ZMod.pow_card]
  have hJ (P : ℤ[X]) (c : ℤ) : residueHom p (J P c) = (unitBlockSum p P c : ZMod p) := rfl
  change residueHom p (-(2 : R) * a * J (firstFCarry p) 0 +
    2 * (a ^ 2 + 1) * J (firstFCarry p) 1 -
    2 * a * J (firstFCarry p) 2 +
    a ^ 2 * J (firstGCarry p) 0 -
    2 * a * J (firstGCarry p) 1 + J (firstGCarry p) 2) = 0
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one, ha, hJ]
  rw [actual_F_unitBlockSum_residue p hp 0, actual_F_unitBlockSum_residue p hp 1,
    actual_F_unitBlockSum_residue p hp 2, actual_G_unitBlockSum_residue p hp 0,
    actual_G_unitBlockSum_residue p hp 1, actual_G_unitBlockSum_residue p hp 2]
  simp only [dividedBlockWeight_zero, dividedBlockWeight_one, dividedBlockWeight_two]
  have hs := whole_first_carry_contraction p (by omega)
  unfold blockWeight0 blockWeight1 blockWeight2 at hs
  convert hs using 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

theorem actualFirstCarryUnitSum_first_digit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (actualFirstCarryUnitSum p) 0 :=
  (integral_residue_zero_iff p _ (actualFirstCarryUnitSum_integral p hp)).mp
    (actualFirstCarryUnitSum_residue_zero p hp)

/-- SB2's first carry is the sum of six complete, signed interior blocks. -/
theorem actual_baseFirstCarry_integer_normalform (p : ℕ) :
    (baseFirstCarry p : ℤ[X]) =
      C (-2 * (4 : ℤ) ^ p) * (firstFCarry p * X ^ (0*p)) +
      C (2 * (((4 : ℤ) ^ p) ^ 2 + 1)) * (firstFCarry p * X ^ (1*p)) -
      C (2 * (4 : ℤ) ^ p) * (firstFCarry p * X ^ (2*p)) +
      C (((4 : ℤ) ^ p) ^ 2) * (firstGCarry p * X ^ (0*p)) -
      C (2 * (4 : ℤ) ^ p) * (firstGCarry p * X ^ (1*p)) +
      firstGCarry p * X ^ (2*p) := by
  unfold baseFirstCarry frobeniusF frobeniusG
  simp only [map_neg, map_mul, map_add, map_pow, map_one, C_ofNat,
    zero_mul, one_mul, pow_zero, mul_one,
    show 2*p=p*2 by omega, pow_mul]
  ring

/-- The actual first-carry period is p times the retained divided unit contraction. -/
theorem actual_baseFirstCarry_period_attachment (p : ℕ) [Fact p.Prime] :
    numeratorPeriod p (baseFirstCarry p) =
      (p : ℚ) / (125 : ℚ) ^ p * actualFirstCarryUnitSum p := by
  have hF : (firstFCarry p : ℤ[X]).natDegree ≤ p - 1 := binomialInterior_degree p (-1) 4
  have hG : (firstGCarry p : ℤ[X]).natDegree ≤ p - 1 := binomialInterior_degree p 4 (-1)
  have hF0 : (firstFCarry p : ℤ[X]).coeff 0 = 0 := by
    simp only [firstFCarry, binomialInterior_coefficient]
    simp
  have hG0 : (firstGCarry p : ℤ[X]).coeff 0 = 0 := by
    simp only [firstGCarry, binomialInterior_coefficient]
    simp
  rw [actual_baseFirstCarry_integer_normalform]
  simp only [numeratorPeriod_add, numeratorPeriod_sub, numeratorPeriod_C_mul]
  rw [numeratorPeriod_unit_block p _ 0 hF hF0, numeratorPeriod_unit_block p _ 1 hF hF0,
    numeratorPeriod_unit_block p _ 2 hF hF0, numeratorPeriod_unit_block p _ 0 hG hG0,
    numeratorPeriod_unit_block p _ 1 hG hG0, numeratorPeriod_unit_block p _ 2 hG hG0]
  simp only [Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_add, Int.cast_one,
    Int.cast_ofNat, actualFirstCarryUnitSum]
  ring

/-- Every coefficient of the original degree-three row has its signed, nonzero index. -/
theorem numeratorCoefficientIndex_bounds (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n ≤ 3*p) :
    2*(n : ℤ)-5*(p : ℤ) ≠ 0 ∧ (2*(n : ℤ)-5*(p : ℤ)).natAbs < p^2 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hkz : (p : ℤ) = 2*(k : ℤ)+1 := by exact_mod_cast hk
  have hnz : (n : ℤ) ≤ 3*(p : ℤ) := by exact_mod_cast hn
  have hne : 2*(n : ℤ)-5*(p : ℤ) ≠ 0 := by omega
  have habs : (2*(n : ℤ)-5*(p : ℤ)).natAbs ≤ 5*p := by omega
  exact ⟨hne, habs.trans_lt (by nlinarith)⟩

theorem numeratorCoefficientWeight_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n ≤ 3*p) :
    0 ≤ padicValRat p (primitiveWeight p (2*(n : ℤ)-5*(p : ℤ))) :=
  primitive_weight_general_integral p (by omega) _
    (numeratorCoefficientIndex_bounds p n hp hn).1
    (numeratorCoefficientIndex_bounds p n hp hn).2

/-- The full original coefficient sum is reduced before selecting either resonance. -/
theorem numeratorPeriod_residue_sum (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (hP : P.natDegree ≤ 3*p) :
    (numeratorPeriod p P : ZMod p) = (1 / 125 : ZMod p) *
      ∑ n ∈ Finset.range (3*p+1), (P.coeff n : ZMod p) *
        (primitiveWeight p (2*(n : ℤ)-5*(p : ℤ)) : ZMod p) := by
  have hn (n : ℕ) (hn : n ∈ Finset.range (3*p+1)) : n ≤ 3*p := by
    have h := Finset.mem_range.mp hn
    omega
  have ht (n : ℕ) (hn' : n ∈ Finset.range (3*p+1)) :
      0 ≤ padicValRat p ((P.coeff n : ℚ) *
        primitiveWeight p (2*(n : ℤ)-5*(p : ℤ))) :=
    (integralRationals p).mul_mem
      (by change 0 ≤ padicValRat p (P.coeff n : ℚ)
          rw [padicValRat.of_int]
          exact Int.natCast_nonneg _)
      (numeratorCoefficientWeight_integral p n hp (hn n hn'))
  have hsum := (integralRationals p).sum_mem ht
  have h125 := WPHasseIntegralTransport.one_over_125_integral p (by omega)
  have hc : 0 ≤ padicValRat p (1 / (125 : ℚ)^p) := by
    change 1 / (125 : ℚ)^p ∈ integralRationals p
    simpa only [one_div, inv_pow] using (integralRationals p).pow_mem h125 p
  have hcast : ((1 / (125 : ℚ)^p : ℚ) : ZMod p) = 1/125 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ZMod.pow_card, one_div] using
      (Rat.cast_inv_nat (α := ZMod p) (125^p))
  rw [numeratorPeriod_coefficient_formula p P (3*p) hP,
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hc)
      (integral_denominator_cast_ne_zero p _ hsum), hcast,
    cast_sum_integral p _ _ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn'
  rw [Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p _
      (by rw [padicValRat.of_int]; exact Int.natCast_nonneg _))
    (integral_denominator_cast_ne_zero p _
      (numeratorCoefficientWeight_integral p n hp (hn n hn'))), Rat.cast_intCast]

theorem numeratorCoefficientIndex_nonresonant (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n ≤ 3*p)
    (h0 : n ≠ 0) (h1 : n ≠ p) (h2 : n ≠ 2*p) (h3 : n ≠ 3*p) :
    ¬(p : ℤ) ∣ 2*(n : ℤ)-5*(p : ℤ) := by
  have hnunit : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hk3 : k ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ k := by omega
      have hmul := Nat.mul_le_mul_left p h4
      omega
    interval_cases k <;> omega
  have htwo := primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  intro hd
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (2*(n : ℤ)-5*(p : ℤ)) p).mpr hd
  have he' : (2 : ZMod p) * (n : ZMod p) = 0 := by simpa using he
  exact mul_ne_zero htwo hnunit he'

/-- Only the actual n=p and n=2p slots remain when the outer coefficients vanish. -/
theorem numeratorPeriod_two_resonance_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℤ[X]) (hP : P.natDegree ≤ 3*p)
    (h0 : P.coeff 0 = 0) (h3 : P.coeff (3*p) = 0) :
    (numeratorPeriod p P : ZMod p) = (1/125 : ZMod p) *
      ((P.coeff p : ZMod p) * (21/8) + (P.coeff (2*p) : ZMod p) * (3/2)) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  have hthree : (3 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      primitive_weight_small_nat_ne_zero p 3 (by omega) (by omega)
  have height : (8 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 htwo using 1
    norm_num
  have hm3 : ¬(p : ℤ) ∣ (-3 : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [Int.cast_neg, Int.cast_ofNat, neg_eq_zero] using hthree
  have hm1 : ¬(p : ℤ) ∣ (-1 : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp
  have hw1 : (primitiveWeight p (2*(p : ℤ)-5*(p : ℤ)) : ZMod p) = 21/8 := by
    rw [show 2*(p : ℤ)-5*(p : ℤ)=(-3)*(p : ℤ) by ring,
      primitive_resonant_residue p (by omega) (-3) hm3]
    norm_num
    field_simp [height, hthree]
    ring
  have hw2 : (primitiveWeight p (2*((2*p : ℕ) : ℤ)-5*(p : ℤ)) : ZMod p) = 3/2 := by
    rw [show 2*((2*p : ℕ) : ℤ)-5*(p : ℤ)=(-1)*(p : ℤ) by push_cast; ring,
      primitive_resonant_residue p (by omega) (-1) hm1]
    norm_num
    field_simp [htwo]
    ring
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hw2
  rw [numeratorPeriod_residue_sum p hp P hP]
  have hs : (∑ n ∈ Finset.range (3*p+1), (P.coeff n : ZMod p) *
      (primitiveWeight p (2*(n : ℤ)-5*(p : ℤ)) : ZMod p)) =
      ∑ n ∈ Finset.range (3*p+1),
        ((if n=p then (P.coeff p : ZMod p)*(21/8) else 0) +
          (if n=2*p then (P.coeff (2*p) : ZMod p)*(3/2) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn1 : n=p
    · subst n
      simp [hw1, show p ≠ 2*p by omega]
    by_cases hn2 : n=2*p
    · subst n
      simp [hw2, show 2*p ≠ p by omega]
    rw [if_neg hn1, if_neg hn2, add_zero]
    by_cases hn0 : n=0
    · simp [hn0, h0]
    by_cases hn3 : n=3*p
    · simp [hn3, h3]
    rw [primitive_nonresonant_residue p (by omega) _
      (numeratorCoefficientIndex_nonresonant p n hp
        (by have h := Finset.mem_range.mp hn; omega) hn0 hn1 hn2 hn3), mul_zero]
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range,
    show p < 3*p+1 by omega, show 2*p < 3*p+1 by omega, if_true]

theorem numeratorPeriod_monomial (p n : ℕ) (a : ℤ) :
    numeratorPeriod p (C a * X^n) = (a : ℚ) / (125 : ℚ)^p *
      primitiveWeight p (2*(n : ℤ)-5*(p : ℤ)) := by
  have hs : numeratorDensity p (C a * X^n) =
      LaurentPolynomial.C ((1/(125 : ℚ)^p)*(a : ℚ)) *
        LaurentPolynomial.T (2*(n : ℤ)-5*(p : ℤ)-1) := by
    rw [numeratorDensity, show (C a * X^n : ℤ[X]) = monomial n a
        from C_mul_X_pow_eq_monomial,
      rootPolynomial_monomial]
    calc
      _ = LaurentPolynomial.C ((1/(125 : ℚ)^p)*(a : ℚ)) *
          (LaurentPolynomial.T (2*(n : ℤ)) * LaurentPolynomial.T (-5*(p : ℤ)-1)) := by
            rw [map_mul]
            ring
      _ = _ := by
        rw [← LaurentPolynomial.T_add]
        congr 2
        ring
  rw [numeratorPeriod, hs, WPActualResonanceReduction.rationalPrimitive_monomial,
    show 2*(n : ℤ)-5*(p : ℤ)-1+1 = 2*(n : ℤ)-5*(p : ℤ) by ring]
  ring

/-- At a resonance the prime cancels in Q and the actual 2^p remains in both ends. -/
theorem primitiveWeight_lambda (p : ℕ) [Fact p.Prime] (b : ℤ) :
    primitiveWeight p (b*(p : ℤ)) =
      (((2 : ℚ)^p)^b - ((2 : ℚ)^p)^(-b)) / (b : ℚ) := by
  have hpow (z : ℤ) : (2 : ℚ)^(z*(p : ℤ)) = ((2 : ℚ)^p)^z := by
    rw [mul_comm z, zpow_mul, zpow_natCast]
  rw [primitive_resonant_rewrite, hpow,
    show -(b*(p : ℤ))=(-b)*(p : ℤ) by ring, hpow]

noncomputable def endpointInterior (p : ℕ) : ℤ[X] :=
  endpointGeometric p - C ((4 : ℤ)^(p-1))

noncomputable def actualEndpointMainUnitSum (p : ℕ) : ℚ :=
  -(4 : ℚ)^p*unitBlockSum p (endpointInterior p) 0 +
    (((4 : ℚ)^p)^2+1)*unitBlockSum p (endpointInterior p) 1 -
      (4 : ℚ)^p*unitBlockSum p (endpointInterior p) 2

theorem actualEndpointMainUnitSum_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualEndpointMainUnitSum p) := by
  let R := integralRationals p
  let a : R := ⟨(4 : ℚ)^p, R.pow_mem (natCast_mem R 4) p⟩
  let J (c : ℤ) : R := ⟨unitBlockSum p (endpointInterior p) c,
    unitBlockSum_integral p hp _ c⟩
  exact (-a*J 0+(a^2+1)*J 1-a*J 2).property

/-- The entire endpoint unit band cancels pointwise with all three Frobenius coefficients. -/
theorem actualEndpointMainUnitSum_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualEndpointMainUnitSum p : ZMod p) = 0 := by
  let R := integralRationals p
  let a : R := ⟨(4 : ℚ)^p, R.pow_mem (natCast_mem R 4) p⟩
  let J (c : ℤ) : R := ⟨unitBlockSum p (endpointInterior p) c,
    unitBlockSum_integral p hp _ c⟩
  have ha : residueHom p a = (4 : ZMod p) := by
    change (((4 : ℚ)^p : ℚ) : ZMod p)=4
    rw [Rat.cast_pow, Rat.cast_ofNat, ZMod.pow_card]
  have hJ (c : ℤ) : residueHom p (J c) = (unitBlockSum p (endpointInterior p) c : ZMod p) := rfl
  change residueHom p (-a*J 0+(a^2+1)*J 1-a*J 2)=0
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_one, ha, hJ]
  rw [unitBlockSum_residue p hp _ 0, unitBlockSum_residue p hp _ 1,
    unitBlockSum_residue p hp _ 2]
  simp only [dividedBlockWeight_zero, dividedBlockWeight_one, dividedBlockWeight_two]
  change
    -(4 : ZMod p)*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight0 (r : ZMod p) ((4 : ZMod p)^r)) +
    (4^2+1)*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight1 (r : ZMod p) ((4 : ZMod p)^r)) -
    4*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight2 (r : ZMod p) ((4 : ZMod p)^r)) = 0
  rw [show
    -(4 : ZMod p)*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight0 (r : ZMod p) ((4 : ZMod p)^r)) +
    (4^2+1)*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight1 (r : ZMod p) ((4 : ZMod p)^r)) -
    4*(∑ r ∈ Finset.Ico 1 p,
      ((endpointInterior p).coeff r : ZMod p)*blockWeight2 (r : ZMod p) ((4 : ZMod p)^r)) =
      ∑ r ∈ Finset.Ico 1 p, ((endpointInterior p).coeff r : ZMod p)*
        (-4*blockWeight0 (r : ZMod p) ((4 : ZMod p)^r)+
          17*blockWeight1 (r : ZMod p) ((4 : ZMod p)^r)-
          4*blockWeight2 (r : ZMod p) ((4 : ZMod p)^r)) by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
  apply Finset.sum_eq_zero
  intro r hr
  rw [endpoint_main_unit_block_zero (K := ZMod p) (r : ZMod p) ((4 : ZMod p)^r)
    (primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega))
    (WPFiniteInversion.denominator_ne_zero p r hr)
    (pow_ne_zero r (four_field_ne_zero p (by omega))), mul_zero]

theorem actualEndpointMainUnitSum_first_digit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (actualEndpointMainUnitSum p) 0 :=
  (integral_residue_zero_iff p _ (actualEndpointMainUnitSum_integral p hp)).mp
    (actualEndpointMainUnitSum_residue_zero p hp)

end WPMomentPrecision.BasePole
