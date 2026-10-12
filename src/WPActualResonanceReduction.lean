import WPActualEtaIntegration
import WPNC67ActualSources
import WPActualEtaIntegrality

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
open WPActualEtaIntegration WPActualEtaSupport WPPIntegralReduction WPActualMomentDefect
open WPActualChiSource WPHasseIntegralTransport WPActualEtaIntegrality

namespace WPActualResonanceReduction

theorem rationalPrimitive_add (p : ℕ) (P Q : ℚ[T;T⁻¹]) :
    rationalPrimitive p (P + Q) = rationalPrimitive p P + rationalPrimitive p Q := by
  unfold rationalPrimitive
  rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index]
  · intro j; simp
  · intro j _ a b; ring

theorem rationalPrimitive_monomial (p : ℕ) (a : ℚ) (j : ℤ) :
    rationalPrimitive p (C a * T j) = a * WPNativeMomentIntegrality.primitiveWeight p (j + 1) := by
  simp [rationalPrimitive, ← single_eq_C_mul_T]

/-- The entire coefficient primitive is the original two-endpoint period. -/
theorem rationalPrimitive_eq_endpointIntegral (p : ℕ) (P : ℚ[T;T⁻¹]) :
    rationalPrimitive p P = (p : ℚ) * endpointIntegral (1 / 2) 2 P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [rationalPrimitive_add, map_add, hP, hQ]; ring
  | C_mul_T j a =>
    rw [rationalPrimitive_monomial, integral_monomial]
    unfold WPNativeMomentIntegrality.primitiveWeight
      WPFiniteConductorReflection.monomialEndpoint
    rw [WPFiniteConductorReflection.reciprocal_two_zpow]
    ring

/-- Full original rational density for every signed resonance index. -/
noncomputable def resonanceSource (p : ℕ) (k : ℤ) : ℚ[T;T⁻¹] :=
  Spull ^ p * C 2 * T 1 * T (2 * (k * (p : ℤ) - 1))

theorem resonanceSource_normalform (p : ℕ) (k : ℤ) :
    resonanceSource p k = C 2 * Vpull ^ p * T ((2 * k - 1) * (p : ℤ) - 1) := by
  unfold resonanceSource
  rw [Spull_power]
  have hT : (T (-(p : ℤ)) * T 1 * T (2 * (k * (p : ℤ) - 1)) : ℚ[T;T⁻¹]) =
      T ((2 * k - 1) * (p : ℤ) - 1) := by
    rw [← T_add, ← T_add]
    congr 1
    ring
  calc
    _ = C 2 * Vpull ^ p * (T (-(p : ℤ)) * T 1 * T (2 * (k * (p : ℤ) - 1))) := by ring
    _ = _ := by rw [hT]

theorem resonancePeriod_eq_rationalPrimitive (p : ℕ) (k : ℤ) :
    resonancePeriod p k = rationalPrimitive p (resonanceSource p k) :=
  (rationalPrimitive_eq_endpointIntegral p (resonanceSource p k)).symm

theorem squareX_odd_coefficient (P : ℚ[T;T⁻¹]) (j : ℤ) (hj : Odd j) :
    (squareX P).coeff j = 0 := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]; simp
  | C_mul_T n a =>
    have hne : 2 * n ≠ j := by obtain ⟨u, hu⟩ := hj; omega
    rw [squareX_monomial, WPActualEtaPrimitive.finite_monomial_coeff]
    exact if_neg hne

theorem Vpull_bounded : bounded Vpull 0 6 := by
  have hP : (Vpolynomial.comp (Polynomial.X ^ 2)).natDegree ≤ 6 := by
    unfold Vpolynomial
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.ofNat_comp,
      Polynomial.one_comp]
    compute_degree
  have hL : Vpull = Polynomial.toLaurent (Vpolynomial.comp (Polynomial.X ^ 2)) := by
    rw [Vpull, Xpull]
    induction Vpolynomial using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simp only [substitute, map_add, Polynomial.add_comp] at *
      rw [hP, hQ]
    | monomial n a =>
      simp [substitute, Polynomial.monomial_comp, T_pow]
  rw [hL]
  exact bounded_toLaurent _ 6 hP

theorem resonanceSource_bounded (p : ℕ) (k : ℤ) :
    bounded (resonanceSource p k) ((2 * k - 1) * (p : ℤ) - 1)
      ((2 * k + 5) * (p : ℤ) - 1) := by
  rw [resonanceSource_normalform]
  exact bounded_mono
    (bounded_mul (bounded_mul (bounded_C 2) (bounded_pow Vpull_bounded p))
      (bounded_T _)) (by ring_nf; omega) (by ring_nf; omega)

theorem resonanceSource_no_log (p : ℕ) (hp : Odd p) (k : ℤ) :
    (resonanceSource p k).coeff (-1) = 0 := by
  have hform : resonanceSource p k =
      C 2 * T ((2 * k - 1) * (p : ℤ) - 1) * squareX (WPActualEtaPole.Vx ^ p) := by
    rw [resonanceSource_normalform, map_pow, squareX_Vx]
    ring
  rw [hform, WPFiniteCartier.coefficient_monomial_mul]
  have hodd : Odd (-1 - ((2 * k - 1) * (p : ℤ) - 1)) := by
    have hpz : Odd (p : ℤ) := by exact_mod_cast hp
    obtain ⟨u, hu⟩ := hpz
    refine ⟨(1 - 2 * k) * u - k, ?_⟩
    rw [hu]
    ring
  rw [squareX_odd_coefficient _ _ hodd, mul_zero]

theorem resonanceSource_primitive_bounds (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (k : ℤ) (hklo : -1 ≤ k) (hkhi : k ≤ 2)
    (j : ℤ) (hj : j ∈ (resonanceSource p k).coeff.support) :
    j + 1 ≠ 0 ∧ (j + 1).natAbs < p ^ 2 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hne := Finsupp.mem_support_iff.mp hj
  have hz : j + 1 ≠ 0 := by
    intro h
    have hj1 : j = -1 := by omega
    rw [hj1, resonanceSource_no_log p hpodd k] at hne
    exact hne rfl
  have hw := resonanceSource_bounded p k j hne
  have hpz : 0 < (p : ℤ) := by omega
  have hlo : -(3 * (p : ℤ)) ≤ j + 1 := by nlinarith [hw.1]
  have hhi : j + 1 ≤ 9 * (p : ℤ) := by nlinarith [hw.2]
  have ha : (j + 1).natAbs ≤ 9 * p := by omega
  exact ⟨hz, ha.trans_lt (by nlinarith)⟩

/-- Lift the actual cubic square pullback to the already proved integral subring. -/
noncomputable def integralPullV (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  substituteOver (integralV p hp) (T 2)

theorem integralPullV_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralPullV p hp) = Vpull := by
  simp only [integralPullV, integralV, substituteOver, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
    map_mul, map_pow, map_sub, map_ofNat, map_one, coefficientMap_C,
    coefficientMap_T, Subring.coe_subtype]
  simp only [Vpull, substitute, Vpolynomial, Xpull, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
    Polynomial.coe_eval₂RingHom]

theorem integralPullV_map_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    coefficientMap (residueHom p) (integralPullV p hp) = WPNC67ActualSources.actualV p := by
  simp only [integralPullV, integralV, substituteOver, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
    map_mul, map_pow, map_sub, map_ofNat, map_one, coefficientMap_C,
    coefficientMap_T]
  unfold WPNC67ActualSources.actualV
  congr 3
  change (((1 / 125 : ℚ) : ZMod p)) = 1 / (125 : ZMod p)
  simpa only [one_div, Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 125)

noncomputable def integralResonanceSource (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (k : ℤ) : (integralRationals p)[T;T⁻¹] :=
  C 2 * integralPullV p hp ^ p * T ((2 * k - 1) * (p : ℤ) - 1)

theorem integralResonanceSource_map_rational (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (k : ℤ) :
    coefficientMap (integralRationals p).subtype (integralResonanceSource p hp k) =
      resonanceSource p k := by
  rw [integralResonanceSource, map_mul, map_mul, coefficientMap_C, map_pow,
    integralPullV_map_rational, coefficientMap_T, resonanceSource_normalform]
  rfl

theorem resonanceSource_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℤ)
    (j : ℤ) : 0 ≤ padicValRat p ((resonanceSource p k).coeff j) := by
  have h := coefficientMap_subtype_integral p (integralResonanceSource p hp k)
  rw [integralResonanceSource_map_rational] at h
  exact h j

theorem reduceLaurent_integral_map (p : ℕ) [Fact p.Prime]
    (P : (integralRationals p)[T;T⁻¹]) :
    reduceLaurent p (coefficientMap (integralRationals p).subtype P) =
      coefficientMap (residueHom p) P := by
  ext j
  rw [reduceLaurent_coeff, coefficientMap_coeff, coefficientMap_coeff]
  rfl

theorem resonanceSource_reduction (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℤ) :
    reduceLaurent p (resonanceSource p k) =
      C 2 * WPNC67ActualSources.actualV p ^ p * T ((2 * k - 1) * (p : ℤ) - 1) := by
  rw [← integralResonanceSource_map_rational p hp k, reduceLaurent_integral_map,
    integralResonanceSource, map_mul, map_mul, coefficientMap_C, map_pow,
    integralPullV_map_field, coefficientMap_T]
  simp only [map_ofNat]

theorem resonanceSource_cartier (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℤ) :
    WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
      (reduceLaurent p (resonanceSource p k)) =
      C 2 * WPNC67ActualSources.actualV p * T (2 * k - 2) := by
  rw [resonanceSource_reduction p hp]
  have hn : (2 * k - 1) * (p : ℤ) - 1 =
      (p : ℤ) * ((2 * k - 2) + 1) - 1 := by ring
  rw [hn]
  calc
    _ = WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
        (WPNC67ActualSources.actualV p ^ p *
          (C 2 * T ((p : ℤ) * ((2 * k - 2) + 1) - 1))) := by congr 1; ring
    _ = _ := by
      rw [WPFiniteCartier.cartier_frobenius_product,
        WPFiniteCartier.cartier_selected_monomial]
      ring

/-- Every original resonance period reduces through its complete Cartier source. -/
theorem resonancePeriod_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (k : ℤ) (hklo : -1 ≤ k) (hkhi : k ≤ 2) :
    (resonancePeriod p k : ZMod p) =
      fieldPrimitive p (C 2 * WPNC67ActualSources.actualV p * T (2 * k - 2)) := by
  rw [resonancePeriod_eq_rationalPrimitive,
    rationalPrimitive_residue_cartier p (by omega) _ (resonanceSource_integral p (by omega) k)
      (fun j hj => (resonanceSource_primitive_bounds p hp k hklo hkhi j hj).1)
      (fun j hj => (resonanceSource_primitive_bounds p hp k hklo hkhi j hj).2),
    resonanceSource_cartier p (by omega)]

theorem rationalPrimitive_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : ℚ[T;T⁻¹]) (ha : ∀ j, 0 ≤ padicValRat p (P.coeff j))
    (hz : ∀ j ∈ P.coeff.support, j + 1 ≠ 0)
    (hb : ∀ j ∈ P.coeff.support, (j + 1).natAbs < p ^ 2) :
    0 ≤ padicValRat p (rationalPrimitive p P) := by
  change rationalPrimitive p P ∈ integralRationals p
  unfold rationalPrimitive Finsupp.sum
  apply (integralRationals p).sum_mem
  intro j hj
  exact (integralRationals p).mul_mem (ha j)
    (primitive_weight_general_integral p hp (j + 1) (hz j hj) (hb j hj))

theorem resonancePeriod_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (k : ℤ) (hklo : -1 ≤ k) (hkhi : k ≤ 2) :
    0 ≤ padicValRat p (resonancePeriod p k) := by
  rw [resonancePeriod_eq_rationalPrimitive]
  exact rationalPrimitive_integral p (by omega) _ (resonanceSource_integral p (by omega) k)
    (fun j hj => (resonanceSource_primitive_bounds p hp k hklo hkhi j hj).1)
    (fun j hj => (resonanceSource_primitive_bounds p hp k hklo hkhi j hj).2)

theorem resonanceMinus_kernel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    C 2 * WPNC67ActualSources.actualV p * T (-4) =
      WPNC67ProjectionIntegrals.resonanceMinus p := by
  apply WPRationalCartier.evaluate_injective p
  rw [map_mul, map_mul, WPRationalCartier.evaluate_C, WPRationalCartier.evaluate_T,
    WPNC67ActualSources.resonanceMinus_actual_source p hp]
  norm_num only [map_ofNat, zpow_neg, zpow_ofNat]
  ring

theorem resonancePlus_kernel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    C 2 * WPNC67ActualSources.actualV p * T 0 =
      WPNC67ProjectionIntegrals.resonancePlus p := by
  apply WPRationalCartier.evaluate_injective p
  rw [map_mul, map_mul, WPRationalCartier.evaluate_C, WPRationalCartier.evaluate_T,
    WPNC67ActualSources.resonancePlus_actual_source p hp]
  norm_num [map_ofNat]

theorem resonanceTwo_kernel (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    C 2 * WPNC67ActualSources.actualV p * T 2 =
      WPNC67ProjectionIntegrals.resonanceTwo p := by
  apply WPRationalCartier.evaluate_injective p
  rw [map_mul, map_mul, WPRationalCartier.evaluate_C, WPRationalCartier.evaluate_T,
    WPNC67ActualSources.resonanceTwo_actual_source p hp]
  norm_num [map_ofNat]

/-- All three original extra periods have their literal first digit, uniformly. -/
theorem actual_resonanceMinus_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (resonancePeriod p (-1) : ZMod p) = 54 / 125 := by
  rw [resonancePeriod_residue p hp (-1) (by norm_num) (by norm_num)]
  norm_num only [Int.reduceMul, Int.reduceSub]
  rw [resonanceMinus_kernel p hp, WPNC67ProjectionIntegrals.resonanceMinus_integral p hp]

theorem actual_resonancePlus_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (resonancePeriod p 1 : ZMod p) = 6102 / 4375 := by
  rw [resonancePeriod_residue p hp 1 (by norm_num) (by norm_num)]
  norm_num only [Int.reduceMul, Int.reduceSub]
  rw [resonancePlus_kernel p hp, WPNC67ProjectionIntegrals.resonancePlus_integral p hp]

theorem actual_resonanceTwo_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (resonancePeriod p 2 : ZMod p) = 28809 / 8750 := by
  rw [resonancePeriod_residue p hp 2 (by norm_num) (by norm_num)]
  norm_num only [Int.reduceMul, Int.reduceSub]
  rw [resonanceTwo_kernel p hp, WPNC67ProjectionIntegrals.resonanceTwo_integral p hp]

end WPActualResonanceReduction
