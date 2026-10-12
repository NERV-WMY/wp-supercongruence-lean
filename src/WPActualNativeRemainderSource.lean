import WPActualNativeCanonicalPart
import WPActualNativeChiTaylor

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualEtaPole WPActualEtaSupport WPActualEtaIntegrality WPActualChiSource
  WPLaurentIntegralResidue WPActualPositiveResidueSource WPActualResidueVanishing
  WPActualCentralNativeJet WPActualNativeChiTaylor WPActualNativeParameter
  WPActualNativeFirstJet WPActualCentralResidueSource WPActualCanonicalSource
open WPPIntegralReduction WPQuadraticRationalCartier WPRationalCartier WPActualResonanceReduction

namespace WPActualNativeRemainderSource

variable (p : ℕ) [Fact p.Prime]

theorem substitute_V_bounded (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    bounded (substitute P Vx) 0 (3 * (d : ℤ)) := by
  rw [Polynomial.as_sum_range' P (d + 1) (by omega)]
  simp only [substitute, map_sum]
  apply bounded_sum
  intro n hn
  have hr := Finset.mem_range.mp hn
  change bounded (Polynomial.eval₂ C Vx (Polynomial.monomial n (P.coeff n))) 0 _
  rw [Polynomial.eval₂_monomial]
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Vx_bounded n))
    (by omega) (by omega)

theorem substitute_Q_bounded (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    bounded (substitute P Qx) (-3 * (d : ℤ)) 0 := by
  rw [Polynomial.as_sum_range' P (d + 1) (by omega)]
  simp only [substitute, map_sum]
  apply bounded_sum
  intro n hn
  have hr := Finset.mem_range.mp hn
  change bounded (Polynomial.eval₂ C Qx (Polynomial.monomial n (P.coeff n))) _ 0
  rw [Polynomial.eval₂_monomial]
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Qx_bounded n))
    (by omega) (by omega)

theorem actual_third_cutoff (hp : 7 ≤ p) : 3 * (p / 6) ≤ (p - 1) / 2 := by
  have hh := WPActualHasseReciprocal.actual_half_exponent p hp
  have hd := Nat.div_mul_le_self p 6
  omega

/-- The actual terminating carry has polynomial support, despite its division by p. -/
theorem actual_deltaTerm_support (hp : 7 ≤ p) :
    bounded (deltaTerm p) 0 (((p - 1) / 2 : ℕ) : ℤ) := by
  have hd := nativeTermPolynomial_degree p hp
  have hc := actual_third_cutoff p hp
  have hV := substitute_V_bounded (nativeTermPolynomial p) (p / 6) hd
  have hQ := bounded_mul (bounded_T (((p - 1) / 2 : ℕ) : ℤ))
    (substitute_Q_bounded (nativeTermPolynomial p) (p / 6) hd)
  have hV' : bounded (substitute (nativeTermPolynomial p) Vx) 0
      (((p - 1) / 2 : ℕ) : ℤ) := bounded_mono hV (by omega) (by omega)
  have hQ' : bounded (T (((p - 1) / 2 : ℕ) : ℤ) *
      substitute (nativeTermPolynomial p) Qx) 0 (((p - 1) / 2 : ℕ) : ℤ) :=
    bounded_mono hQ (by omega) (by omega)
  unfold deltaTerm termDifference
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_sub hV' hQ'))
    (by omega) (by omega)

omit [Fact p.Prime] in
theorem nativeJetPolynomial_degree :
    (nativeJetPolynomial p).natDegree ≤ (p - 1) / 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeJetPolynomial_coeff, if_neg (by omega)]

omit [Fact p.Prime] in
theorem actual_reciprocal_jet_support :
    bounded (nativeJetPullback p) (-2 * (((p - 1) / 2 : ℕ) : ℤ))
      (((p - 1) / 2 : ℕ) : ℤ) := by
  unfold nativeJetPullback
  exact bounded_mono (bounded_mul (bounded_T _)
    (substitute_Q_bounded (nativeJetPolynomial p) _ (nativeJetPolynomial_degree p)))
    (by omega) (by omega)

theorem weightedDifference_bounded (P : ℚ[T;T⁻¹]) (lo hi : ℤ)
    (hl : lo ≤ 0) (hu : 1 ≤ hi) (hP : bounded P lo hi) :
    bounded (weightedDifference P) lo (hi - 1) := by
  rw [weightedDifference_apply]
  exact bounded_add (bounded_mono (bounded_mul (bounded_C 2)
    (dividedDifference_bounded (1 / 4) P lo hi hl hu hP)) (by omega) (by omega))
    (dividedDifference_bounded 4 P lo hi hl hu hP)

/-- Every original native J coefficient is integrated, including the literal zero slot. -/
noncomputable def rationalNativeHJetPullback : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
    C (parameterJet n (-(p : ℚ) / 6) / (n : ℚ)) * Vx ^ n

omit [Fact p.Prime] in
theorem actual_positive_jet_derivative :
    weightedDifference (substitute (nativeJetPolynomial p) Vx) =
      derivative (rationalNativeHJetPullback p) := by
  simp only [nativeJetPolynomial, substitute, map_sum,
    rationalNativeHJetPullback]
  apply Finset.sum_congr rfl
  intro n _
  change weightedDifference (Polynomial.eval₂ C Vx
      (Polynomial.monomial n (parameterJet n (-(p : ℚ) / 6)))) = _
  rw [Polynomial.eval₂_monomial]
  rw [weightedDifference_C_mul, derivative_mul, derivative_C, zero_mul, zero_add]
  cases n with
  | zero => simp [weightedDifference_one]
  | succ n =>
    rw [weightedDifference_Vx_power, derivative_pow_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, ← mul_assoc, ← map_mul]
    congr 2
    field_simp

/-- Source representative after the positive native jet cancels. All reciprocal terms remain. -/
noncomputable def nativeRemainderRepresentative : ℚ[T;T⁻¹] :=
  weightedDifference (deltaTerm p) -
    C (1 / 6) * weightedDifference (nativeJetPullback p) +
    weightedDifference (HX (p / 6)) - C (1 / 2) * HX (p / 6) * T (-1)

theorem actual_remainder_representative_support (hp : 19 ≤ p) :
    bounded (nativeRemainderRepresentative p) (-(p : ℤ) + 1)
      ((((p - 1) / 2 : ℕ) : ℤ) - 1) := by
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hd := actual_third_cutoff p (by omega)
  have hN : (1 : ℤ) ≤ (((p - 1) / 2 : ℕ) : ℤ) := by omega
  have ht := weightedDifference_bounded (deltaTerm p) 0 _ (by omega) hN
    (actual_deltaTerm_support p (by omega))
  have hj := weightedDifference_bounded (nativeJetPullback p) _ _ (by omega) hN
    (actual_reciprocal_jet_support p)
  have hH := actual_HV_bounded (p / 6)
  have hHm : bounded (HX (p / 6)) (-(p : ℤ) + 1) (((p - 1) / 2 : ℕ) : ℤ) :=
    bounded_mono hH (by omega) (by omega)
  have hHw := weightedDifference_bounded _ _ _ (by omega) hN hHm
  unfold nativeRemainderRepresentative
  apply bounded_sub
  · apply bounded_add
    · exact bounded_sub (bounded_mono ht (by omega) (by omega))
        (bounded_mono (bounded_mul (bounded_C _) hj) (by omega) (by omega))
    · exact hHw
  · exact bounded_mono (bounded_mul (bounded_mul (bounded_C _) hH) (bounded_T (-1)))
      (by omega) (by omega)

theorem actual_remainder_representative_integral (hp : 19 ≤ p) :
    nativeRemainderRepresentative p ∈ integralLaurent p := by
  have h6 := WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have h2 := WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hH := actual_HX_integral p (p / 6) (by omega) (by omega)
  unfold nativeRemainderRepresentative
  exact (integralLaurent p).sub_mem
    ((integralLaurent p).add_mem
      ((integralLaurent p).sub_mem
        (weightedDifference_integral p (by omega) _ (actual_deltaTerm_integral p (by omega)))
        ((integralLaurent p).mul_mem (integral_C p _ h6)
          (weightedDifference_integral p (by omega) _ (actual_nativeJetPullback_integral p (by omega)))))
      (weightedDifference_integral p (by omega) _ hH))
    ((integralLaurent p).mul_mem ((integralLaurent p).mul_mem (integral_C p _ h2) hH)
      (integral_T p _))

/-- Exact full-source comparison, before any field primitive or endpoint projection. -/
theorem actual_remainder_representative_kernel (hp : 19 ≤ p) :
    residueZero p (Peta p ((p - 1) / 2) (p - 1 - p / 6) -
      C (1 / 6) * derivative (rationalNativeHJetPullback p) -
      nativeRemainderRepresentative p) := by
  have hc := weightedDifference_residue_kernel p (by omega) _
    (literal_chi_nativeTaylor_kernel p hp)
  have hH := actual_HX_low_cutoff p (p - 1 - p / 6) (by omega) (by omega) (by
    have h := Nat.div_mul_le_self p 6
    omega)
  have hw := weightedDifference_residue_kernel p (by omega) _ hH
  have h2 := WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)
  have hm := residueZero_mul_integral p (residueZero_mul_integral p hH (integral_C p _ h2))
    (integral_T p (-1))
  have h := residueZero_sub p (residueZero_add p hc hw) hm
  have hP : Peta p ((p - 1) / 2) (p - 1 - p / 6) =
      weightedDifference (AX p ((p - 1) / 2) (p - 1 - p / 6)) -
        C (1 / 2) * HX (p - 1 - p / 6) * T (-1) := by
    rw [Peta, weightedDifference_apply]
  convert h using 1
  rw [hP]
  simp only [AX, map_add, map_sub,
    weightedDifference_C_mul, jetDifference, actual_positive_jet_derivative,
    nativeRemainderRepresentative]
  ring

theorem native_jet_div_integral (n : ℕ) (hp : 7 ≤ p) (hn : n < p) :
    parameterJet n (-(p : ℚ) / 6) / (n : ℚ) ∈ integralRationals p := by
  by_cases hz : n = 0
  · subst n; simp
  · have hi := WPFiniteConductorPolynomial.small_inverse_integral p n (by omega) hn
    change 0 ≤ padicValRat p (1 / (n : ℚ)) at hi
    have hinv : (n : ℚ)⁻¹ ∈ integralRationals p := by
      change 0 ≤ padicValRat p (n : ℚ)⁻¹
      simpa only [one_div] using hi
    exact (integralRationals p).mul_mem (actual_parameterJet_integral p n hp hn) hinv

theorem actual_rationalNativeHJetPullback_integral (hp : 7 ≤ p) :
    rationalNativeHJetPullback p ∈ integralLaurent p := by
  rw [rationalNativeHJetPullback]
  apply (integralLaurent p).sum_mem
  intro n hn
  have hr := Finset.mem_range.mp hn
  exact (integralLaurent p).mul_mem
    (integral_C p _ (native_jet_div_integral p n hp (by omega)))
    ((integralLaurent p).pow_mem (integral_Vx p hp) n)

theorem reduceLaurent_sum_integral {ι : Type*} (s : Finset ι)
    (f : ι → ℚ[T;T⁻¹]) (hf : ∀ i ∈ s, f i ∈ integralLaurent p) :
    reduceLaurent p (∑ i ∈ s, f i) = ∑ i ∈ s, reduceLaurent p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reduceLaurent]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hsum : (∑ j ∈ s, f j) ∈ integralLaurent p := (integralLaurent p).sum_mem hfs
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      reduceLaurent_eq_residueLaurent p _ ((integralLaurent p).add_mem hfi hsum)]
    change residueLaurent p (⟨f i, hfi⟩ + ⟨∑ j ∈ s, f j, hsum⟩) = _
    rw [map_add, ← reduceLaurent_eq_residueLaurent p _ hfi,
      ← reduceLaurent_eq_residueLaurent p _ hsum, ih hfs]

theorem reduceLaurent_Vx (hp : 7 ≤ p) :
    reduceLaurent p Vx = Polynomial.toLaurent (WPHasseIntegralTransport.fieldV p) := by
  rw [← integralVx_map_rational p hp, reduceLaurent_integral_map,
    integralVx, coefficientMap_toLaurent, WPHasseIntegralTransport.integralV_map_field]

theorem native_jet_div_residue (n : ℕ) (hp : 7 ≤ p) (hn : n < p) :
    ((parameterJet n (-(p : ℚ) / 6) / (n : ℚ) : ℚ) : ZMod p) =
      (parameterJet n (-(p : ℚ) / 6) : ZMod p) / (n : ZMod p) := by
  by_cases hz : n = 0
  · subst n; simp
  · have hu : (n : ZMod p) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff n p).mp h
      have hh := Nat.le_of_dvd (by omega : 0 < n) hd
      omega
    have hnum : (((n : ℚ).num : ℤ) : ZMod p) ≠ 0 := by simpa using hu
    rw [Rat.cast_div_of_ne_zero
      (integral_denominator_cast_ne_zero p _ (actual_parameterJet_integral p n hp hn))
      hnum, Rat.cast_natCast]

theorem actual_nativeHJet_sum :
    WPActualNativeCanonicalPart.nativeHJet p =
      ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
        Polynomial.monomial n ((parameterJet n (-(p : ℚ) / 6) : ZMod p) / (n : ZMod p)) := by
  rw [Polynomial.as_sum_range' (WPActualNativeCanonicalPart.nativeHJet p)
    ((p - 1) / 2 + 1) (by have h := WPActualNativeCanonicalPart.nativeHJet_degree p; omega)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [WPActualNativeCanonicalPart.nativeHJet_coeff, if_pos (Finset.mem_range.mp hn)]

/-- The rational full native primitive reduces to the coefficient-selected field H_J. -/
theorem actual_rationalNativeHJetPullback_reduction (hp : 19 ≤ p) :
    reduceLaurent p (rationalNativeHJetPullback p) =
      Polynomial.toLaurent (WPActualCanonicalFinitePart.pullbackPolynomial p
        (WPActualNativeCanonicalPart.nativeHJet p)) := by
  rw [rationalNativeHJetPullback, reduceLaurent_sum_integral p]
  · rw [WPActualCanonicalFinitePart.pullbackPolynomial, actual_nativeHJet_sum,
      Polynomial.sum_comp, map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hr := Finset.mem_range.mp hn
    rw [reduceLaurent_mul_integral p _ _
      (integral_C p _ (native_jet_div_integral p n (by omega) (by omega)))
      ((integralLaurent p).pow_mem (integral_Vx p (by omega)) n),
      reduceLaurent_C_integral p _ (native_jet_div_integral p n (by omega) (by omega)),
      reduceLaurent_pow_integral p _ (integral_Vx p (by omega)),
      reduceLaurent_Vx p (by omega), native_jet_div_residue p n (by omega) (by omega),
      Polynomial.monomial_comp, map_mul, map_pow, Polynomial.toLaurent_C]
  · intro n hn
    have hr := Finset.mem_range.mp hn
    exact (integralLaurent p).mul_mem
      (integral_C p _ (native_jet_div_integral p n (by omega) (by omega)))
      ((integralLaurent p).pow_mem (integral_Vx p (by omega)) n)

theorem reduceLaurent_derivative (P : ℚ[T;T⁻¹]) (hP : P ∈ integralLaurent p) :
    reduceLaurent p (derivative P) =
      WPActualFieldPrimitive.fieldDerivative p (reduceLaurent p P) := by
  ext j
  rw [reduceLaurent_coeff, derivative_coefficient,
    WPActualFieldPrimitive.fieldDerivative_coeff, reduceLaurent_coeff,
    Rat.cast_mul_of_ne_zero
      (integral_denominator_cast_ne_zero p _ (intCast_mem (integralRationals p) (j + 1)))
      (integral_denominator_cast_ne_zero p _ (hP (j + 1))), Rat.cast_intCast]

/-- The actual remainder is the primitive of the full bounded original source representative. -/
theorem actual_native_remainder_representative (hp : 19 ≤ p) :
    WPActualNativeCanonicalPart.nativeRemainder p hp =
      WPActualFieldPrimitive.fieldPrimitive p (reduceLaurent p (nativeRemainderRepresentative p)) := by
  have hP := actual_Peta_integral p (p - 1 - p / 6) (by omega) (by omega) (by
    have h := Nat.div_mul_le_self p 6
    omega)
  have hH := actual_rationalNativeHJetPullback_integral p (by omega)
  have hD := derivative_integral p _ hH
  have h6 : (1 / 6 : ℚ) ∈ integralRationals p :=
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)
  have h6D := (integralLaurent p).mul_mem (integral_C p _ h6) hD
  have hr := (integralLaurent p).sub_mem hP h6D
  have hrep := actual_remainder_representative_integral p hp
  have he : reduceLaurent p (Peta p ((p - 1) / 2) (p - 1 - p / 6) -
      C (1 / 6) * derivative (rationalNativeHJetPullback p)) =
      reduceLaurent p (nativeRemainderRepresentative p) := by
    ext j
    rw [reduceLaurent_coeff, reduceLaurent_coeff]
    exact residue_coefficients_equal p _ _ hr hrep
      (actual_remainder_representative_kernel p hp) j
  rw [reduceLaurent_sub_integral p _ _ hP h6D,
    reduceLaurent_mul_integral p _ _ (integral_C p _ h6) hD,
    reduceLaurent_C_integral p _ h6, reduceLaurent_derivative p _ hH,
    actual_rationalNativeHJetPullback_reduction p hp] at he
  have hs : ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p) := by norm_num [Rat.cast_def]
  rw [hs] at he
  unfold WPActualNativeCanonicalPart.nativeRemainder WPActualCanonicalFinitePart.literalRemainder
    WPActualFieldPrimitive.literalFieldPeta
  rw [he]

theorem actual_native_remainder_support (hp : 19 ≤ p) (j : ℤ)
    (hj : (WPActualNativeCanonicalPart.nativeRemainder p hp).coeff j ≠ 0) :
    -(p : ℤ) + 2 ≤ j ∧ j ≤ (((p - 1) / 2 : ℕ) : ℤ) := by
  rw [actual_native_remainder_representative p hp,
    WPActualFieldPrimitive.fieldPrimitive_coeff, reduceLaurent_coeff] at hj
  have hc : (nativeRemainderRepresentative p).coeff (j - 1) ≠ 0 := by
    intro hz
    simp [hz] at hj
  have h := actual_remainder_representative_support p hp (j - 1) hc
  omega

end WPActualNativeRemainderSource
