import WPActualEtaIntegrality
import WPLaurentIntegralResidue
import WPFiniteLaurentDifferential
import WPFiniteJCarrier
import WPFiniteZSource

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPActualChiSource
namespace WPFieldAssembly.GreenLaurentOperators
variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def forward (a : R) : ℕ → R[T;T⁻¹]
  | 0 => 0
  | n + 1 => T (n : ℤ) + C a * forward a n
noncomputable def monQ (a ai : R) : ℤ → R[T;T⁻¹]
  | .ofNat n => forward a n
  | .negSucc n => -C (ai ^ (n + 1)) * T (-(n + 1 : ℤ)) * forward a (n + 1)
noncomputable def DD (a ai : R) : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  (Finsupp.linearCombination R (monQ a ai)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem DD_monomial (a ai c : R) (n : ℤ) :
    DD a ai (C c * T n) = C c * monQ a ai n := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination R _ (Finsupp.single n c) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul]

theorem forward_map (f : R →+* S) (a : R) (n : ℕ) :
    coefficientMap f (forward a n) = forward (f a) n := by
  induction n with
  | zero => simp [forward]
  | succ n ih =>
    simp only [forward, map_add, map_mul, coefficientMap_C,
      coefficientMap_T, ih]

theorem monQ_map (f : R →+* S) (a ai : R) (n : ℤ) :
    coefficientMap f (monQ a ai n) = monQ (f a) (f ai) n := by
  cases n <;> simp only [monQ, map_neg, map_mul, coefficientMap_C,
    coefficientMap_T, map_pow, forward_map]

theorem DD_map (f : R →+* S) (a ai : R) (L : R[T;T⁻¹]) :
    coefficientMap f (DD a ai L) = DD (f a) (f ai) (coefficientMap f L) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add, hL, hM]
  | C_mul_T n c =>
    rw [DD_monomial, map_mul, coefficientMap_C, monQ_map,
      coefficientMap_monomial, DD_monomial]

private theorem forward_Q (a : ℚ) (n : ℕ) :
    forward a n = WPActualEtaPole.forwardQuotient a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forward, WPActualEtaPole.forwardQuotient, ih]

private theorem monQ_Q (a : ℚ) (n : ℤ) :
    monQ a a⁻¹ n = WPActualEtaPole.monomialQuotient a n := by
  cases n with
  | ofNat n => exact forward_Q a n
  | negSucc n =>
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    have hz : a ^ (-(n + 1 : ℤ)) = a⁻¹ ^ (n + 1) := by
      calc
        a ^ (-(n + 1 : ℤ)) = (a ^ ((n : ℤ) + 1))⁻¹ :=
          zpow_neg a ((n : ℤ) + 1)
        _ = (a ^ ((n + 1 : ℕ) : ℤ))⁻¹ :=
          congrArg (fun z : ℤ => (a ^ z)⁻¹) hn
        _ = (a ^ (n + 1))⁻¹ :=
          congrArg (fun x : ℚ => x⁻¹) (zpow_natCast a (n + 1))
        _ = a⁻¹ ^ (n + 1) := (inv_pow a (n + 1)).symm
    simp only [monQ, WPActualEtaPole.monomialQuotient, forward_Q, hz]

theorem DD_Q (a : ℚ) (L : ℚ[T;T⁻¹]) :
    DD a a⁻¹ L = WPActualEtaPole.dividedDifference a L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add, hL, hM]
  | C_mul_T n c =>
    rw [DD_monomial, WPActualEtaPole.dividedDifference_monomial, monQ_Q]

/-- Actual rational quotients are lifted before reduction. -/
theorem integralLift_DD (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ WPPIntegralReduction.integralRationals p)
    (hai : a⁻¹ ∈ WPPIntegralReduction.integralRationals p)
    (L : WPActualEtaIntegrality.integralLaurent p) :
    WPLaurentIntegralResidue.integralLift p
      ⟨WPActualEtaPole.dividedDifference a L.val,
        WPActualEtaIntegrality.dividedDifference_integral p a ha hai L.val L.property⟩ =
      DD (⟨a, ha⟩ : WPPIntegralReduction.integralRationals p) ⟨a⁻¹, hai⟩
        (WPLaurentIntegralResidue.integralLift p L) := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (WPPIntegralReduction.integralRationals p).subtype
    (Subring.subtype_injective _)
  rw [WPLaurentIntegralResidue.integralLift_rational, DD_map,
    WPLaurentIntegralResidue.integralLift_rational]
  exact (DD_Q a L.val).symm

/-- This is the exact actual DD transport. -/
theorem residueLaurent_DD (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ WPPIntegralReduction.integralRationals p)
    (hai : a⁻¹ ∈ WPPIntegralReduction.integralRationals p)
    (L : WPActualEtaIntegrality.integralLaurent p) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨WPActualEtaPole.dividedDifference a L.val,
        WPActualEtaIntegrality.dividedDifference_integral p a ha hai L.val L.property⟩ =
      DD (a : ZMod p) ((a⁻¹ : ℚ) : ZMod p)
        (WPLaurentIntegralResidue.residueLaurent p L) := by
  change coefficientMap (WPPIntegralReduction.residueHom p)
    (WPLaurentIntegralResidue.integralLift p _) = _
  rw [integralLift_DD p a ha hai L, DD_map]
  rfl

theorem cm_coeff (c : R) (n k : ℤ) :
    (C c * T n).coeff k = if n = k then c else 0 := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_apply
theorem C_mul_coeff (c : R) (L : R[T;T⁻¹]) (k : ℤ) :
    (C c * L).coeff k = c * L.coeff k := by
  rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
theorem shift_coeff (c : R) (s k : ℤ) (L : R[T;T⁻¹]) :
    (C c * T s * L).coeff k = c * L.coeff (k-s) := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single_mul_apply]
  congr 1
  congr 1
  omega

theorem forward_coeff (a : R) (n : ℕ) (k : ℤ) :
    (forward a n).coeff k =
      if 0 ≤ k ∧ k < (n : ℤ) then a ^ ((n : ℤ)-1-k).toNat else 0 := by
  induction n with
  | zero =>
    rw [forward]
    have h : ¬(0 ≤ k ∧ k < (0 : ℤ)) := by omega
    simp [h]
  | succ n ih =>
    rw [forward, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      show (T (n : ℤ) : R[T;T⁻¹]) = C 1 * T (n : ℤ) by simp,
      cm_coeff, C_mul_coeff, ih]
    by_cases hk0 : 0 ≤ k
    · by_cases hkn : k = (n : ℤ)
      · subst k
        have h1 : ¬(0 ≤ (n : ℤ) ∧ (n : ℤ) < n) := by omega
        have h2 : 0 ≤ (n : ℤ) ∧ (n : ℤ) < (n+1 : ℕ) := by omega
        have hz : (((n+1 : ℕ) : ℤ)-1-(n : ℤ)).toNat = 0 := by omega
        rw [if_pos rfl, if_neg h1, if_pos h2, hz, pow_zero, mul_zero, add_zero]
      · by_cases hkl : k < (n : ℤ)
        · have h1 : 0 ≤ k ∧ k < (n : ℤ) := ⟨hk0,hkl⟩
          have h2 : 0 ≤ k ∧ k < (n+1 : ℕ) := by omega
          have he : (((n+1 : ℕ) : ℤ)-1-k).toNat =
              ((n : ℤ)-1-k).toNat + 1 := by omega
          rw [if_neg (Ne.symm hkn), if_pos h1, if_pos h2, he, pow_succ]
          ring
        · have h1 : ¬(0 ≤ k ∧ k < (n : ℤ)) := by omega
          have h2 : ¬(0 ≤ k ∧ k < (n+1 : ℕ)) := by omega
          rw [if_neg (Ne.symm hkn), if_neg h1, if_neg h2, mul_zero, add_zero]
    · have h1 : ¬(0 ≤ k ∧ k < (n : ℤ)) := by omega
      have h2 : ¬(0 ≤ k ∧ k < (n+1 : ℕ)) := by omega
      have hn : (n : ℤ) ≠ k := by omega
      rw [if_neg hn, if_neg h1, if_neg h2, mul_zero, add_zero]

theorem monQ_nonnegative_coeff (a ai : R) (j : ℤ) (k : ℕ) :
    (monQ a ai j).coeff (k : ℤ) =
      if (k : ℤ) < j then a ^ (j-(k : ℤ)-1).toNat else 0 := by
  cases j with
  | ofNat n =>
    change (forward a n).coeff (k : ℤ) =
      if (k : ℤ) < (n : ℤ) then a ^ ((n : ℤ)-(k : ℤ)-1).toNat else 0
    rw [forward_coeff]
    simp only [show 0 ≤ (k : ℤ) by omega, true_and]
    rw [show (n : ℤ)-1-(k : ℤ) = (n : ℤ)-(k : ℤ)-1 by omega]
  | negSucc n =>
    rw [monQ, ← map_neg (C : R →+* R[T;T⁻¹]) (ai ^ (n + 1)),
      shift_coeff, forward_coeff]
    have h1 : ¬(0 ≤ (k : ℤ)-(-(n+1 : ℤ)) ∧
      (k : ℤ)-(-(n+1 : ℤ)) < ((n+1 : ℕ) : ℤ)) := by omega
    have h2 : ¬(k : ℤ) < Int.negSucc n := by omega
    rw [if_neg h1, if_neg h2, mul_zero]

variable {K : Type*} [Field K]

theorem DD_shift_monomial (a ai c : K) (s : ℤ) (n k : ℕ) :
    (DD a ai (T s * (Polynomial.monomial n c).toLaurent)).coeff (k : ℤ) =
      c * (if (k : ℤ) < s + n then a ^ (s+(n : ℤ)-(k : ℤ)-1).toNat else 0) := by
  rw [Polynomial.toLaurent_C_mul_T]
  have hm : T s * (C c * T (n : ℤ)) = C c * T (s + n) := by
    rw [LaurentPolynomial.T_add]
    ring
  rw [hm, DD_monomial, C_mul_coeff, monQ_nonnegative_coeff]

theorem DD_positive_phase_middle (p : ℕ) (hp : 0 < p) (a ai : K) (Q : K[X]) :
    (DD a ai (T (p : ℤ) * Q.toLaurent)).coeff ((p : ℤ)-1) = Q.eval a := by
  have hi : ((p-1 : ℕ) : ℤ) = (p : ℤ)-1 := by omega
  rw [← hi]
  induction Q using Polynomial.induction_on' with
  | add Q S hQ hS =>
    simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hQ, hS, Polynomial.eval_add]
  | monomial n c =>
    rw [DD_shift_monomial]
    have hlt : ((p-1 : ℕ) : ℤ) < (p : ℤ)+n := by omega
    have he : ((p : ℤ)+(n : ℤ)-((p-1 : ℕ) : ℤ)-1).toNat = n := by omega
    simp [hlt,he]

theorem DD_polynomial_phase_zero (p : ℕ) (hp : 0 < p) (a ai : K)
    (s : ℤ) (Q : K[X]) (hQ : (Q.natDegree : ℤ)+s < (p : ℤ)) :
    (DD a ai (T s * Q.toLaurent)).coeff ((p : ℤ)-1) = 0 := by
  classical
  have hi : ((p-1 : ℕ) : ℤ) = (p : ℤ)-1 := by omega
  rw [← hi]
  conv_lhs => rw [Q.as_sum_support_C_mul_X_pow]
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  rw [DD_shift_monomial]
  have hnd := Polynomial.le_natDegree_of_mem_supp n hn
  have hnot : ¬(((p-1 : ℕ) : ℤ) < s+(n : ℤ)) := by omega
  rw [if_neg hnot, mul_zero]

/-- A homogeneous Frobenius correction contributes exactly 3 alpha. -/
theorem homogeneous_middle (p : ℕ) (hp : 0 < p) (F : K[X])
    (hF : F.natDegree < p) (ha : F.eval (1/4) = 1) (hb : F.eval 4 = 1)
    (α β γ : K) :
    (2 * DD (1/4 : K) 4 (F.toLaurent *
      (C α*T (p : ℤ)+C β+C γ*T (-(p : ℤ)))) +
      DD (4 : K) (1/4) (F.toLaurent *
      (C α*T (p : ℤ)+C β+C γ*T (-(p : ℤ))))).coeff ((p : ℤ)-1) = 3*α := by
  have hplus (a ai : K) := DD_positive_phase_middle p hp a ai F
  have hzero (a ai : K) := DD_polynomial_phase_zero p hp a ai 0 F (by omega)
  have hminus (a ai : K) := DD_polynomial_phase_zero p hp a ai (-(p : ℤ)) F (by omega)
  have hs (a ai c : K) (L : K[T;T⁻¹]) : DD a ai (C c*L)=C c*DD a ai L := by
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]
  simp only [mul_add, show ∀ c s, F.toLaurent*(C c*T s)=C c*(T s*F.toLaurent) by
    intro c s; ring, show ∀ c, F.toLaurent*C c=C c*(T 0*F.toLaurent) by
    intro c; simp only [T_zero,one_mul]; ring, map_add, hs,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, C_mul_coeff,
    show (2 : K[T;T⁻¹])=C (2 : K) by rfl, hplus, hzero, hminus, ha, hb]
  ring

noncomputable def weightedDD (L : K[T;T⁻¹]) : K[T;T⁻¹] :=
  C 2 * DD (1/4 : K) 4 L + DD (4 : K) (1/4) L
noncomputable def eta (χ H : K[T;T⁻¹]) : K[T;T⁻¹] :=
  weightedDD (χ+H) - C (1/2 : K)*H*T (-1)

noncomputable def ev (a : K) (ha : a ≠ 0) : K[T;T⁻¹] →+* K :=
  LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 a ha)

private theorem forward_identity (a : K) (n : ℕ) :
    (T 1-C a)*forward a n = T (n : ℤ)-C (a^n) := by
  induction n with
  | zero => simp [forward]
  | succ n ih =>
    rw [forward,mul_add]
    calc
      _ = T 1*T (n : ℤ)-C a*T (n : ℤ)+C a*((T 1-C a)*forward a n) := by ring
      _ = _ := by
        rw [ih,←T_add,pow_succ,map_mul]
        push_cast
        ring

private theorem monQ_identity (a : K) (ha : a ≠ 0) (n : ℤ) :
    (T 1-C a)*monQ a a⁻¹ n = T n-C (a^n) := by
  cases n with
  | ofNat n =>
    change (T 1-C a)*forward a n = T (n : ℤ)-C (a^((n : ℤ)))
    rw [zpow_natCast]
    exact forward_identity a n
  | negSucc n =>
    rw [monQ]
    calc
      _ = -C (a⁻¹^(n+1))*T (-(n+1 : ℤ))*((T 1-C a)*forward a (n+1)) := by ring
      _ = _ := by
        rw [forward_identity]
        have hx : -(n+1 : ℤ)+((n+1 : ℕ) : ℤ)=0 := by omega
        have hu : a⁻¹^(n+1)*a^(n+1)=1 := by
          rw [←mul_pow,inv_mul_cancel₀ ha,one_pow]
        rw [mul_sub]
        have ht : T (-(n+1 : ℤ))*T ((n+1 : ℕ) : ℤ) = (1 : K[T;T⁻¹]) := by
          rw [←T_add,hx,T_zero]
        simp only [zpow_negSucc,←inv_pow]
        rw [show Int.negSucc n = -(n+1 : ℤ) by omega]
        have huL := congrArg (C : K →+* K[T;T⁻¹]) hu
        simp only [map_mul,map_one] at huL
        linear_combination -C (a⁻¹^(n+1))*ht + T (-(n+1 : ℤ))*huL

theorem DD_identity (a : K) (ha : a ≠ 0) (L : K[T;T⁻¹]) :
    (T 1-C a)*DD a a⁻¹ L = L-C (ev a ha L) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM =>
    rw [map_add,mul_add,hL,hM,map_add,map_add]
    ring
  | C_mul_T n c =>
    rw [DD_monomial]
    have hev : ev a ha (C c*T n) = c*a^n := by
      simp [ev,LaurentPolynomial.eval₂_C_mul_T,Units.val_zpow_eq_zpow_val]
    rw [hev,map_mul]
    calc
      _ = C c*((T 1-C a)*monQ a a⁻¹ n) := by ring
      _ = _ := by rw [monQ_identity a ha n]; ring

theorem weightedDD_cleared (h4 : (4 : K) ≠ 0) (L : K[T;T⁻¹]) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * weightedDD L =
      L*(33-12*T 1) + 8*(T 1-4)*C (ev (1/4) (div_ne_zero one_ne_zero h4) L) +
        4*(T 1-C (1/4 : K))*C (ev 4 h4 L) := by
  have hu : (4 : K[T;T⁻¹])*C (1/4 : K)=1 := by
    change C (4 : K)*C (1/4 : K)=C (1 : K)
    rw [←map_mul,mul_one_div_cancel h4]
  have hia : (1/4 : K)⁻¹=4 := by simp [one_div]
  have hib : (4 : K)⁻¹=1/4 := by simp only [one_div]
  have ha := DD_identity (1/4 : K) (div_ne_zero one_ne_zero h4) L
  have hb := DD_identity (4 : K) h4 L
  rw [hia] at ha
  rw [hib] at hb
  simp only [map_ofNat] at hb
  have he : (WPFiniteZSource.Abar : K[X]).toLaurent =
      -4*(T 1-C (1/4 : K))*(T 1-4) := by
    simp only [WPFiniteZSource.Abar,map_mul,map_sub,map_ofNat,map_one,Polynomial.toLaurent_X]
    linear_combination (4-T 1)*hu
  have hl : (33-12*T 1 : K[T;T⁻¹]) =
      -4*(2*(T 1-4)+(T 1-C (1/4 : K))) := by
    linear_combination -hu
  rw [he,hl,weightedDD]
  simp only [map_ofNat]
  linear_combination -8*(T 1-4)*ha -4*(T 1-C (1/4 : K))*hb

end WPFieldAssembly.GreenLaurentOperators
