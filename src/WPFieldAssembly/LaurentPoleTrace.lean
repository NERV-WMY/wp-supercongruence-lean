import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial PowerSeries BigOperators
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.LaurentPoleTrace

noncomputable def zcoeff (n : ℤ) : ℚ⟦X⟧ →ₗ[ℚ] ℚ :=
  if 0 ≤ n then PowerSeries.coeff n.toNat else 0

theorem zcoeff_neg (n : ℤ) (hn : n < 0) (F : ℚ⟦X⟧) : zcoeff n F = 0 := by
  simp [zcoeff, not_le.mpr hn]

@[simp] theorem zcoeff_nat (n : ℕ) (F : ℚ⟦X⟧) :
    zcoeff (n : ℤ) F = PowerSeries.coeff n F := by
  simp [zcoeff]

theorem zcoeff_C_mul (n : ℤ) (a : ℚ) (F : ℚ⟦X⟧) :
    zcoeff n (PowerSeries.C a * F) = a * zcoeff n F := by
  by_cases hn : 0 ≤ n
  · simp only [zcoeff, if_pos hn, PowerSeries.coeff_C_mul]
  · simp [zcoeff, hn]

theorem zcoeff_X_mul (n : ℤ) (F : ℚ⟦X⟧) :
    zcoeff n (PowerSeries.X * F) = zcoeff (n-1) F := by
  by_cases hn : 0 < n
  · have h0 : 0 ≤ n := by omega
    have h1 : 0 ≤ n-1 := by omega
    have he : n.toNat = (n-1).toNat+1 := by omega
    simp only [zcoeff, if_pos h0, if_pos h1, he, PowerSeries.coeff_succ_X_mul]
  · by_cases h0 : 0 ≤ n
    · have he : n = 0 := by omega
      subst n
      simp [zcoeff]
    · rw [zcoeff_neg n (by omega), zcoeff_neg (n-1) (by omega)]

noncomputable def reciprocal : ℚ⟦X⟧ :=
  PowerSeries.mk fun k => (4/15 : ℚ)*(4^(k+1)-(1/4 : ℚ)^(k+1))

noncomputable def reversedA : ℚ⟦X⟧ :=
  1 - PowerSeries.C (17/4 : ℚ)*PowerSeries.X + PowerSeries.X^2

theorem reciprocal_identity : reversedA * reciprocal = 1 := by
  apply PowerSeries.ext
  intro n
  have he : reversedA * reciprocal = reciprocal -
      PowerSeries.C (17/4 : ℚ)*(PowerSeries.X*reciprocal)+
      PowerSeries.X*(PowerSeries.X*reciprocal) := by
    unfold reversedA
    ring
  rw [he]
  cases n with
  | zero => norm_num [reciprocal, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    cases n with
    | zero =>
      norm_num [reciprocal, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_one]
    | succ n =>
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, reciprocal, PowerSeries.coeff_mk,
        PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, pow_succ]
      ring

theorem reciprocal_power_identity (m : ℕ) :
    reversedA * reciprocal^(m+1) = reciprocal^m := by
  rw [pow_succ]
  linear_combination reciprocal^m * reciprocal_identity

/-- Each coefficient of the power is obtained by a finite exact convolution. -/
theorem reciprocal_finite_recurrence (m k : ℕ) :
    PowerSeries.coeff k (reciprocal^(m+1)) =
      ∑ q ∈ Finset.antidiagonal k, PowerSeries.coeff q.1 (reciprocal^m) *
        ((4/15 : ℚ)*(4^(q.2+1)-(1/4 : ℚ)^(q.2+1))) := by
  rw [pow_succ, PowerSeries.coeff_mul]
  simp only [reciprocal, PowerSeries.coeff_mk]

theorem reciprocal_coeff_recurrence (m : ℕ) (k : ℤ) :
    zcoeff k (reciprocal^(m+1)) -
      (17/4 : ℚ)*zcoeff (k-1) (reciprocal^(m+1)) +
      zcoeff (k-2) (reciprocal^(m+1)) = zcoeff k (reciprocal^m) := by
  have he : reversedA * reciprocal^(m+1) = reciprocal^(m+1) -
      PowerSeries.C (17/4 : ℚ)*(PowerSeries.X*reciprocal^(m+1)) +
      PowerSeries.X*(PowerSeries.X*reciprocal^(m+1)) := by
    unfold reversedA
    ring
  have h := congrArg (zcoeff k) (reciprocal_power_identity m)
  rw [he, map_add, map_sub, zcoeff_C_mul, zcoeff_X_mul, zcoeff_X_mul,
    zcoeff_X_mul, show k-1-1=k-2 by omega] at h
  exact h

noncomputable def weight (m : ℕ) (n : ℤ) : ℚ :=
  -(-1/4 : ℚ)^m * zcoeff (n - (2*(m : ℤ)-1)) (reciprocal^m)

/-- The exact coefficient of the expansion at infinity, including negative input powers. -/
noncomputable def trace (m : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ (weight m)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem trace_eq_sum (m : ℕ) (L : ℚ[T;T⁻¹]) :
    trace m L = L.coeff.sum (fun n a => a * weight m n) := by
  change Finsupp.linearCombination ℚ (weight m) L.coeff = _
  rw [Finsupp.linearCombination_apply]
  simp only [smul_eq_mul]

@[simp] theorem trace_monomial (m : ℕ) (a : ℚ) (n : ℤ) :
    trace m (LaurentPolynomial.C a * T n) = a * weight m n := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ (weight m) (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem trace_C_mul (m : ℕ) (a : ℚ) (L : ℚ[T;T⁻¹]) :
    trace m (LaurentPolynomial.C a * L) = a * trace m L := by
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using (trace m).map_smul a L

theorem weight_support (m : ℕ) (n : ℤ) (hn : n < 2*(m : ℤ)-1) :
    weight m n = 0 := by
  rw [weight, zcoeff_neg _ (by omega)]
  ring

theorem trace_monomial_support (m : ℕ) (n : ℤ) (hn : n < 2*(m : ℤ)-1) :
    trace m (T n) = 0 := by
  have h := trace_monomial m 1 n
  simpa [weight_support m n hn] using h

theorem trace_support (m : ℕ) (L : ℚ[T;T⁻¹])
    (hL : ∀ n : ℤ, 2*(m : ℤ)-1 ≤ n → L.coeff n = 0) : trace m L = 0 := by
  rw [trace_eq_sum]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro n _
  change L.coeff n * weight m n = 0
  by_cases hn : n < 2*(m : ℤ)-1
  · rw [weight_support m n hn]
    ring
  · rw [hL n (by omega)]
    ring

theorem weight_zero (n : ℤ) : weight 0 n = if n = -1 then -1 else 0 := by
  unfold weight
  simp only [Nat.cast_zero, mul_zero, zero_sub, sub_neg_eq_add, pow_zero, neg_mul,
    one_mul]
  by_cases hn : 0 ≤ n+1
  · simp only [zcoeff, if_pos hn, PowerSeries.coeff_one]
    have he : (n+1).toNat=0 ↔ n=-1 := by omega
    simp only [he]
    split_ifs <;> ring
  · have he : n ≠ -1 := by omega
    simp [zcoeff, hn, he]

theorem trace_zero (L : ℚ[T;T⁻¹]) : trace 0 L = -L.coeff (-1) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hL, hM]
    ring
  | C_mul_T n a =>
    rw [trace_monomial, weight_zero, ←single_eq_C_mul_T]
    change a * (if n = -1 then -1 else 0) = -(Finsupp.single n a (-1))
    by_cases hn : n = -1 <;> simp [hn, eq_comm]

theorem weight_cleared (m : ℕ) (n : ℤ) :
    -4*weight (m+1) (n+2)+17*weight (m+1) (n+1)-4*weight (m+1) n =
      weight m n := by
  have h := reciprocal_coeff_recurrence m (n-(2*(m : ℤ)-1))
  have h2 : n+2-(2*((m+1 : ℕ) : ℤ)-1)=n-(2*(m : ℤ)-1) := by omega
  have h1 : n+1-(2*((m+1 : ℕ) : ℤ)-1)=n-(2*(m : ℤ)-1)-1 := by omega
  have h0 : n-(2*((m+1 : ℕ) : ℤ)-1)=n-(2*(m : ℤ)-1)-2 := by omega
  have hpow : (-1/4 : ℚ)^(m+1)=(-1/4 : ℚ)^m*(-1/4) := pow_succ _ _
  simp only [weight, h2, h1, h0, hpow]
  linear_combination (-(-1/4 : ℚ)^m)*h

noncomputable def Abar : ℚ[X] := (4*X-1)*(4-X)

theorem Abar_laurent : Abar.toLaurent = -4*T 2+17*T 1-4 := by
  simp only [Abar, map_mul, map_sub, map_ofNat, map_one, Polynomial.toLaurent_X]
  have h2 : (T 2 : ℚ[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
  rw [h2]
  ring

theorem Abar_infinity_coordinate : Abar.toLaurent =
    LaurentPolynomial.C (-4 : ℚ)*T 2*
      (1-LaurentPolynomial.C (17/4 : ℚ)*T (-1)+T (-2)) := by
  have h1 : (T 2 : ℚ[T;T⁻¹])*T (-1)=T 1 := by rw [←T_add]; norm_num
  have h0 : (T 2 : ℚ[T;T⁻¹])*T (-2)=1 := by rw [←T_add]; norm_num
  have hC : LaurentPolynomial.C (-4 : ℚ)*LaurentPolynomial.C (17/4 : ℚ) =
      (-17 : ℚ[T;T⁻¹]) := by
    rw [←map_mul, show (-4 : ℚ)*(17/4)=-17 by norm_num]
    simp only [map_neg, map_ofNat]
  rw [Abar_laurent]
  calc
    _ = LaurentPolynomial.C (-4 : ℚ)*T 2-
        (LaurentPolynomial.C (-4 : ℚ)*LaurentPolynomial.C (17/4 : ℚ))*(T 2*T (-1))+
        LaurentPolynomial.C (-4 : ℚ)*(T 2*T (-2)) := by
      rw [hC, h1, h0]
      simp only [map_neg, map_ofNat]
      ring
    _ = _ := by ring

theorem trace_cleared (m : ℕ) (L : ℚ[T;T⁻¹]) :
    trace (m+1) (Abar.toLaurent * L) = trace m L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [mul_add, map_add, hL, hM]
  | C_mul_T n a =>
    have h2 : (T 2 : ℚ[T;T⁻¹])*T n=T (n+2) := by
      rw [←T_add]
      congr 1
      omega
    have h1 : (T 1 : ℚ[T;T⁻¹])*T n=T (n+1) := by
      rw [←T_add]
      congr 1
      omega
    have he : Abar.toLaurent*(LaurentPolynomial.C a*T n) =
        LaurentPolynomial.C (-4*a)*T (n+2)+
          LaurentPolynomial.C (17*a)*T (n+1)+LaurentPolynomial.C (-4*a)*T n := by
      rw [Abar_laurent]
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination -4*LaurentPolynomial.C a*h2+17*LaurentPolynomial.C a*h1
    rw [he, map_add, map_add, trace_monomial, trace_monomial, trace_monomial,
      trace_monomial]
    linear_combination a*weight_cleared m n

theorem trace_cleared_pow (m k : ℕ) (L : ℚ[T;T⁻¹]) :
    trace (m+k) (Abar.toLaurent^k * L) = trace m L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,
      show Abar.toLaurent^(k+1)*L=Abar.toLaurent*(Abar.toLaurent^k*L) by ring,
      trace_cleared, ih]

/-- Equal fractions with powers of the actual denominator have the same trace. -/
theorem trace_common_denominator (a b : ℕ) (L M : ℚ[T;T⁻¹])
    (h : Abar.toLaurent^b * L = Abar.toLaurent^a * M) :
    trace a L = trace b M := by
  calc
    trace a L = trace (a+b) (Abar.toLaurent^b*L) := (trace_cleared_pow a b L).symm
    _ = trace (a+b) (Abar.toLaurent^a*M) := congrArg (trace (a+b)) h
    _ = trace b M := by
      rw [Nat.add_comm a b]
      exact trace_cleared_pow b a M

theorem weight_one_nat (n : ℕ) :
    weight 1 (n : ℤ) = -((1/4 : ℚ)^n-4^n)/15 := by
  cases n with
  | zero => norm_num [weight, zcoeff]
  | succ n =>
    have hn : ((n+1 : ℕ) : ℤ)-1=(n : ℤ) := by omega
    simp only [weight, pow_one, Nat.cast_one]
    change -(-1/4 : ℚ) * zcoeff (((n+1 : ℕ) : ℤ)-1) reciprocal = _
    rw [hn, zcoeff_nat]
    simp only [reciprocal, PowerSeries.coeff_mk]
    ring

theorem trace_one_polynomial (P : ℚ[X]) :
    trace 1 P.toLaurent = -(P.eval (1/4 : ℚ)-P.eval 4)/15 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ]; ring
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
      trace_monomial, weight_one_nat]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    ring

theorem reversedA_derivative : PowerSeries.derivative ℚ reversedA =
    -PowerSeries.C (17/4 : ℚ)+2*PowerSeries.X := by
  simp [reversedA, Derivation.leibniz, smul_eq_mul]

theorem reciprocal_derivative : PowerSeries.derivative ℚ reciprocal =
    -(PowerSeries.derivative ℚ reversedA)*reciprocal^2 := by
  have h := congrArg (PowerSeries.derivative ℚ) reciprocal_identity
  rw [Derivation.leibniz, PowerSeries.derivative_one] at h
  simp only [smul_eq_mul] at h
  linear_combination reciprocal*h-
    (PowerSeries.derivative ℚ reciprocal)*reciprocal_identity

theorem reciprocal_power_derivative (m : ℕ) :
    PowerSeries.derivative ℚ (reciprocal^m) =
      -PowerSeries.C (m : ℚ)*(PowerSeries.derivative ℚ reversedA)*reciprocal^(m+1) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [PowerSeries.derivative_pow, Nat.add_sub_cancel, reciprocal_derivative]
    have hc : PowerSeries.C ((m+1 : ℕ) : ℚ)=((m+1 : ℕ) : ℚ⟦X⟧) := by simp
    rw [hc]
    simp only [pow_succ]
    ring

theorem zcoeff_X_derivative (k : ℤ) (F : ℚ⟦X⟧) :
    zcoeff k (PowerSeries.X*PowerSeries.derivative ℚ F) = (k : ℚ)*zcoeff k F := by
  by_cases hk : 0 < k
  · have h0 : 0 ≤ k := by omega
    have h1 : 0 ≤ k-1 := by omega
    have he : (k-1).toNat+1=k.toNat := by omega
    have hc : ((k-1).toNat : ℚ)=(k : ℚ)-1 := by
      have h := congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg h1)
      simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_one] using h
    rw [zcoeff_X_mul]
    simp only [zcoeff, if_pos h0, if_pos h1, PowerSeries.coeff_derivative, he, hc]
    ring
  · by_cases h0 : 0 ≤ k
    · have he : k=0 := by omega
      subst k
      simp [zcoeff]
    · rw [zcoeff_neg k (by omega), zcoeff_neg k (by omega)]
      ring

theorem reciprocal_power_coefficient_derivative (m : ℕ) (k : ℤ) :
    (k : ℚ)*zcoeff k (reciprocal^m) =
      (m : ℚ)*((17/4 : ℚ)*zcoeff (k-1) (reciprocal^(m+1))-
        2*zcoeff (k-2) (reciprocal^(m+1))) := by
  have he : PowerSeries.X*PowerSeries.derivative ℚ (reciprocal^m) =
      PowerSeries.C (m : ℚ)*
        (PowerSeries.C (17/4 : ℚ)*(PowerSeries.X*reciprocal^(m+1))-
          PowerSeries.C (2 : ℚ)*(PowerSeries.X*(PowerSeries.X*reciprocal^(m+1)))) := by
    rw [reciprocal_power_derivative, reversedA_derivative]
    simp only [map_ofNat]
    ring
  have h := congrArg (zcoeff k) he
  rw [zcoeff_X_derivative, zcoeff_C_mul, map_sub, zcoeff_C_mul, zcoeff_X_mul,
    zcoeff_C_mul, zcoeff_X_mul, zcoeff_X_mul, show k-1-1=k-2 by omega] at h
  exact h

theorem weight_derivative (m : ℕ) (n : ℤ) :
    (n : ℚ)*weight m (n-1) =
      (m : ℚ)*(-8*weight (m+1) (n+1)+17*weight (m+1) n) := by
  have hD := reciprocal_power_coefficient_derivative m (n-2*(m : ℤ))
  have hC := reciprocal_coeff_recurrence m (n-2*(m : ℤ))
  push_cast at hD
  have h0 : n-1-(2*(m : ℤ)-1)=n-2*(m : ℤ) := by omega
  have h1 : n+1-(2*((m+1 : ℕ) : ℤ)-1)=n-2*(m : ℤ) := by omega
  have h2 : n-(2*((m+1 : ℕ) : ℤ)-1)=n-2*(m : ℤ)-1 := by omega
  have hp : (-1/4 : ℚ)^(m+1)=(-1/4 : ℚ)^m*(-1/4) := pow_succ _ _
  simp only [weight, h0, h1, h2, hp]
  linear_combination (-(-1/4 : ℚ)^m)*hD+
    (2*(m : ℚ)*(-1/4 : ℚ)^m)*hC

theorem D_Abar : WPFiniteLaurentDifferential.D Abar.toLaurent = -8*T 1+17 := by
  have hA : Abar.toLaurent = LaurentPolynomial.C (-4 : ℚ)*T 2+
      LaurentPolynomial.C (17 : ℚ)*T 1+LaurentPolynomial.C (-4 : ℚ)*T 0 := by
    rw [Abar_laurent]
    simp only [map_neg, map_ofNat, T_zero]
    ring
  rw [hA, map_add, map_add, WPFiniteLaurentDifferential.D_monomial,
    WPFiniteLaurentDifferential.D_monomial, WPFiniteLaurentDifferential.D_monomial]
  norm_num [map_neg, map_ofNat]

/-- The residue of the derivative of L/Abar^m vanishes; this includes m=0. -/
theorem trace_D (m : ℕ) (L : ℚ[T;T⁻¹]) :
    trace m (WPFiniteLaurentDifferential.D L) =
      (m : ℚ)*trace (m+1) (L*WPFiniteLaurentDifferential.D Abar.toLaurent) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM =>
    simp only [map_add, add_mul, hL, hM]
    ring
  | C_mul_T n a =>
    have ht : (T n : ℚ[T;T⁻¹])*T 1=T (n+1) := by rw [←T_add]
    have he : (LaurentPolynomial.C a*T n)*WPFiniteLaurentDifferential.D Abar.toLaurent =
        LaurentPolynomial.C (-8*a)*T (n+1)+LaurentPolynomial.C (17*a)*T n := by
      rw [D_Abar]
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination -8*LaurentPolynomial.C a*ht
    rw [WPFiniteLaurentDifferential.D_monomial, he, map_add, trace_monomial,
      trace_monomial, trace_monomial]
    linear_combination a*weight_derivative m n

theorem trace_IBP (m : ℕ) (L M : ℚ[T;T⁻¹]) :
    trace m (L*WPFiniteLaurentDifferential.D M) =
      (m : ℚ)*trace (m+1) (L*M*WPFiniteLaurentDifferential.D Abar.toLaurent)-
        trace m (M*WPFiniteLaurentDifferential.D L) := by
  have h := trace_D m (L*M)
  rw [WPFiniteLaurentDifferential.D_mul, map_add,
    show WPFiniteLaurentDifferential.D L*M=M*WPFiniteLaurentDifferential.D L by ring] at h
  linear_combination h

end WPFieldAssembly.LaurentPoleTrace
