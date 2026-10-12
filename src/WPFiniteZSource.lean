import WPFiniteLaurentDifferential
import WPFiniteHJPSource
import WPFiniteLVSharp

open scoped Polynomial LaurentPolynomial

namespace WPFiniteZSource

open LaurentPolynomial WPFiniteLaurentDifferential WPFiniteABSourceTail
  WPFiniteWSource WPFinitePSource WPFiniteLVSource WPFiniteJCarrier
  WPFiniteJSource WPFiniteHJPSource WPFiniteLVSharp

variable {K : Type*} [Field K]

noncomputable def Abar : K[X] := (4 - Polynomial.X) * (4 * Polynomial.X - 1)

noncomputable def phase (p : ℕ) : K[T;T⁻¹] := 17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))

/-- All three original Frobenius phases, including the full negative cutoff. -/
noncomputable def P (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[T;T⁻¹] :=
  T (p : ℤ) * (A p (W p) u).toLaurent + (B0 p (W p) u).toLaurent +
    T (-(p : ℤ)) * (Cminus p u).toLaurent

/-- The universal source is itself a finite Laurent polynomial. -/
noncomputable def R (p : ℕ) : K[T;T⁻¹] :=
  C (1 / 2 : K) * T (-(p : ℤ)) * Abar.toLaurent ^ (p - 1) *
    squaredCoordinate.toLaurent ^ ((p - 1) / 2)

/-- Original whole combined source; the invisible coefficient at 2p is retained. -/
noncomputable def Z (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[T;T⁻¹] :=
  -C (1 / 2 : K) * P p u ^ 2 + GJ p

theorem P_numerator (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    T (p : ℤ) * (P p u : K[T;T⁻¹]) = (Pnumerator p u).toLaurent := by
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have ht2 : (T (p : ℤ) * T (p : ℤ) : K[T;T⁻¹]) = T ((2 * p : ℕ) : ℤ) := by
    rw [← T_add]
    congr 1
    omega
  simp only [P, Pnumerator, map_add, map_mul, Polynomial.toLaurent_X_pow]
  linear_combination (A p (W p) u).toLaurent * ht2 + (Cminus p u).toLaurent * ht

theorem Abar_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (_hp : 19 ≤ p) :
    (Abar : K[X]) ^ p = 17 * Polynomial.X ^ p - 4 * Polynomial.X ^ (2 * p) - 4 := by
  have h4 : (4 : K[X]) ^ p = 4 := by
    have hk : (4 : K) ^ p = 4 := by
      simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
    change (Polynomial.C (4 : K)) ^ p = Polynomial.C (4 : K)
    rw [← map_pow, hk]
  rw [Abar, mul_pow, sub_pow_char, sub_pow_char, mul_pow, h4, one_pow]
  rw [show (Polynomial.X : K[X]) ^ (2 * p) = Polynomial.X ^ p * Polynomial.X ^ p by
    rw [← pow_add]; congr 1; omega]
  ring

theorem phase_factorization (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Abar : K[X]).toLaurent ^ p = T (p : ℤ) * phase p := by
  have he := congrArg (fun F : K[X] => F.toLaurent) (Abar_frobenius (K := K) p hp)
  simp only [map_pow, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X, T_pow, mul_one] at he
  rw [he, phase]
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have ht2 : (T (p : ℤ) * T (p : ℤ) : K[T;T⁻¹]) = T ((2 * p : ℕ) : ℤ) := by
    rw [← T_add]; congr 1; omega
  linear_combination 4 * ht2 + 4 * ht

theorem Abar_nonzero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Abar : K[X]).toLaurent ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have he := congrArg (fun F : K[T;T⁻¹] => F.coeff 0) hz
  have he0 : (Abar : K[X]).coeff 0 = 0 := by
    calc
      _ = (Abar : K[X]).toLaurent.coeff (0 : ℤ) := by
        simpa only [Nat.cast_zero] using (toLaurent_coeff_nat (Abar : K[X]) 0).symm
      _ = 0 := by rw [hz]; rfl
  have h0 : (Abar : K[X]).coeff 0 = -4 := by
    simp [Abar, Polynomial.coeff_mul, Polynomial.coeff_X_zero]
  rw [h0] at he0
  exact (neg_ne_zero.mpr h4) he0

theorem R_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Abar : K[X]).toLaurent * R p =
      C (1 / 2 : K) * phase p * squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hpow : (Abar : K[X]).toLaurent ^ (p - 1) * Abar.toLaurent = Abar.toLaurent ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  unfold R
  calc
    _ = C (1 / 2 : K) * T (-(p : ℤ)) *
        (Abar.toLaurent ^ (p - 1) * Abar.toLaurent) *
          squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by ring
    _ = _ := by rw [hpow, phase_factorization p hp];
                linear_combination C (1 / 2 : K) * phase p *
                  squaredCoordinate.toLaurent ^ ((p - 1) / 2) * ht

theorem P_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    D (P p u : K[T;T⁻¹]) = R p - C (1 / 2 : K) * T (-1) := by
  have heps : (epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hpnum : (Abar : K[X]) * ((Pnumerator p u).derivative +
      Polynomial.C (1 / 2 : K) * Polynomial.X ^ (p - 1)) =
      Polynomial.C (1 / (2 * epsilon p)) *
        (17 * Polynomial.X ^ p - 4 * Polynomial.X ^ (2 * p) - 4) *
          (Polynomial.X + 1) ^ ((p - 1) / 2) := Pnumerator_cleared_source p hp u
  have hnum := congrArg (fun F : K[X] => F.toLaurent) hpnum
  have hs := congrArg (fun F : K[X] => F.toLaurent)
    (epsilon_squaredCoordinate_power (K := K) p hp)
  simp only [map_add, map_mul, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, map_sub, map_ofNat, map_one, T_pow, mul_one] at hnum hs
  have hd : (Pnumerator p u).derivative.toLaurent = T (p : ℤ) * D (P p u) := by
    rw [← D_toLaurent, ← P_numerator, D_frobenius_shift p _ _ (dvd_refl _)]
  have he := congrArg (fun F : K[T;T⁻¹] => T (-(p : ℤ)) * F) hnum
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hm : (T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = T (-1) := by
    rw [← T_add]; congr 1; omega
  have hphase : (17 * T (p : ℤ) - 4 * T ((2 * p : ℕ) : ℤ) - 4 : K[T;T⁻¹]) =
      T (p : ℤ) * phase p := by
    rw [← phase_factorization p hp]
    simpa only [map_pow, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X, T_pow, mul_one] using
      (congrArg (fun F : K[X] => F.toLaurent) (Abar_frobenius (K := K) p hp)).symm
  rw [hd, hphase] at he
  have hc : (C (1 / (2 * epsilon p)) * C (epsilon p) : K[T;T⁻¹]) = C (1 / 2 : K) := by
    rw [← map_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    calc
      (epsilon p)⁻¹ * (2 : K)⁻¹ * epsilon p = (2 : K)⁻¹ * ((epsilon p)⁻¹ * epsilon p) := by ring
      _ = _ := by rw [inv_mul_cancel₀ heps, mul_one]
  have hclear : (Abar : K[X]).toLaurent *
      (D (P p u) + C (1 / 2 : K) * T (-1)) =
        C (1 / 2 : K) * phase p * squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
    linear_combination he - C (1 / (2 * epsilon p)) * phase p * hs +
      phase p * squaredCoordinate.toLaurent ^ ((p - 1) / 2) * hc -
      (Abar.toLaurent * D (P p u) -
        C (1 / (2 * epsilon p)) * phase p * (T 1 + 1) ^ ((p - 1) / 2)) * ht -
      C (1 / 2 : K) * Abar.toLaurent * hm
  have hR := R_cleared (K := K) p hp
  have heq : D (P p u) + C (1 / 2 : K) * T (-1) = R p :=
    mul_left_cancel₀ (Abar_nonzero p hp) (hclear.trans hR.symm)
  linear_combination heq

theorem invert_Abar : invert (Abar : K[X]).toLaurent = T (-2) * Abar.toLaurent := by
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have ht2 : (T (-2) : K[T;T⁻¹]) = T (-1) ^ 2 := by rw [T_pow]; norm_num
  simp only [Abar, map_mul, map_sub, map_ofNat, map_one, Polynomial.toLaurent_X, invert_T]
  rw [ht2]
  linear_combination (4 * T (-1) * T 1 + 4 - 17 * T (-1)) * ht

theorem invert_squaredCoordinate :
    invert (squaredCoordinate : K[X]).toLaurent = T (-1) * squaredCoordinate.toLaurent := by
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  simp only [squaredCoordinate, map_mul, map_add, Polynomial.toLaurent_C,
    map_one, Polynomial.toLaurent_X, invert_C, invert_T]
  linear_combination -C (5 : K)⁻¹ * ht

theorem invert_squared_power (p : ℕ) :
    invert ((squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2)) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
  rw [map_pow, invert_squaredCoordinate, mul_pow, T_pow]
  congr 2
  omega

theorem GJ_phase (p : ℕ) : (GJ p : K[T;T⁻¹]) =
    C (1 / 45 : K) * phase p * ((HJP p).toLaurent + invert (HJP p).toLaurent) := by
  simp only [GJ, phase, T_zero, mul_one, div_eq_mul_inv, one_mul, map_mul, map_ofNat]
  ring

theorem phase_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (phase p : K[T;T⁻¹]) = 0 := by
  have hD1 : D (1 : K[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : K)
  have hpos : D (T (p : ℤ) : K[T;T⁻¹]) = 0 := by
    simpa only [mul_one, hD1, mul_zero] using
      D_frobenius_shift p (1 : K[T;T⁻¹]) (p : ℤ) (dvd_refl _)
  have hneg : D (T (-(p : ℤ)) : K[T;T⁻¹]) = 0 := by
    simpa only [mul_one, hD1, mul_zero] using
      D_frobenius_shift p (1 : K[T;T⁻¹]) (-(p : ℤ)) (dvd_neg.mpr (dvd_refl _))
  change D (C (17 : K) - C (4 : K) * T (p : ℤ) - C (4 : K) * T (-(p : ℤ))) = 0
  simp only [map_sub, D_C, D_C_mul, hpos, hneg, mul_zero, sub_zero]

theorem GJ_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    D (GJ p : K[T;T⁻¹]) = C (1 / 3 : K) * R p *
      ((LV p).toLaurent - T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h45 : (45 : K) ≠ 0 := by
    rw [show (45 : K) = 3 ^ 2 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have hc : (C (1 / 45 : K) * C (15 / 2 : K) : K[T;T⁻¹]) = C (1 / 3 : K) * C (1 / 2 : K) := by
    rw [← map_mul, ← map_mul]
    congr 1
    field_simp [h45, h3, h2]
    ring
  have hHp : (Abar : K[X]) * (HJP p).derivative =
      Polynomial.C (15 / 2 : K) * squaredCoordinate ^ ((p - 1) / 2) * LV p :=
    HJP_cleared_source p hp
  have hH := congrArg (fun F : K[X] => F.toLaurent) hHp
  simp only [map_mul, map_pow, Polynomial.toLaurent_C] at hH
  rw [← D_toLaurent] at hH
  have hi := congrArg (fun F : K[T;T⁻¹] => invert F) hH
  simp only [map_mul, invert_C, invert_Abar, invert_squared_power] at hi
  have href : (Abar : K[X]).toLaurent * (T (-2) * invert (D (HJP p).toLaurent)) =
      C (15 / 2 : K) * T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        squaredCoordinate.toLaurent ^ ((p - 1) / 2) * invert (LV p).toLaurent := by
    linear_combination hi
  have hder : D (GJ p : K[T;T⁻¹]) = C (1 / 45 : K) * phase p *
      (D (HJP p).toLaurent - T (-2) * invert (D (HJP p).toLaurent)) := by
    rw [GJ_phase, mul_assoc, D_C_mul, D_mul, phase_derivative, zero_mul, zero_add, map_add, D_invert]
    ring
  apply mul_left_cancel₀ (Abar_nonzero p hp)
  have hR := R_cleared (K := K) p hp
  rw [hder]
  linear_combination C (1 / 45 : K) * phase p * hH - C (1 / 45 : K) * phase p * href -
    C (1 / 3 : K) * ((LV p).toLaurent - T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent) * hR +
    phase p * squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      ((LV p).toLaurent - T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent) * hc

theorem Z_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    D (Z p u : K[T;T⁻¹]) = R p *
      (-P p u + C (1 / 3 : K) * ((LV p).toLaurent -
        T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent)) +
      C (1 / 2 : K) * T (-1) * P p u := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  rw [Z, neg_mul, map_add, map_neg, D_half_square _ h2, P_derivative p hp u, GJ_derivative p hp]
  ring

theorem remainder_phases (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    (LV p).toLaurent - 3 * (P p u : K[T;T⁻¹]) =
      (positiveDifference p u).toLaurent - 3 * T (-(p : ℤ)) * (Cminus p u).toLaurent := by
  simp only [positiveDifference, WPFiniteLVSupport.regularRemainder, P, map_sub, map_mul,
    map_ofNat, Polynomial.toLaurent_X_pow]
  ring

end WPFiniteZSource
