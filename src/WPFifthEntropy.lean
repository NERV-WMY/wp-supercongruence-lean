import WPFiniteField
import WPFiniteEntropy
import WPFiniteFieldLog
import Mathlib.NumberTheory.Zsqrtd.Basic

open scoped BigOperators

namespace WPFifthEntropy

private def realHom : Zsqrtd 5 →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- An integral divided binomial polynomial, before reduction in any field. -/
def traceEntropy (p : ℕ) (a : ℤ) : Zsqrtd 5 :=
  -(∑ j ∈ Finset.Ico 1 p,
    (((Nat.choose p j : ℤ) / (p : ℤ) : ℤ) : Zsqrtd 5) *
      (5 : Zsqrtd 5) ^ (p - j) * ((a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ j)

def B (p : ℕ) (a : ℤ) : ℤ := (traceEntropy p a).re

def T (p : ℕ) (a : ℤ) : ℤ :=
  (((5 : Zsqrtd 5) + (a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ p).re

private theorem odd_root_power_real (p : ℕ) (hp : Odd p) (a : ℤ) :
    (((a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ p).re = 0 := by
  obtain ⟨n, hn⟩ := hp
  have hp' : p = 2 * n + 1 := by omega
  have heven : ((a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ (2 * n) =
      (((a ^ 2 * 5 : ℤ) ^ n : ℤ) : Zsqrtd 5) := by
    rw [pow_mul, mul_pow,
      show (Zsqrtd.sqrtd : Zsqrtd 5) ^ 2 = 5 by simp [pow_two, Zsqrtd.dmuld]]
    norm_cast
  rw [hp', pow_add, heven, pow_one]
  simp only [Zsqrtd.re_smul, Zsqrtd.re_sqrtd, mul_zero]

theorem trace_exact (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (a : ℤ) :
    T p a = (5 : ℤ) ^ p - (p : ℤ) * B p a := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hbin := add_pow ((a : Zsqrtd 5) * Zsqrtd.sqrtd) (5 : Zsqrtd 5) p
  rw [Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, mul_one, Nat.choose_self, Nat.sub_self] at hbin
  have hsum : (∑ j ∈ Finset.Ico 1 p,
      ((a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ j * 5 ^ (p - j) *
        (Nat.choose p j : Zsqrtd 5)) = -(p : Zsqrtd 5) * traceEntropy p a := by
    unfold traceEntropy
    simp only [mul_neg, neg_mul, neg_neg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by omega) hj'.2
    have he := Int.mul_ediv_cancel' hd
    have he' := congrArg (fun z : ℤ => (z : Zsqrtd 5)) he
    push_cast at he'
    linear_combination
      -(((a : Zsqrtd 5) * Zsqrtd.sqrtd) ^ j * 5 ^ (p - j)) * he'
  rw [hsum] at hbin
  have hr := congrArg Zsqrtd.re hbin
  rw [add_comm ((a : Zsqrtd 5) * Zsqrtd.sqrtd) 5] at hr
  have h5cast : (5 : Zsqrtd 5) ^ p = (((5 : ℤ) ^ p : ℤ) : Zsqrtd 5) := by norm_cast
  have hpcast : (p : Zsqrtd 5) = ((p : ℤ) : Zsqrtd 5) := by simp
  simp only [Nat.sub_zero] at hr
  rw [h5cast, hpcast] at hr
  simpa only [T, B, Zsqrtd.re_add, Zsqrtd.re_neg,
    Zsqrtd.re_intCast, Zsqrtd.re_smul, neg_mul,
    odd_root_power_real p hodd a, add_zero, sub_eq_add_neg] using hr

theorem trace_cubic (p : ℕ) :
    (40 : ℤ) ^ p * T p 2 = 4 * (T p 1) ^ 3 - 3 * (20 : ℤ) ^ p * T p 1 := by
  let z : Zsqrtd 5 := 5 + Zsqrtd.sqrtd
  have hz : z ^ 3 = 40 * (5 + 2 * Zsqrtd.sqrtd) := by
    ext <;> norm_num [z, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hn : Zsqrtd.norm (z ^ p) = (20 : ℤ) ^ p := by
    change (Zsqrtd.normMonoidHom (d := 5)) (z ^ p) = (20 : ℤ) ^ p
    rw [map_pow]
    change (Zsqrtd.norm z) ^ p = (20 : ℤ) ^ p
    congr 1
  have hc : ((z ^ p) ^ 3).re =
      4 * ((z ^ p).re) ^ 3 - 3 * Zsqrtd.norm (z ^ p) * (z ^ p).re := by
    simp only [pow_succ, pow_zero, one_mul, Zsqrtd.re_mul, Zsqrtd.im_mul,
      Zsqrtd.norm_def]
    ring
  have hh := congrArg (fun w : Zsqrtd 5 => w ^ p) hz
  rw [mul_pow, ← pow_mul, Nat.mul_comm 3 p, pow_mul] at hh
  have hh' := congrArg Zsqrtd.re hh
  have h40cast : (40 : Zsqrtd 5) ^ p = (((40 : ℤ) ^ p : ℤ) : Zsqrtd 5) := by norm_cast
  rw [hc, hn, h40cast, Zsqrtd.re_smul] at hh'
  simpa [T, z] using hh'.symm

private theorem square_zero_cubic {A : Type*} [CommRing A]
    (P q k b1 b2 : A) (hP : P ^ 2 = 0)
    (hc : 2 * (1 + P * q) ^ 3 * (5 * (1 + P * k)) * (5 * (1 + P * k) - P * b2) =
      (5 * (1 + P * k) - P * b1) ^ 3 -
        3 * (1 + P * q) ^ 2 * (5 * (1 + P * k)) * (5 * (1 + P * k) - P * b1)) :
    5 * P * (2 * b2 - 12 * b1 - 60 * q + 25 * k) = 0 := by
  have h3 : P ^ 3 = 0 := by rw [pow_succ, hP, zero_mul]
  have h4 : P ^ 4 = 0 := by rw [pow_succ, h3, zero_mul]
  have h5 : P ^ 5 = 0 := by rw [pow_succ, h4, zero_mul]
  ring_nf at hc
  simp only [hP, h3, h4, h5, zero_mul, add_zero] at hc
  linear_combination -hc

theorem trace_cubic_divisibility (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (p : ℤ) ∣ 5 * (2 * B p 2 - 12 * B p 1 -
      60 * WPFiniteInversion.integerFermatQuotient p 2 +
        25 * WPFiniteInversion.integerFermatQuotient p 5) := by
  let q := WPFiniteInversion.integerFermatQuotient p 2
  let k := WPFiniteInversion.integerFermatQuotient p 5
  have hprime : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using htwo)
  have hk := WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using hfive)
  have h2pow : (2 : ℤ) ^ p = 2 * (1 + (p : ℤ) * q) := by
    calc
      (2 : ℤ) ^ p = (2 : ℤ) ^ (p - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -2 * hq
  have h5pow : (5 : ℤ) ^ p = 5 * (1 + (p : ℤ) * k) := by
    calc
      (5 : ℤ) ^ p = (5 : ℤ) ^ (p - 1) * 5 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by linear_combination -5 * hk
  have h40pow : (40 : ℤ) ^ p = 8 * (1 + (p : ℤ) * q) ^ 3 * 5 ^ p := by
    rw [show (40 : ℤ) = 2 ^ 3 * 5 by norm_num, mul_pow, ← pow_mul,
      Nat.mul_comm 3 p, pow_mul, h2pow]
    ring
  have h20pow : (20 : ℤ) ^ p = 4 * (1 + (p : ℤ) * q) ^ 2 * 5 ^ p := by
    rw [show (20 : ℤ) = 2 ^ 2 * 5 by norm_num, mul_pow, ← pow_mul,
      Nat.mul_comm 2 p, pow_mul, h2pow]
    ring
  have hc := trace_cubic p
  rw [trace_exact p hp 2, trace_exact p hp 1, h40pow, h20pow] at hc
  have hc' : 2 * (1 + (p : ℤ) * q) ^ 3 * 5 ^ p * (5 ^ p - (p : ℤ) * B p 2) =
      (5 ^ p - (p : ℤ) * B p 1) ^ 3 -
        3 * (1 + (p : ℤ) * q) ^ 2 * 5 ^ p * (5 ^ p - (p : ℤ) * B p 1) := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination hc
  rw [h5pow] at hc'
  have hcZ := congrArg (fun z : ℤ => (z : ZMod (p ^ 2))) hc'
  push_cast at hcZ
  have hP : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hzero := square_zero_cubic (p : ZMod (p ^ 2)) (q : ZMod (p ^ 2))
    (k : ZMod (p ^ 2)) (B p 1 : ZMod (p ^ 2)) (B p 2 : ZMod (p ^ 2)) hP hcZ
  have hz : (((p : ℤ) * (5 * (2 * B p 2 - 12 * B p 1 - 60 * q + 25 * k)) : ℤ) :
      ZMod (p ^ 2)) = 0 := by
    push_cast
    linear_combination hzero
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨z, hz'⟩ := hd
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ (by exact_mod_cast hprime.ne_zero : (p : ℤ) ≠ 0)
  simpa only [Nat.cast_pow, pow_two, Nat.cast_mul, mul_assoc] using hz'

section Field

variable {K : Type*} [Field K]

private theorem divided_choose_field (p j : ℕ) [Fact p.Prime] [CharP K p]
    (hj : j ∈ Finset.Ico 1 p) :
    (((Nat.choose p j : ℤ) / (p : ℤ) : ℤ) : K) = (-1) ^ (j - 1) / (j : K) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.divided_choose_cast p j hj)
  simpa only [map_intCast, map_div₀, map_pow, map_neg, map_one, map_natCast] using h

private theorem trace_evaluation (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : ℤ) (u : K) (hu : (5 * u) * (5 * u) = ((5 : ℤ) : K)) :
    Zsqrtd.lift ⟨5 * u, hu⟩ (traceEntropy p a) =
      (5 : K) ^ p * WPFiniteField.ell p (-((a : K) * u)) := by
  let f : Zsqrtd 5 →+* K := Zsqrtd.lift ⟨5 * u, hu⟩
  have hv : f Zsqrtd.sqrtd = 5 * u := by simp [f, Zsqrtd.lift_apply_apply]
  change f (traceEntropy p a) = _
  simp only [traceEntropy, map_neg, map_sum, map_mul, map_pow, map_intCast,
    map_ofNat, hv, WPFiniteField.ell]
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hpow : (5 : K) ^ (p - j) * 5 ^ j = 5 ^ p := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hsign : (-1 : K) ^ j = -(-1) ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    ring
  rw [divided_choose_field p j hj,
    show (a : K) * (5 * u) = 5 * ((a : K) * u) by ring, mul_pow]
  rw [neg_pow ((a : K) * u), hsign]
  calc
    _ = (5 ^ (p - j) * 5 ^ j) *
        (-(-1 : K) ^ (j - 1) * ((a : K) * u) ^ j / (j : K)) := by ring
    _ = _ := by rw [hpow]

theorem B_evaluation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (a : ℤ) (u : K) (hu : u ^ 2 = 1 / 5) :
    (B p a : K) = (5 : K) ^ p * WPFiniteField.E p ((a : K) * u) := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have hv : (5 * u) * (5 * u) = ((5 : ℤ) : K) := by
    norm_num only [Int.cast_ofNat]
    calc
      _ = 25 * u ^ 2 := by ring
      _ = 5 := by rw [hu]; field_simp [hfive]; ring
  have hvneg : (5 * -u) * (5 * -u) = ((5 : ℤ) : K) := by linear_combination hv
  have ha := trace_evaluation p a u hv
  have hb := trace_evaluation p a (-u) hvneg
  have hreal : (B p a : K) * 2 =
      Zsqrtd.lift ⟨5 * u, hv⟩ (traceEntropy p a) +
        Zsqrtd.lift ⟨5 * -u, hvneg⟩ (traceEntropy p a) := by
    simp only [B, Zsqrtd.lift_apply_apply]
    ring
  have hE : WPFiniteField.E p ((a : K) * u) * 2 =
      WPFiniteField.ell p ((a : K) * u) + WPFiniteField.ell p (-((a : K) * u)) :=
    div_mul_cancel₀ _ htwo
  rw [ha, hb, show -((a : K) * -u) = (a : K) * u by ring] at hreal
  apply mul_right_cancel₀ htwo
  linear_combination hreal - 5 ^ p * hE

/-- The actual cubic entropy endpoint equation, with exact Fermat quotients. -/
theorem E_double_cubic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.E p (2 * u) = 6 * WPFiniteField.E p u +
      6 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  obtain ⟨z, hz⟩ := trace_cubic_divisibility p hp
  have hzK := congrArg (fun n : ℤ => (n : K)) hz
  push_cast at hzK
  rw [CharP.cast_eq_zero K p, zero_mul] at hzK
  have hzero := (mul_eq_zero.mp hzK).resolve_left hfive
  have h5pow : (5 : K) ^ p = 5 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (5 : ZMod p))
    simpa only [map_pow, map_ofNat] using he
  rw [B_evaluation p hp 1 u hu, B_evaluation p hp 2 u hu, h5pow] at hzero
  norm_num only [Int.cast_one, Int.cast_ofNat, one_mul] at hzero
  have hred : 2 * WPFiniteField.E p (2 * u) - 12 * WPFiniteField.E p u -
      12 * (WPFiniteInversion.integerFermatQuotient p 2 : K) +
        5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) = 0 := by
    apply mul_left_cancel₀ hfive
    linear_combination hzero
  apply mul_right_cancel₀ htwo
  rw [sub_mul, add_mul, div_mul_cancel₀ _ htwo]
  linear_combination hred

theorem ell_square_even_odd (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : K) : WPFiniteField.E p x + x ^ p * WPFiniteField.O p x =
      WPFiniteField.ell p (x ^ 2) / 2 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hd := WPFiniteField.ell_quadratic_distribution p hodd x
  have hE : WPFiniteField.E p x * 2 = WPFiniteField.ell p x + WPFiniteField.ell p (-x) :=
    div_mul_cancel₀ _ htwo
  have hO : WPFiniteField.O p x * 2 = WPFiniteField.ell p x - WPFiniteField.ell p (-x) :=
    div_mul_cancel₀ _ htwo
  apply mul_right_cancel₀ htwo
  rw [add_mul, div_mul_cancel₀ _ htwo]
  linear_combination hE + x ^ p * hO - hd

theorem fifth_norm_equation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.E p u + u ^ p * WPFiniteField.O p u =
      (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
        4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  rw [ell_square_even_odd p hp, hu, WPFiniteField.ell_one_fifth_eq_fermat p hp]
  field_simp [htwo, hfive]
  ring

theorem double_fifth_norm_equation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.E p (2 * u) + 2 * u ^ p * WPFiniteField.O p (2 * u) =
      (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
        4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h2pow : (2 * u) ^ p = 2 * u ^ p := by
    have h2 : (2 : K) ^ p = 2 := by
      simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
    rw [mul_pow, h2]
  have hsquare : (2 * u) ^ 2 = 1 - 1 / 5 := by
    rw [mul_pow, hu]
    field_simp [hfive]
    ring
  have he := ell_square_even_odd p hp (2 * u)
  rw [h2pow, hsquare, WPFiniteField.ell_reflection p (by omega : 3 ≤ p) (1 / 5),
    WPFiniteField.ell_one_fifth_eq_fermat p hp] at he
  rw [he]
  field_simp [htwo, hfive]
  ring

/-- The genuine fifth entropy difference; it is not assigned a target value. -/
def C (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  WPFiniteField.E p (2 * u) - WPFiniteField.E p u

theorem E_at_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.E p u = (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
      6 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5 + C p u / 5 := by
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have he := E_double_cubic p hp u hu
  apply mul_right_cancel₀ hfive
  rw [add_mul, sub_mul, div_mul_cancel₀ _ hfive, div_mul_cancel₀ _ hfive]
  unfold C
  linear_combination -he

theorem E_at_double_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    WPFiniteField.E p (2 * u) = WPFiniteField.E p u + C p u := by
  unfold C
  ring

private theorem fifth_frobenius_square (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (hu : u ^ 2 = 1 / 5) : (u ^ p) ^ 2 = 1 / 5 := by
  have h5 : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 5)
  calc
    _ = (u ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2]
    _ = (1 / 5 : K) ^ p := by rw [hu]
    _ = 1 / 5 := by rw [div_pow, one_pow, h5]

private theorem fifth_nonzero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) : u ≠ 0 := by
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hn : (1 : K) / 5 ≠ 0 := div_ne_zero one_ne_zero hfive
  apply hn
  rw [← hu, hz]
  norm_num

theorem O_at_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.O p u = u ^ p *
      (2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) - C p u) := by
  have hup : u ^ p ≠ 0 := pow_ne_zero _ (fifth_nonzero p hp u hu)
  have he := fifth_norm_equation p hp u hu
  rw [E_at_fifth p hp u hu] at he
  apply mul_left_cancel₀ hup
  rw [← mul_assoc, ← pow_two, fifth_frobenius_square p u hu]
  linear_combination he

theorem O_at_double_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteField.O p (2 * u) = u ^ p *
      ((WPFiniteInversion.integerFermatQuotient p 2 : K) - 3 * C p u) := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h5inv : (5 : K)⁻¹ * 5 = 1 := inv_mul_cancel₀ hfive
  have hup : u ^ p ≠ 0 := pow_ne_zero _ (fifth_nonzero p hp u hu)
  have he := double_fifth_norm_equation p hp u hu
  rw [E_at_double_fifth, E_at_fifth p hp u hu] at he
  have hphase : (2 * u ^ p) * u ^ p = (2 : K) / 5 := by
    calc
      _ = 2 * (u ^ p) ^ 2 := by ring
      _ = 2 / 5 := by rw [fifth_frobenius_square p u hu]; ring
  apply mul_left_cancel₀ (mul_ne_zero htwo hup)
  rw [← mul_assoc, hphase]
  linear_combination he + C p u * h5inv

end Field

end WPFifthEntropy
