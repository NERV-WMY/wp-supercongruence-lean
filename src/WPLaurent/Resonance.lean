import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace WPLaurent

def RationalCongruent (p m : ℕ) (a b : ℚ) : Prop :=
  a = b ∨ (m : ℤ) ≤ padicValRat p (a - b)

def AllowedMultiplier (b : ℤ) : Prop :=
  b = -5 ∨ b = -3 ∨ b = -1 ∨ b = 1 ∨ b = 3 ∨ b = 5

def fermatQuotient4 (p : ℕ) : ℚ := ((4 : ℚ) ^ (p - 1) - 1) / (p : ℚ)

def resonantWeight (p : ℕ) (b : ℤ) : ℚ :=
  (p : ℚ) * (1 - (4 : ℚ) ^ (-(b * (p : ℤ)))) / ((b * (p : ℤ) : ℤ) : ℚ)

def resonantExpansion (p : ℕ) (b : ℤ) : ℚ :=
  (1 - (4 : ℚ) ^ (-b)) / (b : ℚ) +
    (p : ℚ) * (4 : ℚ) ^ (-b) * fermatQuotient4 p -
    ((p : ℚ) ^ 2 / 2) * ((b : ℚ) + 1) * (4 : ℚ) ^ (-b) * fermatQuotient4 p ^ 2

private theorem smallNat_unit (p n : ℕ) (hn : 0 < n) (hnp : n < p) :
    padicValRat p (n : ℚ) = 0 := by
  have hnd : ¬p ∣ n := by
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Int.natCast_zero]

theorem four_unit (p : ℕ) (hp7 : 7 ≤ p) : padicValRat p (4 : ℚ) = 0 := by
  exact smallNat_unit p 4 (by norm_num) (by omega)

theorem allowedMultiplier_nonzero (b : ℤ) (hb : AllowedMultiplier b) : b ≠ 0 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem allowedMultiplier_unit (p : ℕ) (hp7 : 7 ≤ p) (b : ℤ)
    (hb : AllowedMultiplier b) : padicValRat p (b : ℚ) = 0 := by
  have h1 := smallNat_unit p 1 (by norm_num) (by omega)
  have h3 := smallNat_unit p 3 (by norm_num) (by omega)
  have h5 := smallNat_unit p 5 (by norm_num) (by omega)
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num only [Int.cast_neg, Int.cast_ofNat, padicValRat.neg] <;> assumption

theorem fermatQuotient4_integer (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ k : ℤ, fermatQuotient4 p = (k : ℚ) := by
  have hnd : ¬p ∣ 4 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  have hc : Nat.Coprime 4 p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hci : IsCoprime (4 : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨k, hk⟩ := Int.prime_dvd_pow_sub_one hp hci
  refine ⟨k, ?_⟩
  have hkq : (4 : ℚ) ^ (p - 1) - 1 = (p : ℚ) * (k : ℚ) := by
    exact_mod_cast hk
  unfold fermatQuotient4
  rw [hkq]
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp

theorem fermatQuotient4_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    0 ≤ padicValRat p (fermatQuotient4 p) := by
  obtain ⟨k, hk⟩ := fermatQuotient4_integer p hp hp7
  rw [hk, padicValRat.of_int]
  exact Int.natCast_nonneg _

theorem fermatQuotient4_identity (p : ℕ) (hp : p.Prime) :
    1 + (p : ℚ) * fermatQuotient4 p = (4 : ℚ) ^ (p - 1) := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold fermatQuotient4
  field_simp
  ring

theorem fermatUnit_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    padicValRat p (1 + (p : ℚ) * fermatQuotient4 p) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [fermatQuotient4_identity p hp, padicValRat.pow, four_unit p hp7]
  ring

theorem resonantWeight_rewrite (p : ℕ) (hp : p.Prime) (b : ℤ)
    (hb : AllowedMultiplier b) :
    resonantWeight p b =
      (1 - (4 : ℚ) ^ (-b) * (1 + (p : ℚ) * fermatQuotient4 p) ^ (-b)) /
        (b : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (allowedMultiplier_nonzero b hb)
  have hexp : -(b * (p : ℤ)) = -b + ((p - 1 : ℕ) : ℤ) * (-b) := by
    have hp1 := hp.one_lt
    have hcast : (p : ℤ) = ((p - 1 : ℕ) : ℤ) + 1 := by omega
    rw [hcast]
    ring
  have hpow : (4 : ℚ) ^ (-(b * (p : ℤ))) =
      (4 : ℚ) ^ (-b) * ((4 : ℚ) ^ (p - 1)) ^ (-b) := by
    rw [← zpow_natCast (4 : ℚ) (p - 1), ← zpow_mul, ← zpow_add₀ (by norm_num), hexp]
  unfold resonantWeight
  rw [hpow, ← fermatQuotient4_identity p hp]
  push_cast
  field_simp

private def binomialTail (b : ℤ) (u : ℚ) : ℚ :=
  if b = -5 then 10 + 5*u + u^2 else
  if b = -3 then 1 else
  if b = -1 then 0 else
  if b = 1 then -(1+u)⁻¹ else
  if b = 3 then -(10 + 15*u + 6*u^2)/(1+u)^3 else
  -(35 + 105*u + 126*u^2 + 70*u^3 + 15*u^4)/(1+u)^5

private theorem finite_binomial_residual (b : ℤ) (hb : AllowedMultiplier b)
    (u : ℚ) (hu : 1 + u ≠ 0) :
    (1 + u) ^ (-b) - (1 - (b : ℚ)*u + ((b : ℚ)*((b : ℚ)+1)/2)*u^2) =
      u^3 * binomialTail b u := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [binomialTail, zpow_neg] <;> field_simp <;> ring

private theorem integral_int (p : ℕ) (k : ℤ) : 0 ≤ padicValRat p (k : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

private theorem integral_mul (p : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x*y) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  rw [padicValRat.mul hx0 hy0]
  omega

private theorem integral_div_unit (p : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : padicValRat p y = 0) :
    0 ≤ padicValRat p (x/y) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [div_eq_mul_inv]
  apply integral_mul p hp x y⁻¹ hx
  rw [padicValRat.inv, hy]
  norm_num

private theorem binomialTail_integral (p : ℕ) (hp : p.Prime) (b : ℤ)
    (hb : AllowedMultiplier b) (k : ℤ) (hu : padicValRat p (1 + (k : ℚ)) = 0) :
    0 ≤ padicValRat p (binomialTail b (k : ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have h5 := integral_int p (10 + 5*k + k^2)
  have h3 := integral_int p (10 + 15*k + 6*k^2)
  have hpos5 := integral_int p (35 + 105*k + 126*k^2 + 70*k^3 + 15*k^4)
  push_cast at h5 h3 hpos5
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [binomialTail] using h5
  · simp [binomialTail]
  · simp [binomialTail]
  · norm_num only [binomialTail]
    simp only [ite_false, ite_true]
    rw [padicValRat.neg, padicValRat.inv, hu]
    norm_num
  · norm_num only [binomialTail]
    apply integral_div_unit p hp
    · simpa only [padicValRat.neg] using h3
    · rw [padicValRat.pow, hu]
      ring
  · norm_num only [binomialTail]
    apply integral_div_unit p hp
    · simpa only [padicValRat.neg] using hpos5
    · rw [padicValRat.pow, hu]
      ring

private theorem cube_mul_integral (p : ℕ) (hp : p.Prime) (x : ℚ)
    (hx : 0 ≤ padicValRat p x) : RationalCongruent p 3 ((p : ℚ)^3*x) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx0 : x = 0
  · exact Or.inl (by simp [hx0])
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  apply Or.inr
  rw [sub_zero, padicValRat.mul (pow_ne_zero _ hpq) hx0,
    padicValRat.pow, padicValRat.self hp.one_lt]
  norm_num
  omega

theorem literal_resonant_kernel (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : ℤ) (hb : AllowedMultiplier b) :
    RationalCongruent p 3 (resonantWeight p b) (resonantExpansion p b) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := fermatQuotient4_integer p hp hp7
  have hU : 1 + (p : ℚ)*fermatQuotient4 p ≠ 0 := by
    rw [fermatQuotient4_identity p hp]
    positivity
  have hres := finite_binomial_residual b hb ((p : ℚ)*fermatQuotient4 p) hU
  have hunit := fermatUnit_unit p hp hp7
  have htail : 0 ≤ padicValRat p (binomialTail b ((p : ℚ)*fermatQuotient4 p)) := by
    rw [hk]
    have hcast : (p : ℚ)*(k : ℚ) = (((p : ℤ)*k : ℤ) : ℚ) := by push_cast; rfl
    rw [hcast]
    apply binomialTail_integral p hp b hb
    simpa only [hk, hcast] using hunit
  have hfactor : resonantWeight p b - resonantExpansion p b =
      (p : ℚ)^3 * (-(4 : ℚ)^(-b)/(b : ℚ) * fermatQuotient4 p^3 *
        binomialTail b ((p : ℚ)*fermatQuotient4 p)) := by
    rw [resonantWeight_rewrite p hp b hb]
    unfold resonantExpansion
    have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (allowedMultiplier_nonzero b hb)
    rw [show (1 + (p : ℚ)*fermatQuotient4 p)^(-b) =
      1 - (b : ℚ)*((p : ℚ)*fermatQuotient4 p) +
        ((b : ℚ)*((b : ℚ)+1)/2)*((p : ℚ)*fermatQuotient4 p)^2 +
        ((p : ℚ)*fermatQuotient4 p)^3 * binomialTail b ((p : ℚ)*fermatQuotient4 p)
      by linear_combination hres]
    field_simp
    ring
  have hbase : 0 ≤ padicValRat p (-(4 : ℚ)^(-b)/(b : ℚ)) := by
    apply integral_div_unit p hp
    · rw [padicValRat.neg, padicValRat.zpow, four_unit p hp7]
      norm_num
    · exact allowedMultiplier_unit p hp7 b hb
  have hk3 : 0 ≤ padicValRat p (fermatQuotient4 p^3) := by
    rw [padicValRat.pow]
    have := fermatQuotient4_integral p hp hp7
    omega
  have hint := integral_mul p hp _ _ (integral_mul p hp _ _ hbase hk3) htail
  have h := cube_mul_integral p hp _ hint
  unfold RationalCongruent at h ⊢
  rw [← sub_eq_zero]
  rw [hfactor]
  simpa only [sub_zero] using h

theorem literal_resonant_kernel_expanded (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : ℤ) (hb : AllowedMultiplier b) :
    RationalCongruent p 3
      ((p : ℚ) * (1 - (4 : ℚ) ^ (-(b * (p : ℤ)))) / ((b * (p : ℤ) : ℤ) : ℚ))
      ((1 - (4 : ℚ) ^ (-b)) / (b : ℚ) +
        (p : ℚ) * (4 : ℚ) ^ (-b) * fermatQuotient4 p -
        ((p : ℚ) ^ 2 / 2) * ((b : ℚ) + 1) * (4 : ℚ) ^ (-b) * fermatQuotient4 p ^ 2) := by
  exact literal_resonant_kernel p hp hp7 b hb

end WPLaurent
