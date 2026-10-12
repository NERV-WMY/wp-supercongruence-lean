import WPResidueFrobenius.Specialization
import WPTruncationArithmetic.Valuation

noncomputable section

namespace WPResidueFrobenius

/-- The signed scalar multiplying the factorial generator in the raw pullback. -/
def pullbackScalar (p r k : ℕ) : ℚ :=
  (-1 : ℚ)^k * (p : ℚ)^(5+k) * ((r+k-1).factorial : ℚ) /
    ((k.factorial : ℚ) * ((p*(r+k)-1).factorial : ℚ))

theorem pullbackScalar_ne_zero (p r k : ℕ) (hp : p.Prime) :
    pullbackScalar p r k ≠ 0 := by
  unfold pullbackScalar
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
      (by exact_mod_cast Nat.factorial_ne_zero _))
    (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
      (by exact_mod_cast Nat.factorial_ne_zero _))

theorem pole_index_div (p r k : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    (p*(r+k)-1)/p = r+k-1 := by
  have hsub : r+k-1+1 = r+k := by omega
  have hmul : (r+k-1)*p+p = p*(r+k) := by
    calc
      _ = (r+k-1+1)*p := by ring
      _ = p*(r+k) := by rw [hsub]; ring
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [hsub, Nat.mul_comm (r+k) p]
    exact Nat.sub_lt (Nat.mul_pos hp (by omega)) (by decide)

theorem pullbackScalar_valuation (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    padicValRat p (pullbackScalar p r k) =
      6 - (r : ℤ) - (WPTruncationArithmetic.factorialValuation p k : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : (-1 : ℚ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpw : (p : ℚ)^(5+k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have ha : ((r+k-1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hb : ((p*(r+k)-1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [pullbackScalar, padicValRat.div (mul_ne_zero (mul_ne_zero hs hpw) ha)
    (mul_ne_zero hk hb), padicValRat.mul (mul_ne_zero hs hpw) ha,
    padicValRat.mul hs hpw, padicValRat.mul hk hb]
  simp only [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero,
    padicValRat.self hp.one_lt, mul_one, padicValRat.of_nat]
  have hrec := WPTruncationArithmetic.factorial_valuation_recursion p (p*(r+k)-1) hp
  rw [pole_index_div p r k hp.pos hr] at hrec
  change 0 + (5+k : ℕ) + (WPTruncationArithmetic.factorialValuation p (r+k-1) : ℤ) -
    ((WPTruncationArithmetic.factorialValuation p k : ℤ) +
      (WPTruncationArithmetic.factorialValuation p (p*(r+k)-1) : ℤ)) = _
  rw [hrec]
  push_cast
  have hcast : ((r+k-1 : ℕ) : ℤ) = (r : ℤ)+k-1 := by omega
  rw [hcast]
  omega

def pullbackGain (r k : ℕ) : ℕ := (r+k-6)/5

theorem pullbackGain_is_closed_gain (p r k : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    (((p*(r+k)-1)/p)-5)/5 = pullbackGain r k := by
  rw [pole_index_div p r k hp hr]
  simp [pullbackGain, Nat.sub_sub]

theorem pullbackGain_lower (r k : ℕ) :
    (r : ℤ)+(k : ℤ)-10 ≤ 5*(pullbackGain r k : ℤ) := by
  have hm := Nat.mod_lt (r+k-6) (by decide : 0 < 5)
  have hd := Nat.div_add_mod (r+k-6) 5
  dsimp [pullbackGain]
  omega

theorem factorial_valuation_bound (p k d : ℕ) (hp : p.Prime)
    (hd : d+1 ≤ p) (hk : 1 ≤ k) :
    (d : ℚ) * WPTruncationArithmetic.factorialValuation p k ≤ (k : ℚ)-1 := by
  have h := WPTruncationArithmetic.factorial_valuation_growth p k hp hk
  have hpQ : (d : ℚ)+1 ≤ p := by exact_mod_cast hd
  have hpos : (0 : ℚ) < (p : ℚ)-1 := by
    have hx : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hx := (le_div_iff₀ hpos).mp h
  have hv : (0 : ℚ) ≤ WPTruncationArithmetic.factorialValuation p k := by positivity
  nlinarith

theorem pullback_gain_lower_seven (p r k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ((k : ℚ)-24*r+125)/30 ≤
      (padicValRat p (pullbackScalar p r k) : ℚ) + pullbackGain r k := by
  rw [pullbackScalar_valuation p r k hp hr]
  push_cast
  have hv := factorial_valuation_bound p k 6 hp hp7 hk
  norm_num at hv
  have hg := pullbackGain_lower r k
  have hgQ : (r : ℚ)+k-10 ≤ 5*(pullbackGain r k : ℚ) := by exact_mod_cast hg
  linarith

theorem good_prime_eleven (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hne : p ≠ 7) :
    11 ≤ p := by
  by_contra h
  have hp10 : p ≤ 10 := by omega
  interval_cases p <;> norm_num at *

theorem pullback_gain_lower_eleven (p r k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p)
    (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ((k : ℚ)-8*r+41)/10 ≤
      (padicValRat p (pullbackScalar p r k) : ℚ) + pullbackGain r k := by
  rw [pullbackScalar_valuation p r k hp hr]
  push_cast
  have hv := factorial_valuation_bound p k 10 hp hp11 hk
  norm_num at hv
  have hg := pullbackGain_lower r k
  have hgQ : (r : ℚ)+k-10 ≤ 5*(pullbackGain r k : ℚ) := by exact_mod_cast hg
  linarith

theorem pullback_gain_eventual (p r precision : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : 1 ≤ r) : ∃ cutoff : ℕ, ∀ k, cutoff ≤ k →
    (precision : ℤ) ≤ padicValRat p (pullbackScalar p r k) + pullbackGain r k := by
  refine ⟨30*precision+24*r, ?_⟩
  intro k hk
  have h := pullback_gain_lower_seven p r k hp hp7 hr (by omega)
  have hkQ : (30*precision+24*r : ℚ) ≤ k := by exact_mod_cast hk
  have he : (precision : ℚ) ≤
      (padicValRat p (pullbackScalar p r k) : ℚ) + pullbackGain r k := by linarith
  exact_mod_cast he

theorem pullback_gain_T128 (p r k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hne : p ≠ 7) (hr : 1 ≤ r) (hr5 : r ≤ 5) (hk : 123 ≤ k) :
    8 ≤ padicValRat p (pullbackScalar p r k) + pullbackGain r k := by
  have h := pullback_gain_lower_eleven p r k hp (good_prime_eleven p hp hp7 hne) hr (by omega)
  have hkQ : (123 : ℚ) ≤ k := by exact_mod_cast hk
  have hrQ : (r : ℚ) ≤ 5 := by exact_mod_cast hr5
  have he : (8 : ℚ) ≤
      (padicValRat p (pullbackScalar p r k) : ℚ) + pullbackGain r k := by linarith
  exact_mod_cast he

theorem pullback_gain_nonnegative (p r k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hne : p ≠ 7) (hr : 1 ≤ r) (hr5 : r ≤ 5) :
    0 ≤ padicValRat p (pullbackScalar p r k) + pullbackGain r k := by
  by_cases hk : k = 0
  · subst k
    rw [pullbackScalar_valuation p r 0 hp hr, WPTruncationArithmetic.factorial_valuation_zero]
    omega
  · have h := pullback_gain_lower_eleven p r k hp (good_prime_eleven p hp hp7 hne) hr
      (by omega)
    have hrQ : (r : ℚ) ≤ 5 := by exact_mod_cast hr5
    have hkQ : (1 : ℚ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have he : (0 : ℚ) ≤
        (padicValRat p (pullbackScalar p r k) : ℚ) + pullbackGain r k := by linarith
    exact_mod_cast he

def primitiveTailScalar (p r K : ℕ) : ℚ := pullbackScalar p r (K-1)/(p : ℚ)

theorem primitiveTailScalar_ne_zero (p r K : ℕ) (hp : p.Prime) :
    primitiveTailScalar p r K ≠ 0 := div_ne_zero (pullbackScalar_ne_zero p r (K-1) hp)
      (by exact_mod_cast hp.ne_zero)

theorem primitiveTailScalar_valuation (p r K : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hK : 1 ≤ K) :
    padicValRat p (primitiveTailScalar p r K) =
      5-(r : ℤ)+(padicValNat p K : ℤ)-(WPTruncationArithmetic.factorialValuation p K : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [primitiveTailScalar, padicValRat.div (pullbackScalar_ne_zero p r (K-1) hp)
    (by exact_mod_cast hp.ne_zero), pullbackScalar_valuation p r (K-1) hp hr,
    padicValRat.self hp.one_lt]
  have he : K-1+1 = K := by omega
  have hf := WPTruncationArithmetic.factorial_valuation_succ p (K-1) hp
  rw [he] at hf
  omega

theorem primitiveTailScalars_same_valuation (p r K : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hK : 1 ≤ K) :
    padicValRat p (pullbackScalar p (r+1) (K-1)) =
      padicValRat p (primitiveTailScalar p r K) := by
  rw [pullbackScalar_valuation p (r+1) (K-1) hp (by omega),
    primitiveTailScalar_valuation p r K hp hr hK]
  have hf := WPTruncationArithmetic.factorial_valuation_succ p (K-1) hp
  rw [show K-1+1 = K by omega] at hf
  omega

theorem primitive_tail_gain_eventual (p r precision : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : 1 ≤ r) : ∃ cutoff : ℕ, ∀ K, cutoff ≤ K →
    (precision : ℤ) ≤ padicValRat p (primitiveTailScalar p r K) + pullbackGain (r+1) (K-1) := by
  obtain ⟨cutoff, hc⟩ := pullback_gain_eventual p (r+1) precision hp hp7 (by omega)
  refine ⟨cutoff+1, ?_⟩
  intro K hK
  rw [← primitiveTailScalars_same_valuation p r K hp hr (by omega)]
  exact hc (K-1) (by omega)

end WPResidueFrobenius
