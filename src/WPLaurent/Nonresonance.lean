import WPLaurent.Resonance

namespace WPLaurent

def nonresonantWeight (p : ℕ) (ell : ℤ) : ℚ :=
  (p : ℚ) * (1 - (4 : ℚ) ^ (-ell)) / (ell : ℚ)

def nonresonantExpansion (p : ℕ) (ell b r : ℤ) : ℚ :=
  (p : ℚ) * (1 - (4 : ℚ) ^ (-b-r)) / (ell : ℚ) +
    (p : ℚ)^2 * (b : ℚ) * (4 : ℚ)^(-b-r) * fermatQuotient4 p / (ell : ℚ)

theorem nonresonant_denominator_nonzero (p : ℕ) (ell b r : ℤ)
    (hsplit : ell = b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ)) :
    ell ≠ 0 := by
  have hpz : (p : ℤ) ≠ 0 := by omega
  have hrem : ell % (p : ℤ) = r := by
    rw [hsplit, Int.add_emod, Int.mul_emod]
    simp [Int.emod_eq_of_lt (by omega : 0 ≤ r) hrp]
  intro hzero
  rw [hzero, Int.zero_emod] at hrem
  omega

theorem nonresonant_denominator_unit (p : ℕ) (ell b r : ℤ)
    (hsplit : ell = b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ)) :
    padicValRat p (ell : ℚ) = 0 := by
  have hrem : ell % (p : ℤ) = r := by
    rw [hsplit, Int.add_emod, Int.mul_emod]
    simp [Int.emod_eq_of_lt (by omega : 0 ≤ r) hrp]
  have hnd : ¬(p : ℤ) ∣ ell := by
    intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    rw [hrem] at hz
    omega
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnd]
  norm_num

theorem four_integer_power_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (z : ℤ) :
    padicValRat p ((4 : ℚ)^z) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.zpow, four_unit p hp7]
  ring

theorem fermat_integer_power_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (z : ℤ) :
    padicValRat p ((1 + (p : ℚ)*fermatQuotient4 p)^z) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.zpow, fermatUnit_unit p hp hp7]
  ring

theorem native_interval_multiplier_bounds (p : ℕ) (hp7 : 7 ≤ p) (ell b r : ℤ)
    (hsplit : ell = b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ))
    (hlo : -6*((5*p/6 : ℕ) : ℤ)-1 ≤ ell) (hhi : ell ≤ 6*(p : ℤ)-1) :
    -6 ≤ b ∧ b ≤ 5 := by
  have hquot : 6*(5*p/6 : ℕ) ≤ 5*p := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (5*p) 6
  have hquotz : 6*((5*p/6 : ℕ) : ℤ) ≤ 5*(p : ℤ) := by exact_mod_cast hquot
  have hpz : (7 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp7
  constructor
  · by_contra hb
    have hb7 : b ≤ -7 := by omega
    have hbp : b*(p : ℤ) ≤ -7*(p : ℤ) :=
      mul_le_mul_of_nonneg_right hb7 (by omega)
    omega
  · by_contra hb
    have hb6 : 6 ≤ b := by omega
    have hbp : 6*(p : ℤ) ≤ b*(p : ℤ) :=
      mul_le_mul_of_nonneg_right hb6 (by omega)
    omega

theorem nonresonant_power_rewrite (p : ℕ) (hp : p.Prime) (ell b r : ℤ)
    (hsplit : ell = b*(p : ℤ)+r) :
    (4 : ℚ)^(-ell) = (4 : ℚ)^(-b-r)*(1+(p : ℚ)*fermatQuotient4 p)^(-b) := by
  have hp1 := hp.one_lt
  have hcast : (p : ℤ) = ((p-1 : ℕ) : ℤ)+1 := by omega
  have hexp : -ell = (-b-r)+((p-1 : ℕ) : ℤ)*(-b) := by
    rw [hsplit, hcast]
    ring
  rw [fermatQuotient4_identity p hp, ← zpow_natCast (4 : ℚ) (p-1),
    ← zpow_mul, ← zpow_add₀ (by norm_num), hexp]

private def firstOrderTail (b : ℤ) (u : ℚ) : ℚ :=
  if b = -6 then 15+20*u+15*u^2+6*u^3+u^4 else
  if b = -5 then 10+10*u+5*u^2+u^3 else
  if b = -4 then 6+4*u+u^2 else
  if b = -3 then 3+u else
  if b = -2 then 1 else
  if b = -1 then 0 else
  if b = 0 then 0 else
  if b = 1 then (1+u)⁻¹ else
  if b = 2 then (3+2*u)/(1+u)^2 else
  if b = 3 then (6+8*u+3*u^2)/(1+u)^3 else
  if b = 4 then (10+20*u+15*u^2+4*u^3)/(1+u)^4 else
  (15+40*u+45*u^2+24*u^3+5*u^4)/(1+u)^5

private theorem finite_first_order_residual (b : ℤ) (hblo : -6 ≤ b) (hbhi : b ≤ 5)
    (u : ℚ) (hu : 1+u ≠ 0) :
    (1+u)^(-b)-(1-(b : ℚ)*u) = u^2*firstOrderTail b u := by
  interval_cases b <;> norm_num [firstOrderTail, zpow_neg] <;> field_simp <;> ring

private theorem integer_integral (p : ℕ) (k : ℤ) : 0 ≤ padicValRat p (k : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

private theorem product_integral (p : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x*y) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  rw [padicValRat.mul hx0 hy0]
  omega

private theorem quotient_integral (p : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : padicValRat p y = 0) :
    0 ≤ padicValRat p (x/y) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [div_eq_mul_inv]
  apply product_integral p hp x y⁻¹ hx
  rw [padicValRat.inv, hy]
  norm_num

private theorem firstOrderTail_integral (p : ℕ) (hp : p.Prime) (b : ℤ)
    (hblo : -6 ≤ b) (hbhi : b ≤ 5) (k : ℤ)
    (hu : padicValRat p (1+(k : ℚ)) = 0) :
    0 ≤ padicValRat p (firstOrderTail b (k : ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hm6 := integer_integral p (15+20*k+15*k^2+6*k^3+k^4)
  have hm5 := integer_integral p (10+10*k+5*k^2+k^3)
  have hm4 := integer_integral p (6+4*k+k^2)
  have hm3 := integer_integral p (3+k)
  have h2 := integer_integral p (3+2*k)
  have h3 := integer_integral p (6+8*k+3*k^2)
  have h4 := integer_integral p (10+20*k+15*k^2+4*k^3)
  have h5 := integer_integral p (15+40*k+45*k^2+24*k^3+5*k^4)
  push_cast at hm6 hm5 hm4 hm3 h2 h3 h4 h5
  interval_cases b
  · simpa [firstOrderTail] using hm6
  · simpa [firstOrderTail] using hm5
  · simpa [firstOrderTail] using hm4
  · simpa [firstOrderTail] using hm3
  · simp [firstOrderTail]
  · simp [firstOrderTail]
  · simp [firstOrderTail]
  · change 0 ≤ padicValRat p ((1+(k : ℚ))⁻¹)
    rw [padicValRat.inv, hu]
    norm_num
  · change 0 ≤ padicValRat p ((3+2*(k : ℚ))/(1+(k : ℚ))^2)
    apply quotient_integral p hp _ _ h2
    rw [padicValRat.pow, hu]
    ring
  · change 0 ≤ padicValRat p ((6+8*(k : ℚ)+3*(k : ℚ)^2)/(1+(k : ℚ))^3)
    apply quotient_integral p hp _ _ h3
    rw [padicValRat.pow, hu]
    ring
  · change 0 ≤ padicValRat p ((10+20*(k : ℚ)+15*(k : ℚ)^2+4*(k : ℚ)^3)/(1+(k : ℚ))^4)
    apply quotient_integral p hp _ _ h4
    rw [padicValRat.pow, hu]
    ring
  · change 0 ≤ padicValRat p ((15+40*(k : ℚ)+45*(k : ℚ)^2+24*(k : ℚ)^3+5*(k : ℚ)^4)/(1+(k : ℚ))^5)
    apply quotient_integral p hp _ _ h5
    rw [padicValRat.pow, hu]
    ring

private theorem cube_times_integral_congruent (p : ℕ) (hp : p.Prime) (x : ℚ)
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

theorem literal_nonresonant_kernel (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ell b r : ℤ) (hsplit : ell = b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ))
    (_hodd : Odd ell) (hlo : -6*((5*p/6 : ℕ) : ℤ)-1 ≤ ell) (hhi : ell ≤ 6*(p : ℤ)-1) :
    RationalCongruent p 3 (nonresonantWeight p ell) (nonresonantExpansion p ell b r) := by
  let : Fact p.Prime := ⟨hp⟩
  have hb := native_interval_multiplier_bounds p hp7 ell b r hsplit hr1 hrp hlo hhi
  obtain ⟨k, hk⟩ := fermatQuotient4_integer p hp hp7
  have hU : 1+(p : ℚ)*fermatQuotient4 p ≠ 0 := by
    rw [fermatQuotient4_identity p hp]
    positivity
  have hres := finite_first_order_residual b hb.1 hb.2 ((p : ℚ)*fermatQuotient4 p) hU
  have hunit := fermatUnit_unit p hp hp7
  have htail : 0 ≤ padicValRat p (firstOrderTail b ((p : ℚ)*fermatQuotient4 p)) := by
    rw [hk]
    have hcast : (p : ℚ)*(k : ℚ) = (((p : ℤ)*k : ℤ) : ℚ) := by push_cast; rfl
    rw [hcast]
    apply firstOrderTail_integral p hp b hb.1 hb.2
    simpa only [hk, hcast] using hunit
  have hellq : (ell : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (nonresonant_denominator_nonzero p ell b r hsplit hr1 hrp)
  have hfactor : nonresonantWeight p ell - nonresonantExpansion p ell b r =
      (p : ℚ)^3 * (-(4 : ℚ)^(-b-r)/(ell : ℚ) * fermatQuotient4 p^2 *
        firstOrderTail b ((p : ℚ)*fermatQuotient4 p)) := by
    unfold nonresonantWeight nonresonantExpansion
    rw [nonresonant_power_rewrite p hp ell b r hsplit]
    rw [show (1+(p : ℚ)*fermatQuotient4 p)^(-b) =
      1-(b : ℚ)*((p : ℚ)*fermatQuotient4 p) +
        ((p : ℚ)*fermatQuotient4 p)^2*firstOrderTail b ((p : ℚ)*fermatQuotient4 p)
      by linear_combination hres]
    field_simp
    ring
  have hbase : 0 ≤ padicValRat p (-(4 : ℚ)^(-b-r)/(ell : ℚ)) := by
    apply quotient_integral p hp
    · rw [padicValRat.neg, four_integer_power_unit p hp hp7]
    · exact nonresonant_denominator_unit p ell b r hsplit hr1 hrp
  have hq2 : 0 ≤ padicValRat p (fermatQuotient4 p^2) := by
    rw [padicValRat.pow]
    have := fermatQuotient4_integral p hp hp7
    omega
  have hint := product_integral p hp _ _ (product_integral p hp _ _ hbase hq2) htail
  have h := cube_times_integral_congruent p hp _ hint
  unfold RationalCongruent at h ⊢
  rw [← sub_eq_zero, hfactor]
  simpa only [sub_zero] using h

theorem literal_nonresonant_kernel_expanded (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ell b r : ℤ) (hsplit : ell = b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ))
    (hodd : Odd ell) (hlo : -6*((5*p/6 : ℕ) : ℤ)-1 ≤ ell) (hhi : ell ≤ 6*(p : ℤ)-1) :
    RationalCongruent p 3
      ((p : ℚ)*(1-(4 : ℚ)^(-ell))/(ell : ℚ))
      ((p : ℚ)*(1-(4 : ℚ)^(-b-r))/(ell : ℚ) +
        (p : ℚ)^2*(b : ℚ)*(4 : ℚ)^(-b-r)*fermatQuotient4 p/(ell : ℚ)) := by
  exact literal_nonresonant_kernel p hp hp7 ell b r hsplit hr1 hrp hodd hlo hhi

end WPLaurent
