import WPFiniteSignTrace

open scoped BigOperators

namespace WPFiniteDReciprocity

variable {K : Type*} [Field K]

def triangle (p : ℕ) : Finset (Sigma (fun _ : ℕ => ℕ)) :=
  (Finset.Ico 1 p).sigma (fun j => Finset.Ico 1 (j + 1))

theorem full_D_triangle (p : ℕ) [Fact p.Prime] (x y : K) :
    WPFiniteLoop.D (p - 1) x y =
      ∑ jk ∈ triangle p, x ^ jk.2 * y ^ (jk.1 - jk.2) / ((jk.2 : K) * (jk.1 : K)) := by
  unfold WPFiniteLoop.D triangle
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le, Finset.sum_sigma']

theorem triangle_reversal (p : ℕ) {A : Type*} [AddCommMonoid A]
    (f : Sigma (fun _ : ℕ => ℕ) → A) :
    (∑ jk ∈ triangle p, f ⟨p - jk.2, p - jk.1⟩) = ∑ jk ∈ triangle p, f jk := by
  have hm : ∀ jk ∈ triangle p, (⟨p - jk.2, p - jk.1⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ triangle p := by
    rintro ⟨j, k⟩ hjk
    simp only [triangle, Finset.mem_sigma, Finset.mem_Ico] at hjk ⊢
    omega
  have hi : ∀ jk ∈ triangle p,
      (⟨p - (p - jk.1), p - (p - jk.2)⟩ : Sigma (fun _ : ℕ => ℕ)) = jk := by
    rintro ⟨j, k⟩ hjk
    simp only [triangle, Finset.mem_sigma, Finset.mem_Ico] at hjk
    have hj : p - (p - j) = j := by omega
    have hk : p - (p - k) = k := by omega
    simp only [hj, hk]
  apply Finset.sum_bij' (fun jk _ => ⟨p - jk.2, p - jk.1⟩)
    (fun jk _ => ⟨p - jk.2, p - jk.1⟩) hm hm hi hi
  intro jk hjk
  rfl

theorem D_reciprocity (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) (hx : x ≠ 0) :
    WPFiniteLoop.D (p - 1) x y = x ^ p * WPFiniteLoop.D (p - 1) x⁻¹ (y / x) := by
  rw [full_D_triangle p x y, full_D_triangle p x⁻¹ (y / x), Finset.mul_sum]
  rw [← triangle_reversal p (fun jk =>
    x ^ jk.2 * y ^ (jk.1 - jk.2) / ((jk.2 : K) * (jk.1 : K)))]
  apply Finset.sum_congr rfl
  rintro ⟨j, k⟩ hjk
  have hm := hjk
  simp only [triangle, Finset.mem_sigma, Finset.mem_Ico] at hm
  have hj : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hk : k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hjd : (j : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j hj
  have hkd : (k : K) ≠ 0 := WPFiniteField.denominator_ne_zero p k hk
  simp only
  rw [show p - k - (p - j) = j - k by omega,
    WPFiniteField.reflected_denominator p j hj, WPFiniteField.reflected_denominator p k hk,
    neg_mul_neg, div_pow, inv_pow]
  have hs : x ^ j = x ^ k * x ^ (j - k) := by
    rw [← pow_add, show k + (j - k) = j by omega]
  have hpower : x ^ p * (x ^ k)⁻¹ * (x ^ (j - k))⁻¹ = x ^ (p - j) := by
    rw [pow_sub₀ x hx (Nat.le_of_lt (Finset.mem_Ico.mp hj).2), hs, mul_inv_rev]
    ring
  simp only [div_eq_mul_inv]
  linear_combination -(y ^ (j - k) * (j : K)⁻¹ * (k : K)⁻¹) * hpower

noncomputable def N_o (p : ℕ) (x y : K) : K :=
  WPFiniteLoop.D (p - 1) x y - WPFiniteLoop.D (p - 1) (-x) y -
    WPFiniteLoop.D (p - 1) x (-y) + WPFiniteLoop.D (p - 1) (-x) (-y)

theorem N_o_reciprocity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x y : K) (hx : x ≠ 0) : N_o p x y = x ^ p * N_o p x⁻¹ (y / x) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  unfold N_o
  rw [D_reciprocity p x y hx, D_reciprocity p (-x) y (neg_ne_zero.mpr hx),
    D_reciprocity p x (-y) hx, D_reciprocity p (-x) (-y) (neg_ne_zero.mpr hx)]
  rw [hodd.neg_pow]
  simp only [inv_neg, div_neg, neg_div, neg_neg]
  ring

noncomputable def T2 (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) : K :=
  WPFiniteLoop.D (p - 1) x y + WPFiniteLoop.D (p - 1) y x -
    WPFiniteField.R p x - WPFiniteField.R p y

private theorem D_off_diagonal (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) :
    WPFiniteLoop.D (p - 1) x y =
      (∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / ((k : K) * (j : K))) + WPFiniteField.R p x := by
  unfold WPFiniteLoop.D WPFiniteField.R
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_Ico_succ_top (Finset.mem_Ico.mp hj).1]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [show ((j : K) * (j : K)) = (j : K) ^ 2 by ring]

private theorem off_diagonal_reflection (j : ℕ) (x y : K) :
    (∑ k ∈ Finset.Ico 1 j, y ^ k * x ^ (j - k) / ((k : K) * (j : K))) =
      ∑ k ∈ Finset.Ico 1 j, x ^ k * y ^ (j - k) / (((j - k : ℕ) : K) * (j : K)) := by
  rw [← WPFiniteInversion.full_cutoff_reflection j
    (fun k => y ^ k * x ^ (j - k) / ((k : K) * (j : K)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show j - (j - k) = k by have h := Finset.mem_Ico.mp hk; omega]
  ring

theorem T2_low_rows (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) :
    T2 p x y = ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
      x ^ k * y ^ (j - k) / ((k : K) * ((j - k : ℕ) : K)) := by
  unfold T2
  rw [D_off_diagonal, D_off_diagonal]
  have he : (∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
      y ^ k * x ^ (j - k) / ((k : K) * (j : K))) =
      ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / (((j - k : ℕ) : K) * (j : K)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact off_diagonal_reflection j x y
  rw [he]
  have ha : ((∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / ((k : K) * (j : K))) + WPFiniteField.R p x) +
      ((∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / (((j - k : ℕ) : K) * (j : K))) + WPFiniteField.R p y) -
        WPFiniteField.R p x - WPFiniteField.R p y =
      (∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / ((k : K) * (j : K))) +
      ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 j,
        x ^ k * y ^ (j - k) / (((j - k : ℕ) : K) * (j : K)) := by ring
  rw [ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hj' := Finset.mem_Ico.mp hj
  have hk' := Finset.mem_Ico.mp hk
  have hjd : (j : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j hj
  have hkd : (k : K) ≠ 0 := WPFiniteField.denominator_ne_zero p k
    (Finset.mem_Ico.mpr (by omega))
  have hnd : ((j - k : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p (j - k)
    (Finset.mem_Ico.mpr (by omega))
  rw [Nat.cast_sub (by omega : k ≤ j)]
  rw [Nat.cast_sub (by omega : k ≤ j)] at hnd
  field_simp [hjd, hkd, hnd]
  ring

def closedLowTriangle (p : ℕ) : Finset (Sigma (fun _ : ℕ => ℕ)) :=
  (Finset.Ico 1 (p + 1)).sigma (fun j => Finset.Ico 1 j)

theorem closed_triangle_reindex (p : ℕ) {A : Type*} [AddCommMonoid A]
    (f : Sigma (fun _ : ℕ => ℕ) → A) :
    (∑ jk ∈ triangle p, f ⟨p - jk.1 + jk.2, jk.2⟩) =
      ∑ jk ∈ closedLowTriangle p, f jk := by
  have hm : ∀ jk ∈ triangle p,
      (⟨p - jk.1 + jk.2, jk.2⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ closedLowTriangle p := by
    rintro ⟨j, k⟩ hjk
    simp only [triangle, closedLowTriangle, Finset.mem_sigma, Finset.mem_Ico] at hjk ⊢
    omega
  have hn : ∀ jk ∈ closedLowTriangle p,
      (⟨p - jk.1 + jk.2, jk.2⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ triangle p := by
    rintro ⟨j, k⟩ hjk
    simp only [triangle, closedLowTriangle, Finset.mem_sigma, Finset.mem_Ico] at hjk ⊢
    omega
  have hi : ∀ jk ∈ triangle p,
      (⟨p - (p - jk.1 + jk.2) + jk.2, jk.2⟩ : Sigma (fun _ : ℕ => ℕ)) = jk := by
    rintro ⟨j, k⟩ hjk
    simp only [triangle, Finset.mem_sigma, Finset.mem_Ico] at hjk
    have he : p - (p - j + k) + k = j := by omega
    simp only [he]
  have hj : ∀ jk ∈ closedLowTriangle p,
      (⟨p - (p - jk.1 + jk.2) + jk.2, jk.2⟩ : Sigma (fun _ : ℕ => ℕ)) = jk := by
    rintro ⟨j, k⟩ hjk
    simp only [closedLowTriangle, Finset.mem_sigma, Finset.mem_Ico] at hjk
    have he : p - (p - j + k) + k = j := by omega
    simp only [he]
  apply Finset.sum_bij' (fun jk _ => ⟨p - jk.1 + jk.2, jk.2⟩)
    (fun jk _ => ⟨p - jk.1 + jk.2, jk.2⟩) hm hn hi hj
  intro jk hjk
  rfl

noncomputable def H2 (p : ℕ) (x y : K) : K :=
  ∑ k ∈ Finset.Ico 1 p, x ^ k * y ^ (p - k) / (k : K) ^ 2

theorem D_second_reciprocity (p : ℕ) [Fact p.Prime] [CharP K p]
    (x y : K) (hy : y ≠ 0) :
    y ^ p * WPFiniteLoop.D (p - 1) (x / y) (1 / y) = -T2 p x y + H2 p x y := by
  have he : y ^ p * WPFiniteLoop.D (p - 1) (x / y) (1 / y) =
      ∑ jk ∈ triangle p,
        -(x ^ jk.2 * y ^ (p - jk.1) / ((jk.2 : K) * ((p - jk.1 : ℕ) : K))) := by
    rw [full_D_triangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    rintro ⟨j, k⟩ hjk
    have hm := hjk
    simp only [triangle, Finset.mem_sigma, Finset.mem_Ico] at hm
    have hj : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
    have hs : y ^ j = y ^ k * y ^ (j - k) := by
      rw [← pow_add, show k + (j - k) = j by omega]
    have hpower : y ^ p * (y ^ k)⁻¹ * (y ^ (j - k))⁻¹ = y ^ (p - j) := by
      rw [pow_sub₀ y hy (Nat.le_of_lt (Finset.mem_Ico.mp hj).2), hs, mul_inv_rev]
      ring
    have hnum : y ^ p * ((x / y) ^ k * (1 / y) ^ (j - k)) = x ^ k * y ^ (p - j) := by
      rw [div_pow, one_div, inv_pow]
      simp only [div_eq_mul_inv]
      linear_combination x ^ k * hpower
    simp only
    rw [← mul_div_assoc, hnum, WPFiniteField.reflected_denominator p j hj]
    simp only [mul_neg, div_neg, neg_neg]
  have hrows : (∑ jk ∈ triangle p,
      -(x ^ jk.2 * y ^ (p - jk.1) / ((jk.2 : K) * ((p - jk.1 : ℕ) : K)))) =
      ∑ jk ∈ closedLowTriangle p,
        -(x ^ jk.2 * y ^ (jk.1 - jk.2) / ((jk.2 : K) * ((jk.1 - jk.2 : ℕ) : K))) := by
    rw [← closed_triangle_reindex p (fun jk =>
      -(x ^ jk.2 * y ^ (jk.1 - jk.2) / ((jk.2 : K) * ((jk.1 - jk.2 : ℕ) : K))))]
    apply Finset.sum_congr rfl
    rintro ⟨j, k⟩ hjk
    simp only
    rw [show p - j + k - k = p - j by omega]
  rw [he, hrows]
  simp only [closedLowTriangle, Finset.sum_sigma, Finset.sum_neg_distrib]
  rw [Finset.sum_Ico_succ_top (Fact.out : p.Prime).one_le]
  rw [← T2_low_rows]
  have hb : (∑ k ∈ Finset.Ico 1 p,
      x ^ k * y ^ (p - k) / ((k : K) * ((p - k : ℕ) : K))) = -H2 p x y := by
    unfold H2
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [WPFiniteField.reflected_denominator p k hk]
    simp only [mul_neg, div_neg]
    rw [show (k : K) * (k : K) = (k : K) ^ 2 by ring]
  rw [hb]
  ring

private theorem H2_joint_neg (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (x y : K) :
    H2 p (-x) (-y) = -H2 p x y := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  unfold H2
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  have hpowers : (-x) ^ k * (-y) ^ (p - k) = -(x ^ k * y ^ (p - k)) := by
    rw [neg_pow, neg_pow]
    calc
      _ = (-1 : K) ^ (k + (p - k)) * (x ^ k * y ^ (p - k)) := by rw [pow_add]; ring
      _ = _ := by rw [show k + (p - k) = p by omega, hodd.neg_pow, one_pow]; ring
  rw [hpowers, neg_div]

theorem H2_four_signs_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (x y : K) :
    H2 p x y + H2 p (-x) y + H2 p x (-y) + H2 p (-x) (-y) = 0 := by
  have he := H2_joint_neg p hp (-x) y
  rw [neg_neg] at he
  rw [he, H2_joint_neg p hp x y]
  ring

noncomputable def M (p : ℕ) (x y : K) : K :=
  WPFiniteLoop.D (p - 1) x y + WPFiniteLoop.D (p - 1) (-x) y -
    WPFiniteLoop.D (p - 1) x (-y) - WPFiniteLoop.D (p - 1) (-x) (-y)

private theorem M_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x y : K) (hy : y ≠ 0) :
    y ^ p * M p (x / y) (1 / y) =
      -WPFiniteSignTrace.fullTraceS p x y - WPFiniteSignTrace.fullTraceS p y x +
        2 * (WPFiniteField.R p x + WPFiniteField.R p (-x) +
          WPFiniteField.R p y + WPFiniteField.R p (-y)) := by
  have he0 := D_second_reciprocity p x y hy
  have he1 := D_second_reciprocity p (-x) y hy
  have he2 := D_second_reciprocity p x (-y) (neg_ne_zero.mpr hy)
  have he3 := D_second_reciprocity p (-x) (-y) (neg_ne_zero.mpr hy)
  have hH := H2_four_signs_zero p hp x y
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [hodd.neg_pow] at he2 he3
  simp only [div_neg, neg_div, neg_neg] at he1 he2 he3
  unfold M WPFiniteSignTrace.fullTraceS T2 at *
  linear_combination he0 + he1 + he2 + he3 + hH

theorem M_reciprocity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x y : K) (hy : y ≠ 0) :
    M p x y = y ^ p *
      (2 * (WPFiniteField.R p (x / y) + WPFiniteField.R p (-(x / y)) +
          WPFiniteField.R p (1 / y) + WPFiniteField.R p (-(1 / y))) -
        WPFiniteLoop.S p (x / y) (1 / y) - WPFiniteLoop.S p (1 / y) (x / y)) := by
  have he := M_source p hp (x / y) (1 / y) (one_div_ne_zero hy)
  have harg : (x / y) / (1 / y) = x := by field_simp [hy]
  rw [harg, one_div_one_div] at he
  rw [WPFiniteSignTrace.full_trace_eq_half_cutoff p hp,
    WPFiniteSignTrace.full_trace_eq_half_cutoff p hp] at he
  have hpow : (1 / y : K) ^ p * y ^ p = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy)]
  linear_combination y ^ p * he - M p x y * hpow

private theorem R_neg_one_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.R p (-1 : K) = 0 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have he := WPFiniteField.R_inversion p (-1 : K) (neg_ne_zero.mpr one_ne_zero)
  simp only [inv_neg, inv_one, hodd.neg_pow, one_pow, neg_one_mul] at he
  have hz : (2 : K) * WPFiniteField.R p (-1 : K) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left htwo

theorem M_rational_constant (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    2 * (WPFiniteField.R p (2 : K) + WPFiniteField.R p (-2 : K) +
      WPFiniteField.R p (1 / 2 : K) + WPFiniteField.R p (-(1 / 2) : K) -
      2 * WPFiniteField.R p (1 : K) - 2 * WPFiniteField.R p (-1 : K)) =
        WPFiniteField.R p (-2 : K) - 3 * (WPFiniteNC122.q p) ^ 2 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hR1 : WPFiniteField.R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
  have hR2 : WPFiniteField.R p (2 : K) = -(WPFiniteNC122.q p) ^ 2 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_two_eq_fermat p hp)
    simpa only [← WPFiniteField.R_castHom, map_ofNat, map_neg, map_pow, map_intCast,
      WPFiniteNC122.q] using he
  have hhalf := WPFiniteField.R_inversion p (2 : K) htwo
  rw [h2pow, hR2] at hhalf
  have hnhalf := WPFiniteField.R_inversion p (-2 : K) (neg_ne_zero.mpr htwo)
  rw [hodd.neg_pow, h2pow] at hnhalf
  simp only [inv_neg] at hnhalf
  simp only [one_div]
  rw [hR1, R_neg_one_zero p hp, hR2, hhalf, hnhalf]
  field_simp [htwo]
  ring

noncomputable def At (p : ℕ) (t : K) : K := WPFiniteLoop.S p 1 (2 * t) - WPFiniteLoop.S p (1 / 2) t

noncomputable def Bt (p : ℕ) (t : K) : K := WPFiniteLoop.S p 2 (2 * t) - WPFiniteLoop.S p 1 t

noncomputable def F_d (p : ℕ) (t : K) : K :=
  -M p t 1 + 2 * M p t (1 / 2) + M p (2 * t) 2 / 2 - M p (2 * t) 1

theorem F_d_original_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    F_d p t = WPFiniteLoop.A p t - WPFiniteLoop.B p t + At p t - Bt p t +
      WPFiniteField.R p (-2 : K) - 3 * (WPFiniteNC122.q p) ^ 2 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hhalfPow : (1 / 2 : K) ^ p = 1 / 2 := by rw [div_pow, one_pow, h2pow]
  have hM1 := M_reciprocity p hp t (1 : K) one_ne_zero
  have hMh := M_reciprocity p hp t (1 / 2 : K) (one_div_ne_zero htwo)
  have hM2 := M_reciprocity p hp (2 * t) (2 : K) htwo
  have hM21 := M_reciprocity p hp (2 * t) (1 : K) one_ne_zero
  simp only [one_pow, div_one] at hM1 hM21
  have hargHalf : t / (1 / 2 : K) = 2 * t := by field_simp [htwo]
  have hargTwo : (2 * t) / (2 : K) = t := by field_simp [htwo]
  rw [hhalfPow, hargHalf, one_div_one_div] at hMh
  rw [h2pow, hargTwo] at hM2
  unfold F_d At Bt WPFiniteLoop.A WPFiniteLoop.B
  rw [hM1, hMh, hM2, hM21]
  have hc := M_rational_constant (K := K) p hp
  field_simp [htwo]
  linear_combination hc

end WPFiniteDReciprocity
