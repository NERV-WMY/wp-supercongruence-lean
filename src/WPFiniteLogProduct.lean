import WPFiniteDReciprocity

open scoped BigOperators

namespace WPFiniteLogProduct

open WPFiniteDReciprocity

variable {K : Type*} [Field K]

def rect (p : ℕ) : Finset (ℕ × ℕ) := (Finset.Ico 1 p) ×ˢ (Finset.Ico 1 p)

def lowRect (p : ℕ) : Finset (ℕ × ℕ) := (rect p).filter (fun ij => ij.1 + ij.2 < p)

def midRect (p : ℕ) : Finset (ℕ × ℕ) := (rect p).filter (fun ij => ij.1 + ij.2 = p)

def highRect (p : ℕ) : Finset (ℕ × ℕ) := (rect p).filter (fun ij => p < ij.1 + ij.2)

def lowTriangle (p : ℕ) : Finset (Sigma (fun _ : ℕ => ℕ)) :=
  (Finset.Ico 1 p).sigma (fun j => Finset.Ico 1 j)

theorem rectangle_partition (p : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ × ℕ → A) :
    (∑ ij ∈ rect p, f ij) = (∑ ij ∈ lowRect p, f ij) +
      (∑ ij ∈ midRect p, f ij) + ∑ ij ∈ highRect p, f ij := by
  simp only [lowRect, midRect, highRect, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  rcases lt_trichotomy (ij.1 + ij.2) p with h | h | h
  · simp only [if_pos h, if_neg (ne_of_lt h), if_neg (not_lt_of_ge h.le), add_zero]
  · simp only [if_neg (not_lt_of_ge h.ge), if_pos h, if_neg (not_lt_of_ge h.le),
      zero_add, add_zero]
  · simp only [if_neg (not_lt_of_ge h.le), if_neg (ne_of_gt h), if_pos h, zero_add]

theorem low_reindex (p : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ × ℕ → A) :
    (∑ jk ∈ lowTriangle p, f (jk.2, jk.1 - jk.2)) = ∑ ij ∈ lowRect p, f ij := by
  have hm : ∀ jk ∈ lowTriangle p, (jk.2, jk.1 - jk.2) ∈ lowRect p := by
    rintro ⟨j, k⟩ hjk
    simp only [lowTriangle, lowRect, rect, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ico] at hjk ⊢
    omega
  have hn : ∀ ij ∈ lowRect p,
      (⟨ij.1 + ij.2, ij.1⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ lowTriangle p := by
    rintro ⟨i, j⟩ hij
    simp only [lowTriangle, lowRect, rect, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ico] at hij ⊢
    omega
  apply Finset.sum_bij' (fun jk _ => (jk.2, jk.1 - jk.2))
    (fun ij _ => ⟨ij.1 + ij.2, ij.1⟩) hm hn
  · rintro ⟨j, k⟩ hjk
    simp only [lowTriangle, Finset.mem_sigma, Finset.mem_Ico] at hjk
    have he : k + (j - k) = j := by omega
    simp only [he]
  · rintro ⟨i, j⟩ hij
    simp
  · intro jk hjk
    rfl

theorem mid_reindex (p : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ × ℕ → A) :
    (∑ k ∈ Finset.Ico 1 p, f (k, p - k)) = ∑ ij ∈ midRect p, f ij := by
  have hm : ∀ k ∈ Finset.Ico 1 p, (k, p - k) ∈ midRect p := by
    intro k hk
    simp only [midRect, rect, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hk ⊢
    omega
  have hn : ∀ ij ∈ midRect p, ij.1 ∈ Finset.Ico 1 p := by
    rintro ⟨i, j⟩ hij
    simp only [midRect, rect, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hij ⊢
    omega
  apply Finset.sum_bij' (fun k _ => (k, p - k)) (fun ij _ => ij.1) hm hn
  · intro k hk
    rfl
  · rintro ⟨i, j⟩ hij
    simp only [midRect, rect, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hij
    have he : p - i = j := by omega
    simp only [he]
  · intro k hk
    rfl

theorem high_reindex (p : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ × ℕ → A) :
    (∑ jk ∈ lowTriangle p, f (p - jk.2, p - (jk.1 - jk.2))) =
      ∑ ij ∈ highRect p, f ij := by
  have hm : ∀ jk ∈ lowTriangle p, (p - jk.2, p - (jk.1 - jk.2)) ∈ highRect p := by
    rintro ⟨j, k⟩ hjk
    simp only [lowTriangle, highRect, rect, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ico] at hjk ⊢
    omega
  have hn : ∀ ij ∈ highRect p,
      (⟨2 * p - ij.1 - ij.2, p - ij.1⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ lowTriangle p := by
    rintro ⟨i, j⟩ hij
    simp only [lowTriangle, highRect, rect, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Ico] at hij ⊢
    omega
  apply Finset.sum_bij' (fun jk _ => (p - jk.2, p - (jk.1 - jk.2)))
    (fun ij _ => ⟨2 * p - ij.1 - ij.2, p - ij.1⟩) hm hn
  · rintro ⟨j, k⟩ hjk
    simp only [lowTriangle, Finset.mem_sigma, Finset.mem_Ico] at hjk
    have hj : 2 * p - (p - k) - (p - (j - k)) = j := by omega
    have hk : p - (p - k) = k := by omega
    simp only [hj, hk]
  · rintro ⟨i, j⟩ hij
    simp only [highRect, rect, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hij
    have hi : p - (p - i) = i := by omega
    have hj : p - (2 * p - i - j - (p - i)) = j := by omega
    simp only [hi, hj]
  · intro jk hjk
    rfl

theorem full_logarithm_product (p : ℕ) [Fact p.Prime] [CharP K p]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    WPFiniteField.ell p x * WPFiniteField.ell p y =
      T2 p x y - H2 p x y + x ^ p * y ^ p * T2 p x⁻¹ y⁻¹ := by
  let f : ℕ × ℕ → K := fun ij => x ^ ij.1 * y ^ ij.2 / ((ij.1 : K) * (ij.2 : K))
  have he : WPFiniteField.ell p x * WPFiniteField.ell p y = ∑ ij ∈ rect p, f ij := by
    unfold WPFiniteField.ell rect
    rw [Finset.sum_mul, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f]
    simp only [div_eq_mul_inv]
    ring
  have hl : (∑ ij ∈ lowRect p, f ij) = T2 p x y := by
    rw [← low_reindex p f]
    simp only [lowTriangle, Finset.sum_sigma]
    exact (T2_low_rows p x y).symm
  have hm : (∑ ij ∈ midRect p, f ij) = -H2 p x y := by
    rw [← mid_reindex p f]
    unfold H2
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [WPFiniteField.reflected_denominator p k hk]
    simp only [mul_neg, div_neg]
    rw [show (k : K) * (k : K) = (k : K) ^ 2 by ring]
  have hh : (∑ ij ∈ highRect p, f ij) = x ^ p * y ^ p * T2 p x⁻¹ y⁻¹ := by
    rw [← high_reindex p f, T2_low_rows]
    simp only [lowTriangle, Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    have hj' := Finset.mem_Ico.mp hj
    have hk' := Finset.mem_Ico.mp hk
    have hkm : k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
    have hnm : j - k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
    dsimp only [f]
    rw [WPFiniteField.reflected_denominator p k hkm,
      WPFiniteField.reflected_denominator p (j - k) hnm, neg_mul_neg,
      pow_sub₀ x hx (Nat.le_of_lt (Finset.mem_Ico.mp hkm).2),
      pow_sub₀ y hy (Nat.le_of_lt (Finset.mem_Ico.mp hnm).2), inv_pow, inv_pow]
    simp only [div_eq_mul_inv]
    ring
  rw [he, rectangle_partition, hl, hm, hh]
  ring

private theorem product_sign_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    4 * WPFiniteField.E p x * WPFiniteField.E p y =
      WPFiniteLoop.S p x y + WPFiniteLoop.S p y x -
        2 * (WPFiniteField.R p x + WPFiniteField.R p (-x) +
          WPFiniteField.R p y + WPFiniteField.R p (-y)) +
        x ^ p * y ^ p * (N_o p x⁻¹ y⁻¹ + N_o p y⁻¹ x⁻¹) := by
  have he0 := full_logarithm_product p x y hx hy
  have he1 := full_logarithm_product p (-x) y (neg_ne_zero.mpr hx) hy
  have he2 := full_logarithm_product p x (-y) hx (neg_ne_zero.mpr hy)
  have he3 := full_logarithm_product p (-x) (-y) (neg_ne_zero.mpr hx) (neg_ne_zero.mpr hy)
  have hH := H2_four_signs_zero p hp x y
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  simp only [hodd.neg_pow, inv_neg] at he1 he2 he3
  rw [← WPFiniteSignTrace.full_trace_eq_half_cutoff p hp x y,
    ← WPFiniteSignTrace.full_trace_eq_half_cutoff p hp y x]
  unfold WPFiniteField.E N_o WPFiniteSignTrace.fullTraceS T2 at *
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  field_simp [htwo]
  simp only [one_div] at *
  linear_combination 4 * (he0 + he1 + he2 + he3 - hH)

theorem even_logarithm_product (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    4 * WPFiniteField.E p x * WPFiniteField.E p y =
      WPFiniteLoop.S p x y + WPFiniteLoop.S p y x -
        2 * (WPFiniteField.R p x + WPFiniteField.R p (-x) +
          WPFiniteField.R p y + WPFiniteField.R p (-y)) +
        y ^ p * N_o p x (x / y) + x ^ p * N_o p y (y / x) := by
  rw [product_sign_source p hp x y hx hy]
  have heX := N_o_reciprocity p hp x⁻¹ y⁻¹ (inv_ne_zero hx)
  have heY := N_o_reciprocity p hp y⁻¹ x⁻¹ (inv_ne_zero hy)
  have hargX : y⁻¹ / x⁻¹ = x / y := by field_simp [hx, hy]
  have hargY : x⁻¹ / y⁻¹ = y / x := by field_simp [hx, hy]
  rw [inv_inv, hargX] at heX
  rw [inv_inv, hargY] at heY
  rw [heX, heY]
  have hxpow : x ^ p * x⁻¹ ^ p = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
  have hypow : y ^ p * y⁻¹ ^ p = 1 := by rw [← mul_pow, mul_inv_cancel₀ hy, one_pow]
  linear_combination (y ^ p * N_o p x (x / y)) * hxpow +
    (x ^ p * N_o p y (y / x)) * hypow

noncomputable def F_b (p : ℕ) (t : K) : K :=
  -N_o p t 1 + 2 * N_o p t (1 / 2) + N_o p (2 * t) 2 - 2 * N_o p (2 * t) 1

theorem F_b_original_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (t : K) (ht : t ≠ 0) :
    t ^ p * F_b p t = WPFiniteLoop.Chi p t -
      2 * (WPFiniteField.E p (2 * t) - WPFiniteField.E p t) ^ 2 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h2t : (2 * t : K) ≠ 0 := mul_ne_zero htwo ht
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have he1 := even_logarithm_product p hp t t ht ht
  have he2 := even_logarithm_product p hp (2 * t) (2 * t) h2t h2t
  have heM := even_logarithm_product p hp (2 * t) t h2t ht
  rw [div_self ht] at he1
  rw [div_self h2t, mul_pow, h2pow] at he2
  have harg2 : (2 * t) / t = (2 : K) := by field_simp [ht]
  have hargHalf : t / (2 * t) = (1 / 2 : K) := by field_simp [ht, htwo]
  rw [harg2, hargHalf, mul_pow, h2pow] at heM
  apply mul_left_cancel₀ htwo
  unfold F_b WPFiniteLoop.Chi
  linear_combination he1 + he2 - 2 * heM

end WPFiniteLogProduct
