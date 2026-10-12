import WPActualEtaPole

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource WPActualEtaPole

namespace WPActualEtaSupport

/-- An exact coefficient window; zero slots and both endpoints are included. -/
def bounded (P : ℚ[T;T⁻¹]) (lo hi : ℤ) : Prop :=
  ∀ j, P.coeff j ≠ 0 → lo ≤ j ∧ j ≤ hi

theorem bounded_zero (lo hi : ℤ) : bounded 0 lo hi := by
  intro j hj
  simp at hj

theorem bounded_mono {P : ℚ[T;T⁻¹]} {l u lo hi : ℤ}
    (h : bounded P l u) (hl : lo ≤ l) (hu : u ≤ hi) : bounded P lo hi := by
  intro j hj
  exact ⟨hl.trans (h j hj).1, (h j hj).2.trans hu⟩

theorem bounded_monomial (c : ℚ) (n : ℤ) : bounded (C c * T n) n n := by
  intro j hj
  have hmem : j ∈ (C c * T n).coeff.support := Finsupp.mem_support_iff.mpr hj
  have hnj : j = n := Finset.mem_singleton.mp (support_C_mul_T c n hmem)
  omega

theorem bounded_T (n : ℤ) : bounded (T n) n n := by
  simpa using bounded_monomial 1 n

theorem bounded_C (c : ℚ) : bounded (C c) 0 0 := by
  simpa using bounded_monomial c 0

theorem bounded_add {P Q : ℚ[T;T⁻¹]} {lo hi : ℤ}
    (hP : bounded P lo hi) (hQ : bounded Q lo hi) : bounded (P + Q) lo hi := by
  intro j hj
  by_cases hp : P.coeff j = 0
  · have hq : Q.coeff j ≠ 0 := by simpa [AddMonoidAlgebra.coeff_add, hp] using hj
    exact hQ j hq
  · exact hP j hp

theorem bounded_neg {P : ℚ[T;T⁻¹]} {lo hi : ℤ}
    (hP : bounded P lo hi) : bounded (-P) lo hi := by
  intro j hj
  apply hP j
  simpa [AddMonoidAlgebra.coeff_neg] using hj

theorem bounded_sub {P Q : ℚ[T;T⁻¹]} {lo hi : ℤ}
    (hP : bounded P lo hi) (hQ : bounded Q lo hi) : bounded (P - Q) lo hi := by
  simpa only [sub_eq_add_neg] using bounded_add hP (bounded_neg hQ)

theorem bounded_mul {P Q : ℚ[T;T⁻¹]} {l u v w : ℤ}
    (hP : bounded P l u) (hQ : bounded Q v w) : bounded (P * Q) (l + v) (u + w) := by
  classical
  intro j hj
  by_contra h
  apply hj
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hpa := hP a (Finsupp.mem_support_iff.mp ha)
  have hqb := hQ b (Finsupp.mem_support_iff.mp hb)
  have hab : a + b ≠ j := by omega
  exact if_neg hab

theorem bounded_pow {P : ℚ[T;T⁻¹]} {lo hi : ℤ}
    (hP : bounded P lo hi) (n : ℕ) : bounded (P ^ n) ((n : ℤ) * lo) ((n : ℤ) * hi) := by
  induction n with
  | zero => simpa using bounded_T 0
  | succ n ih =>
    rw [pow_succ]
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using bounded_mul ih hP

theorem bounded_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[T;T⁻¹]) (lo hi : ℤ)
    (hf : ∀ i ∈ s, bounded (f i) lo hi) : bounded (∑ i ∈ s, f i) lo hi := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero lo hi
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem bounded_toLaurent (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    bounded (Polynomial.toLaurent P) 0 d := by
  intro j hj
  have hmem : j ∈ (Polynomial.toLaurent P).coeff.support := Finsupp.mem_support_iff.mpr hj
  rw [support_coeff_toLaurent] at hmem
  obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hmem
  have hnd : n ≤ d := (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hn)).trans hd
  change 0 ≤ (n : ℤ) ∧ (n : ℤ) ≤ (d : ℤ)
  exact ⟨by omega, by exact_mod_cast hnd⟩

theorem forwardQuotient_bounded (a : ℚ) (n : ℕ) :
    bounded (forwardQuotient a n) 0 ((n : ℤ) - 1) := by
  induction n with
  | zero => exact bounded_zero _ _
  | succ n ih =>
    rw [forwardQuotient]
    apply bounded_add
    · exact bounded_mono (bounded_T n) (by omega) (by omega)
    · exact bounded_mono (bounded_mul (bounded_C a) ih) (by omega) (by omega)

theorem monomialQuotient_bounded (a : ℚ) (n lo hi : ℤ)
    (hl : lo ≤ 0) (hu : 1 ≤ hi) (hnl : lo ≤ n) (hnu : n ≤ hi) :
    bounded (monomialQuotient a n) lo (hi - 1) := by
  cases n with
  | ofNat n =>
    change (n : ℤ) ≤ hi at hnu
    exact bounded_mono (forwardQuotient_bounded a n) hl (by omega)
  | negSucc n =>
    unfold monomialQuotient
    apply bounded_mono (bounded_mul
      (bounded_mul (bounded_neg (bounded_C _)) (bounded_T _))
      (forwardQuotient_bounded a (n + 1))) <;> omega

theorem dividedDifference_bounded (a : ℚ) (P : ℚ[T;T⁻¹]) (lo hi : ℤ)
    (hl : lo ≤ 0) (hu : 1 ≤ hi) (hP : bounded P lo hi) :
    bounded (dividedDifference a P) lo (hi - 1) := by
  classical
  change bounded (Finsupp.linearCombination ℚ (monomialQuotient a) P.coeff) lo (hi - 1)
  rw [Finsupp.linearCombination_apply]
  apply bounded_sum
  intro j hj
  change bounded (P.coeff j • monomialQuotient a j) lo (hi - 1)
  rw [smul_eq_C_mul]
  have hjs := hP j (Finsupp.mem_support_iff.mp hj)
  exact bounded_mono (bounded_mul (bounded_C _) (monomialQuotient_bounded a j lo hi
    hl hu hjs.1 hjs.2)) (by omega) (by omega)

theorem Vx_bounded : bounded Vx 0 3 := by
  apply bounded_toLaurent Vpolynomial 3
  unfold Vpolynomial
  compute_degree

theorem Qx_bounded : bounded Qx (-3) 0 := by
  let P : ℚ[X] := Polynomial.C (1 / 125) * (4 * Polynomial.X - 1) *
    (4 - Polynomial.X) ^ 2
  have hP : P.natDegree ≤ 3 := by unfold P; compute_degree
  have hQ : Qx = Polynomial.toLaurent P * T (-3) := by
    simp only [Qx, P, map_mul, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  rw [hQ]
  exact bounded_mono (bounded_mul (bounded_toLaurent P 3 hP) (bounded_T (-3)))
    (by omega) (by omega)

theorem Fpull_expansion (e : ℕ) (L : ℚ[T;T⁻¹]) :
    Fpull e L = ∑ n ∈ Finset.range (e + 1), C (WPReview.nativeCoefficient n) * L ^ n := by
  simp [Fpull, substitute, WPReview.nativePolynomial, Polynomial.eval₂_monomial]

theorem Hpull_expansion (e : ℕ) (L : ℚ[T;T⁻¹]) :
    Hpull e L = ∑ n ∈ Finset.range (e + 1), C (WPReview.nativeCoefficient n / (n : ℚ)) *
      L ^ n := by
  simp [Hpull, Hpolynomial, substitute, Polynomial.eval₂_monomial]

theorem actual_FV_bounded (e : ℕ) : bounded (Fpull e Vx) 0 (3 * (e : ℤ)) := by
  rw [Fpull_expansion]
  apply bounded_sum
  intro n hn
  have hne := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Vx_bounded n))
    (by omega) (by omega)

theorem actual_FQ_bounded (e : ℕ) : bounded (Fpull e Qx) (-3 * (e : ℤ)) 0 := by
  rw [Fpull_expansion]
  apply bounded_sum
  intro n hn
  have hne := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Qx_bounded n))
    (by omega) (by omega)

theorem actual_HV_bounded (e : ℕ) : bounded (HX e) 0 (3 * (e : ℤ)) := by
  rw [HX, Hpull_expansion]
  apply bounded_sum
  intro n hn
  have hne := Finset.mem_range.mp hn
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_pow Vx_bounded n))
    (by omega) (by omega)

theorem actual_chi_full_support (p N e : ℕ) (he : N ≤ e) :
    bounded (chiX p N e) ((N : ℤ) - 3 * (e : ℤ)) (3 * (e : ℤ)) := by
  unfold chiX
  have hV : bounded (Fpull e Vx) ((N : ℤ) - 3 * (e : ℤ)) (3 * (e : ℤ)) :=
    bounded_mono (actual_FV_bounded e) (by omega) (by omega)
  have hQ : bounded (T (N : ℤ) * Fpull e Qx)
      ((N : ℤ) - 3 * (e : ℤ)) (3 * (e : ℤ)) :=
    bounded_mono (bounded_mul (bounded_T N) (actual_FQ_bounded e)) (by omega) (by omega)
  exact bounded_mono (bounded_mul (bounded_C _) (bounded_sub hV hQ)) (by omega) (by omega)

theorem actual_AX_full_support (p N e : ℕ) (he : N ≤ e) :
    bounded (AX p N e) ((N : ℤ) - 3 * (e : ℤ)) (3 * (e : ℤ)) := by
  exact bounded_add (actual_chi_full_support p N e he)
    (bounded_mono (actual_HV_bounded e) (by omega) (by omega))

theorem actual_Peta_full_support (p N e : ℕ) (he : N ≤ e) (hepos : 1 ≤ e) :
    bounded (Peta p N e) ((N : ℤ) - 3 * (e : ℤ)) (3 * (e : ℤ) - 1) := by
  unfold Peta
  have hA := actual_AX_full_support p N e he
  have hl : (N : ℤ) - 3 * (e : ℤ) ≤ 0 := by omega
  have hu : 1 ≤ 3 * (e : ℤ) := by omega
  apply bounded_sub
  · apply bounded_add
    · exact bounded_mono (bounded_mul (bounded_C 2)
        (dividedDifference_bounded (1 / 4) _ _ _ hl hu hA)) (by omega) (by omega)
    · exact dividedDifference_bounded 4 _ _ _ hl hu hA
  · apply bounded_mono (bounded_mul (bounded_mul (bounded_C (1 / 2))
      (actual_HV_bounded e)) (bounded_T (-1))) <;> omega

theorem actual_Peta_cutoff_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    bounded (Peta p ((p - 1) / 2) (p - 1 - p / 6))
      ((((p - 1) / 2 : ℕ) : ℤ) - 3 * ((p - 1 - p / 6 : ℕ) : ℤ))
      (3 * ((p - 1 - p / 6 : ℕ) : ℤ) - 1) := by
  apply actual_Peta_full_support
  · omega
  · omega

end WPActualEtaSupport
