import WPLiteralAdapter.FiniteStokes

open scoped BigOperators
open WPForcedSourceStokes WPFiniteConductorPolynomial Polynomial

namespace WPLiteralAdapter

noncomputable section

set_option maxHeartbeats 1000000

/-- The low-index numerator retains the actual pair of native primitive terms. -/
noncomputable def primitiveLowTail : ℚ[X] :=
  ∑ i : Fin 6, if i=2 then 0 else
    C ((9/40000 : ℚ)*nativeStateTermWeight 1 i/primitiveDenominatorScalar i)*primitiveNumerator i

noncomputable def primitiveLowNumerator : ℚ[X] :=
  C (1/884458575000000 : ℚ)*
    (primitiveNumerator 3-C (1/25 : ℚ)*primitiveNumerator 2)+X^3*primitiveLowTail

noncomputable def primitiveHighNumerator (n : ℕ) (i : Fin 6) : ℚ[X] :=
  C (nativeStateTermWeight n i*WPReview.nativeCoefficient n^2*
    (729/15625 : ℚ)^n/primitiveDenominatorScalar i)*
    X^(3*n-primitiveDenominatorOrder i)*primitiveNumerator i

noncomputable def nativePrimitiveNumerator (p : ℕ) : ℚ[X] :=
  primitiveLowNumerator.divX+
    ∑ n∈Finset.Ico 2 p, ∑ i : Fin 6, primitiveHighNumerator n i

theorem primitive_denominator_escape (i : Fin 6) :
    primitiveDenominator i=C (primitiveDenominatorScalar i)*
      X^primitiveDenominatorOrder i*escape^2 := by
  simpa only [escape, C_ofNat] using primitive_denominator_formula i

theorem primitive_term_fraction (n : ℕ) (i : Fin 6) :
    nativePrimitiveTerm n i=
      RatFunc.C (nativeStateTermWeight n i*WPReview.nativeCoefficient n^2*
        (729/15625 : ℚ)^n)*symbol^(3*n)*
          algebraMap ℚ[X] (RatFunc ℚ) (primitiveNumerator i)/
        (RatFunc.C (primitiveDenominatorScalar i)*symbol^primitiveDenominatorOrder i*
          algebraMap ℚ[X] (RatFunc ℚ) (escape^2)) := by
  simp only [nativePrimitiveTerm, primitiveEntry, primitive_denominator_escape,
    lambda, symbol, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_div₀, mul_pow, ← pow_mul]
  norm_num [map_ratCast]
  ring

theorem primitive_low_pair_fraction :
    (∑ i : Fin 6, nativePrimitiveTerm 0 i)+(∑ i : Fin 6, nativePrimitiveTerm 1 i) =
    algebraMap ℚ[X] (RatFunc ℚ) primitiveLowNumerator /
      (symbol*algebraMap ℚ[X] (RatFunc ℚ) (escape^2)) := by
  have hx : symbol≠0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have he : algebraMap ℚ[X] (RatFunc ℚ) escape≠0 := by
    apply RatFunc.algebraMap_ne_zero
    intro hz
    have hc := congrArg (fun P : ℚ[X] => P.coeff 0) hz
    norm_num [escape] at hc
  simp_rw [primitive_term_fraction]
  simp only [primitiveLowNumerator, primitiveLowTail, map_add, map_sub, map_mul,
    map_pow, map_sum, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  norm_num [Fin.sum_univ_succ, nativeStateTermWeight, WPReview.nativeCoefficient,
    primitiveDenominatorScalar, primitiveDenominatorOrder, Fin.ext_iff,
    map_neg, map_mul, map_pow, map_div₀, map_ratCast, _root_.map_ofNat]
  have h3 : Fin.succ (2 : Fin 5)=(3 : Fin 6) := by decide
  have h4 : (Fin.succ (2 : Fin 4)).succ=(4 : Fin 6) := by decide
  have h5 : (Fin.succ (2 : Fin 3)).succ.succ=(5 : Fin 6) := by decide
  simp only [h3, h4, h5, symbol, RatFunc.algebraMap_X] at *
  field_simp [hx, he]
  ring

theorem primitive_low_numerator_coeff_zero : primitiveLowNumerator.coeff 0=0 := by
  dsimp only [primitiveLowNumerator, primitiveNumerator, Matrix.cons_val]
  norm_num [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul']

theorem primitive_low_numerator_coeff_one : primitiveLowNumerator.coeff 1=0 := by
  dsimp only [primitiveLowNumerator, primitiveNumerator, Matrix.cons_val]
  norm_num [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow_mul']

theorem primitive_low_numerator_X_sq_dvd : (X : ℚ[X])^2∣primitiveLowNumerator := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  have hk' : k=0 ∨ k=1 := by omega
  rcases hk' with rfl | rfl
  · exact primitive_low_numerator_coeff_zero
  · exact primitive_low_numerator_coeff_one

theorem primitive_low_divX_X_dvd : (X : ℚ[X])∣primitiveLowNumerator.divX := by
  apply X_dvd_iff.mpr
  simpa only [coeff_divX] using primitive_low_numerator_coeff_one

theorem primitive_low_divX_attachment :
    X*primitiveLowNumerator.divX=primitiveLowNumerator := by
  simpa only [primitive_low_numerator_coeff_zero, C_0, add_zero]
    using X_mul_divX_add primitiveLowNumerator

theorem primitive_low_pair_regular :
    (∑ i : Fin 6, nativePrimitiveTerm 0 i)+(∑ i : Fin 6, nativePrimitiveTerm 1 i) =
      algebraMap ℚ[X] (RatFunc ℚ) primitiveLowNumerator.divX /
        algebraMap ℚ[X] (RatFunc ℚ) (escape^2) := by
  rw [primitive_low_pair_fraction]
  conv_lhs => rw [← primitive_low_divX_attachment, map_mul]
  have hx : algebraMap ℚ[X] (RatFunc ℚ) X≠0 := RatFunc.algebraMap_ne_zero X_ne_zero
  change (algebraMap ℚ[X] (RatFunc ℚ) X)*
    (algebraMap ℚ[X] (RatFunc ℚ) primitiveLowNumerator.divX) /
      ((algebraMap ℚ[X] (RatFunc ℚ) X)*algebraMap ℚ[X] (RatFunc ℚ) (escape^2)) = _
  rw [mul_div_mul_left _ _ hx]

theorem primitive_high_term_regular (n : ℕ) (hn : 2≤n) (i : Fin 6) :
    nativePrimitiveTerm n i=algebraMap ℚ[X] (RatFunc ℚ) (primitiveHighNumerator n i)/
      algebraMap ℚ[X] (RatFunc ℚ) (escape^2) := by
  have ho : primitiveDenominatorOrder i≤4 := by
    fin_cases i <;> norm_num [primitiveDenominatorOrder]
  have hs : primitiveDenominatorScalar i≠0 := by
    fin_cases i <;> norm_num [primitiveDenominatorScalar]
  have hx : symbol≠0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have he : algebraMap ℚ[X] (RatFunc ℚ) escape≠0 := by
    apply RatFunc.algebraMap_ne_zero
    intro hz
    have hc := congrArg (fun P : ℚ[X] => P.coeff 0) hz
    norm_num [escape] at hc
  have hpow : symbol^(3*n)=symbol^(3*n-primitiveDenominatorOrder i)*
      symbol^primitiveDenominatorOrder i := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [primitive_term_fraction]
  simp only [primitiveHighNumerator, map_mul, map_pow, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X]
  simp only [symbol, RatFunc.algebraMap_X] at hpow hx ⊢
  rw [hpow]
  simp only [map_div₀, map_mul, map_pow]
  have hsC : RatFunc.C (primitiveDenominatorScalar i)≠0 := by
    intro hz
    apply hs
    exact RatFunc.C_injective (by simpa only [map_zero] using hz)
  field_simp [hx, he, hsC]

theorem primitive_high_numerator_X_squared (n : ℕ) (hn : 2≤n) (i : Fin 6) :
    (X : ℚ[X])^2∣primitiveHighNumerator n i := by
  have ho : primitiveDenominatorOrder i≤4 := by
    fin_cases i <;> norm_num [primitiveDenominatorOrder]
  apply X_pow_dvd_iff.mpr
  intro k hk
  have hexp : 2≤3*n-primitiveDenominatorOrder i := by omega
  simp only [primitiveHighNumerator, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', if_neg (by omega : ¬3*n-primitiveDenominatorOrder i≤k), mul_zero]

theorem actual_native_primitive_numerator (p : ℕ) (hp : 2≤p) :
    nativePrimitive p=algebraMap ℚ[X] (RatFunc ℚ) (nativePrimitiveNumerator p)/
      algebraMap ℚ[X] (RatFunc ℚ) (escape^2) := by
  classical
  rw [actual_primitive_finite_expansion,
    ← Finset.sum_range_add_sum_Ico (fun n => ∑ i : Fin 6, nativePrimitiveTerm n i) hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [primitive_low_pair_regular]
  have hhigh : (∑ n∈Finset.Ico 2 p, ∑ i : Fin 6, nativePrimitiveTerm n i)=
      (∑ n∈Finset.Ico 2 p, ∑ i : Fin 6,
        algebraMap ℚ[X] (RatFunc ℚ) (primitiveHighNumerator n i))/
          algebraMap ℚ[X] (RatFunc ℚ) (escape^2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    exact primitive_high_term_regular n (Finset.mem_Ico.mp hn).1 i
  rw [hhigh, ← add_div]
  simp only [nativePrimitiveNumerator, map_add, map_sum]

theorem native_primitive_numerator_X_dvd (p : ℕ) :
    (X : ℚ[X])∣nativePrimitiveNumerator p := by
  classical
  unfold nativePrimitiveNumerator
  apply dvd_add primitive_low_divX_X_dvd
  apply Finset.dvd_sum
  intro n hn
  apply Finset.dvd_sum
  intro i _hi
  have hX2 : (X : ℚ[X])∣X^2 := ⟨X, by ring⟩
  exact dvd_trans hX2
    (primitive_high_numerator_X_squared n (Finset.mem_Ico.mp hn).1 i)

theorem primitive_numerator_degree_uniform (i : Fin 6) :
    (primitiveNumerator i).natDegree≤11 := by
  fin_cases i <;> norm_num [primitiveNumerator]
  all_goals compute_degree!

theorem primitive_low_divX_degree : primitiveLowNumerator.divX.natDegree≤13 := by
  have ht : primitiveLowTail.natDegree≤11 := by
    unfold primitiveLowTail
    apply natDegree_sum_le_of_forall_le
    intro i _hi
    split_ifs
    · simp
    · exact (natDegree_C_mul_le _ _).trans (primitive_numerator_degree_uniform i)
  have hl : primitiveLowNumerator.natDegree≤14 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_C_mul_le _ _).trans
      apply (natDegree_sub_le _ _).trans
      exact (max_le (primitive_numerator_degree_uniform 3)
        ((natDegree_C_mul_le _ _).trans (primitive_numerator_degree_uniform 2))).trans (by omega)
    · calc
        _≤(X^3 : ℚ[X]).natDegree+primitiveLowTail.natDegree := natDegree_mul_le
        _≤3+11 := by rw [natDegree_X_pow]; omega
        _=14 := rfl
  rw [natDegree_divX_eq_natDegree_tsub_one]
  omega

theorem primitive_high_numerator_degree (n : ℕ) (hn : 2≤n) (i : Fin 6) :
    (primitiveHighNumerator n i).natDegree≤3*n+10 := by
  have ho : 1≤primitiveDenominatorOrder i := by
    fin_cases i <;> norm_num [primitiveDenominatorOrder]
  let a : ℚ := nativeStateTermWeight n i*WPReview.nativeCoefficient n^2*
    (729/15625 : ℚ)^n/primitiveDenominatorScalar i
  let d : ℕ := 3*n-primitiveDenominatorOrder i
  have ha : (C a*X^d : ℚ[X]).natDegree≤d := natDegree_C_mul_X_pow_le a d
  have hN : (primitiveNumerator i).natDegree≤11 := primitive_numerator_degree_uniform i
  change (C a*X^d*primitiveNumerator i).natDegree≤3*n+10
  calc
    _≤(C a*X^d : ℚ[X]).natDegree+(primitiveNumerator i).natDegree :=
      Polynomial.natDegree_mul_le (p:=C a*X^d) (q:=primitiveNumerator i)
    _≤d+11 := Nat.add_le_add ha hN
    _≤3*n+10 := by dsimp only [d]; omega

/-- The actual numerator has a proved cap; the final endpoint does not assume one. -/
theorem native_primitive_numerator_degree (p : ℕ) (hp : 2≤p) :
    (nativePrimitiveNumerator p).natDegree≤3*p+7 := by
  classical
  unfold nativePrimitiveNumerator
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact primitive_low_divX_degree.trans (by omega)
  · apply natDegree_sum_le_of_forall_le
    intro n hn
    apply natDegree_sum_le_of_forall_le
    intro i _hi
    have hnI := Finset.mem_Ico.mp hn
    exact (primitive_high_numerator_degree n hnI.1 i).trans (by omega)

end

end WPLiteralAdapter
