import WPActualConductorEscape

namespace WPForcedSourceStokes

noncomputable section

theorem precisionZero_neg (p k : ℕ) (a : ℚ) (ha : precisionZero p k a) :
    precisionZero p k (-a) := by
  rcases ha with ha | ha
  · exact Or.inl (by rw [ha, neg_zero])
  · exact Or.inr (by simpa only [padicValRat.neg] using ha)

/-- The literal endpoint times each of the last three native coefficients has precision six. -/
theorem actual_endpoint_top_three_precision (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hn : n<p) (hh : p-3≤n) :
    precisionZero p 6 (WPReview.nativeEndpoint p*WPReview.nativeCoefficient n) := by
  by_cases he : WPReview.nativeEndpoint p=0
  · exact Or.inl (by rw [he, zero_mul])
  apply Or.inr
  rw [padicValRat.mul he (WPNativeMomentIntegrality.nativeCoefficient_ne_zero n),
    actual_native_endpoint_valuation p (by omega), native_top_three_valuation p n hp hn hh]
  norm_num

/-- Every actual theta weight preserves the precision of the selected endpoint term. -/
theorem actual_endpoint_weighted_top_three_precision (p n i : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hn : n<p) (hh : p-3≤n) :
    precisionZero p 6
      (WPReview.nativeEndpoint p*((n : ℚ)^i*WPReview.nativeCoefficient n)) := by
  have hr : (n : ℚ)^i ∈ WPFiniteConductorPolynomial.integralSubring p :=
    (WPFiniteConductorPolynomial.integralSubring p).pow_mem
      (natCast_mem (WPFiniteConductorPolynomial.integralSubring p) n) i
  have heq : WPReview.nativeEndpoint p*((n : ℚ)^i*WPReview.nativeCoefficient n) =
      (WPReview.nativeEndpoint p*WPReview.nativeCoefficient n)*(n : ℚ)^i := by ring
  rw [heq]
  exact precisionZero_mul_integral p 6 _ _
    (actual_endpoint_top_three_precision p n hp hn hh) hr

/-- Both selected high native factors give precision six in the extended conductor endpoint. -/
theorem actual_two_top_three_precision (p n m : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hn : n<p) (hm : m<p) (hhn : p-3≤n) (hhm : p-3≤m) :
    precisionZero p 6 (WPReview.nativeCoefficient n*WPReview.nativeCoefficient m) := by
  apply Or.inr
  rw [padicValRat.mul (WPNativeMomentIntegrality.nativeCoefficient_ne_zero n)
      (WPNativeMomentIntegrality.nativeCoefficient_ne_zero m),
    native_top_three_valuation p n hp hn hhn, native_top_three_valuation p m hp hm hhm]
  norm_num

end

end WPForcedSourceStokes
