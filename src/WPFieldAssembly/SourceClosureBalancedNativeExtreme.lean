import WPFieldAssembly.SourceClosureBalancedNativeReciprocal
import WPFieldAssembly.SourceClosureLaurentBandCoefficient

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeSupport
  WPFieldAssembly.SourceClosureBalancedNativeReciprocal
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureLaurentBandCoefficient

namespace WPFieldAssembly.SourceClosureBalancedNativeExtreme

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_low_F_square_strict_band (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp^2).natDegree=6*(p/6) ∧
      (NativeChiFieldSource.halfPullbackField p hp^2).natDegree<p := by
  have hd := actual_balanced_multiplier_exact_degree p hp
  /- With d=p/6 the exact degree is 6d. Its prime remainder is positive;
  the two prime classes give 6d=p-1 or p-5, both strictly below p. -/
  have hnot : ¬6∣p := by
    intro h
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h with h | h <;> omega
  have hm : 0<p%6 := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnot (Nat.dvd_of_mod_eq_zero hz)
  have hdiv := Nat.mod_add_div p 6
  have hsquare : ((NativeChiFieldSource.halfPullbackField p hp)^2).natDegree=
      6*(p/6) := by
    rw [natDegree_pow,hd]
    omega
  exact ⟨hsquare,hsquare.trans_lt (by omega)⟩

/-- The actual balanced term vanishes at both detectors by its full asymmetric support.
This is not a replacement of M=Q6-6fE by Q6 away from these two exponents. -/
theorem actual_balanced_product_extreme_zero (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    (6*f*actualBalancedField p hp).coeff (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=0 ∧
      (6*f*actualBalancedField p hp).coeff
        (-2*(p : ℤ)+2*(((p-1)/2 : ℕ) : ℤ)-6*((p/6 : ℕ) : ℤ))=0 := by
  have hn : 2*(((p-1)/2 : ℕ) : ℤ)+1=(p : ℤ) := by
    exact_mod_cast (WPFiniteWSource.half_exponent p hp).symm
  have hf := actual_low_F_bounds p hp
  have hE : Above (actualBalancedField p hp) (4*(((p-1)/2 : ℕ) : ℤ)+1) := by
    intro j hj
    exact actual_balanced_support_field p hp j (Or.inr hj)
  have hEi : Above (invert (actualBalancedField p hp))
      (2*(((p-1)/2 : ℕ) : ℤ)+3*((p/6 : ℕ) : ℤ)+1) := by
    intro j hj
    rw [invert_apply]
    exact actual_balanced_support_field p hp (-j) (Or.inl (by omega))
  have htop : Above (6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      actualBalancedField p hp) (3*((p/6 : ℕ) : ℤ)+4*(((p-1)/2 : ℕ) : ℤ)+1) := by
    have hs := Above_mul (Above_C_mul hf.1 (6 : ZMod p)) hE
    simp only [map_ofNat] at hs
    convert hs using 1
    ring
  have hbot : Above (invert (6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      actualBalancedField p hp)) (2*3*((p/6 : ℕ) : ℤ)+(((p-1)/2 : ℕ) : ℤ)+1) := by
    simp only [map_mul,map_ofNat]
    have hs := Above_mul (Above_C_mul hf.2 (6 : ZMod p)) hEi
    simp only [map_ofNat] at hs
    convert hs using 1
    ring
  constructor
  · exact htop _ (by omega)
  · have he := hbot
      (2*(p : ℤ)-2*(((p-1)/2 : ℕ) : ℤ)+6*((p/6 : ℕ) : ℤ)) (by omega)
    have hj : -(2*(p : ℤ)-2*(((p-1)/2 : ℕ) : ℤ)+6*((p/6 : ℕ) : ℤ))=
        -2*(p : ℤ)+2*(((p-1)/2 : ℕ) : ℤ)-6*((p/6 : ℕ) : ℤ) := by ring
    simpa only [invert_apply,hj] using he

/-- The positive signed detector extracts the SAME unassigned coefficient from Q6. -/
theorem actual_cleared_positive_extreme (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R)
    (hR : R=LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    (actualNativeClearedNumerator p hp).coeff (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=
      R.coeff (2*(p : ℤ))*(NativeChiFieldSource.halfPullbackField p hp).leadingCoeff^2 := by
  have hd := actual_low_F_square_strict_band p hp
  have hc := polynomial_three_band_top
    (NativeChiFieldSource.halfPullbackField p hp^2) p hd.2 R _ _ _ hR
  rw [hd.1,leadingCoeff_pow] at hc
  have hdZ : ((6*(p/6) : ℕ) : ℤ)=6*((p/6 : ℕ) : ℤ) := by
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  rw [hdZ,map_pow] at hc
  have he := congrArg (fun L : (ZMod p)[T;T⁻¹] =>
    L.coeff (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))) hfactor
  rw [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    (actual_balanced_product_extreme_zero p hp).1,sub_zero] at he
  exact he.trans hc

/-- Reflection and the second support exclusion give the matching negative detector. -/
theorem actual_cleared_negative_extreme (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R)
    (hR : R=LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    (actualNativeClearedNumerator p hp).coeff
        (-2*(p : ℤ)+2*(((p-1)/2 : ℕ) : ℤ)-6*((p/6 : ℕ) : ℤ))=
      R.coeff (2*(p : ℤ))*(NativeChiFieldSource.halfPullbackField p hp).leadingCoeff^2 := by
  let N : ℤ := (((p-1)/2 : ℕ) : ℤ)
  let j : ℤ := 2*(p : ℤ)+6*((p/6 : ℕ) : ℤ)
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let M := actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp
  /- Reflection sends the positive detector j to 2N-j. The multiplier
  order 2N-6d is 0 or 4 in the two classes, so the negative detector is
  -2p or -2p+4. This extracts the retained extreme slot; it does not kill it. -/
  have heM := actual_difference_weighted_reflection p hp
  have ht : (T N : (ZMod p)[T;T⁻¹])^2=T (2*N) := by
    rw [T_pow]
    congr 1
  change T N^2*invert M=M at heM
  rw [ht] at heM
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (2*N) j (invert M)
  simp only [map_one,one_mul,invert_apply] at hs
  have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff j) heM
  rw [hs] at he
  have hj : -(j-2*N)=-2*(p : ℤ)+2*(((p-1)/2 : ℕ) : ℤ)-6*((p/6 : ℕ) : ℤ) := by
    dsimp only [j,N]
    ring
  rw [hj] at he
  dsimp only [M,j,f] at he
  simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    (actual_balanced_product_extreme_zero p hp).1,
    (actual_balanced_product_extreme_zero p hp).2,sub_zero] at he
  exact he.trans (actual_cleared_positive_extreme p hp R hfactor hR)

/-- The detector denominator is nonzero for the actual original multiplier. -/
theorem actual_extreme_leading_coefficient_nonzero (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).leadingCoeff^2≠0 := by
  have hd := actual_balanced_multiplier_exact_degree p hp
  have hf : NativeChiFieldSource.halfPullbackField p hp≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hd
    omega
  exact pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hf)

end WPFieldAssembly.SourceClosureBalancedNativeExtreme
