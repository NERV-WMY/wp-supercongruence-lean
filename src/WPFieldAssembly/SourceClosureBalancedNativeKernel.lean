import WPFieldAssembly.SourceClosureBalancedNativeRatio
import WPFieldAssembly.SourceClosureBalancedNativeSupport
import WPFieldAssembly.SourceClosureLaurentBounds

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureBalancedNativeRatio
  WPFieldAssembly.SourceClosureBalancedNativeSupport
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureLaurentBounds
  WPFieldAssembly.ActualBalancedTrace

namespace WPFieldAssembly.SourceClosureBalancedNativeKernel

set_option maxHeartbeats 1600000

/-- The actual homogeneous quotient keeps exactly the strict three-p support bound.
In particular the second positive and negative Frobenius slots have not been removed. -/
theorem actual_native_balanced_ratio_full_band (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    ∃ R : (ZMod p)[T;T⁻¹],
      actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp=f^2*R ∧
      D R=0 ∧ Above R (3*(p : ℤ)-3) ∧ Above (invert R) (3*(p : ℤ)-3) := by
  let F := NativeChiFieldSource.halfPullbackField p hp
  let f := F.toLaurent
  let N : ℤ := (((p-1)/2 : ℕ) : ℤ)
  let M := actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp
  have hdegree : F.natDegree=3*(p/6) := actual_balanced_multiplier_exact_degree p hp
  have hF : F≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hdegree
    omega
  have hF2 : F^2≠0 := pow_ne_zero 2 hF
  have hF2degree : ((F^2).natDegree : ℤ)=6*((p/6 : ℕ) : ℤ) := by
    rw [natDegree_pow,hdegree]
    push_cast
    ring
  obtain ⟨R,hfactor,hD⟩ := actual_native_balanced_ratio_exists p hp
  change M=f^2*R at hfactor
  have hm := actual_native_balanced_difference_bounds p hp
  have htop : Above ((F^2).toLaurent*R)
      (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-3) := by
    rw [map_pow,←hfactor]
    exact hm.1
  have hR := above_cancel_polynomial (F^2) hF2 R _ htop
  have hr : Above R (3*(p : ℤ)-3) := by
    convert hR using 1
    rw [hF2degree]
    ring
  have hreflect : (F^2).toLaurent*invert R=T (2*N)*invert M := by
    have hf := actual_low_F_weighted_reflection p hp
    change f=T N*invert f at hf
    calc
      (F^2).toLaurent*invert R=f^2*invert R := by rw [map_pow]
      _=(T N*invert f)^2*invert R := by rw [←hf]
      _=T (2*N)*invert (f^2*R) := by
        simp only [map_mul,map_pow,mul_pow,LaurentPolynomial.T_pow,Nat.cast_ofNat]
        ring
      _=T (2*N)*invert M := by rw [←hfactor]
  have hbot : Above ((F^2).toLaurent*invert R)
      (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-3) := by
    rw [hreflect]
    have he := Above_shift hm.2 (2*N)
    convert he using 1
    dsimp only [N]
    ring
  have hRi := above_cancel_polynomial (F^2) hF2 (invert R) _ hbot
  have hri : Above (invert R) (3*(p : ℤ)-3) := by
    convert hRi using 1
    rw [hF2degree]
    ring
  exact ⟨R,hfactor,hD,hr,hri⟩

/-- The original actual carriers differ by all five explicit Frobenius coefficients. -/
theorem actual_native_balanced_five_slots (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    ∃ R : (ZMod p)[T;T⁻¹],
      actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp=f^2*R ∧
      R=LaurentPolynomial.C (R.coeff (-2*(p : ℤ)))*T (-2*(p : ℤ))+
        LaurentPolynomial.C (R.coeff (-(p : ℤ)))*T (-(p : ℤ))+
        LaurentPolynomial.C (R.coeff 0)+
        LaurentPolynomial.C (R.coeff (p : ℤ))*T (p : ℤ)+
        LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*T (2*(p : ℤ)) := by
  obtain ⟨R,hfactor,hD,htop,hbot⟩ := actual_native_balanced_ratio_full_band p hp
  /- The two bounds give |j|≤3p-3. At every nonzero coefficient, D R=0
  forces p to divide j, hence j=-2p,-p,0,p,2p. Both extreme slots survive. -/
  exact ⟨R,hfactor,derivative_kernel_five_expansion p hp R hD htop hbot⟩

end WPFieldAssembly.SourceClosureBalancedNativeKernel
