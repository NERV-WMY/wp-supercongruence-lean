import WPFiniteLaurentDifferential

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureBalancedPrimitiveReflection

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

theorem weighted_invert_derivative (n : ℤ) (P : K[T;T⁻¹]) :
    D (T n*invert P)=C (n : K)*T (n-1)*invert P-T (n-2)*invert (D P) := by
  have hd : D (T n : K[T;T⁻¹])=C (n : K)*T (n-1) := by
    simpa only [map_one,one_mul] using D_monomial (1 : K) n
  have ht : (T n*T (-2) : K[T;T⁻¹])=T (n-2) := by
    rw [←T_add]
    congr 1
  rw [D_mul,hd,D_invert,mul_neg,←mul_assoc,ht]
  ring

/-- The weighted multiplier reflection cancels its derivative term exactly. -/
theorem weighted_wronskian_reflection (n : ℤ) (f J : K[T;T⁻¹])
    (hf : f=T n*invert f) :
    f*D (T n*invert J)-T n*invert J*D f=
      -T (2*n-2)*invert (f*D J-J*D f) := by
  have hdf := congrArg D hf
  rw [weighted_invert_derivative] at hdf
  have hdJ := weighted_invert_derivative n J
  have ht : (T n*T (n-2) : K[T;T⁻¹])=T (2*n-2) := by
    rw [←T_add]
    congr 1
    omega
  simp only [map_sub,map_mul]
  linear_combination
    f*hdJ-T n*invert J*hdf+
      (C (n : K)*T (n-1)*invert J-T (n-2)*invert (D J))*hf+
        (invert J*invert (D f)-invert f*invert (D J))*ht

/-- The entire local source is reflected, including the harmonic and TB forcings. -/
theorem weighted_proper_source_reflection (n : ℤ)
    (f L U J A TB : K[T;T⁻¹]) (h : K)
    (hf : f=T n*invert f)
    (hL : invert L=T (-5)*L)
    (hU : invert U=T (-n-3)*U)
    (hsource : L*(f*D J-J*D f)=U*(A+C h*f^2+f*TB)) :
    L*(f*D (T n*invert J)-T n*invert J*D f)=
      -U*(T n*invert A+C h*T (-n)*f^2+f*invert TB) := by
  have ht0 : (T (-n)*T n : K[T;T⁻¹])=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  have hfi : invert f=T (-n)*f := by
    linear_combination -T (-n)*hf-invert f*ht0
  have hw := weighted_wronskian_reflection n f J hf
  have hi := congrArg invert hsource
  simp only [map_mul,map_add,map_pow,invert_C,hL,hU,hfi] at hi
  have htL : (T (2*n+3)*T (-5) : K[T;T⁻¹])=T (2*n-2) := by
    rw [←T_add]
    congr 1
    omega
  have htU : (T (2*n+3)*T (-n-3) : K[T;T⁻¹])=T n := by
    rw [←T_add]
    congr 1
    omega
  have htF : (T n*T (-n) : K[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have htF2 : (T n*T (-n)^2 : K[T;T⁻¹])=T (-n) := by
    rw [pow_two,←mul_assoc,htF,one_mul]
  linear_combination
    L*hw-T (2*n+3)*hi+
      L*invert (f*D J-J*D f)*htL-
        U*(invert A+C h*(T (-n)*f)^2+(T (-n)*f)*invert TB)*htU-
          U*C h*f^2*htF2-U*f*invert TB*htF

end WPFieldAssembly.SourceClosureBalancedPrimitiveReflection
