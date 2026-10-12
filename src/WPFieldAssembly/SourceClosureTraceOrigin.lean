import WPFieldAssembly.LaurentPoleField

open scoped LaurentPolynomial PowerSeries
open LaurentPolynomial

namespace WPFieldAssembly.SourceClosureTraceOrigin

/- These are the literal origin coefficients of Abar^(-m). The full
   reciprocal power is retained; no Laurent support bound is assumed. -/

noncomputable def originWeight (p m : ℕ) [Fact p.Prime] (n : ℤ) : ZMod p :=
  (-1/4 : ZMod p)^m * LaurentPoleField.fieldZcoeff p (-n-1)
    (LaurentPoleField.fieldReciprocal p^m)

noncomputable def originTrace (p m : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (Finsupp.linearCombination (ZMod p) (originWeight p m)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem originTrace_monomial (p m : ℕ) [Fact p.Prime] (d : ZMod p) (n : ℤ) :
    originTrace p m (LaurentPolynomial.C d*T n)=d*originWeight p m n := by
  rw [←single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single n d)=_
  rw [Finsupp.linearCombination_single,smul_eq_mul]

theorem originTrace_C_mul (p m : ℕ) [Fact p.Prime] (d : ZMod p)
    (F : (ZMod p)[T;T⁻¹]) :
    originTrace p m (LaurentPolynomial.C d*F)=d*originTrace p m F := by
  simpa only [smul_eq_C_mul,smul_eq_mul] using (originTrace p m).map_smul d F

/-- Exact infinity-to-origin inversion, including every signed coefficient. -/
theorem fieldTrace_origin (p m : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p m F=
      -originTrace p m (T (2*(m : ℤ)-2)*invert F) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    rw [map_add,map_add,mul_add,map_add,hF,hG]
    ring
  | C_mul_T n d =>
    have hinv : invert (LaurentPolynomial.C d*T n)=
        LaurentPolynomial.C d*T (-n) := by
      rw [map_mul,invert_C,invert_T]
    have ht : (T (2*(m : ℤ)-2) : (ZMod p)[T;T⁻¹])*
        (LaurentPolynomial.C d*T (-n))=
          LaurentPolynomial.C d*T (2*(m : ℤ)-2-n) := by
      rw [mul_comm (T (2*(m : ℤ)-2)),mul_assoc,←T_add]
      congr 1
      ring
    rw [LaurentPoleField.fieldTrace_monomial,hinv,
      ht,originTrace_monomial,originWeight,LaurentPoleField.fieldWeight]
    rw [show -(2*(m : ℤ)-2-n)-1=n-(2*(m : ℤ)-1) by ring]
    ring

/-- The actual common denominator p+1 gives the complete origin shift 2p. -/
theorem fieldTrace_successor_origin (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p (p+1) F=
      -originTrace p (p+1) (T (2*(p : ℤ))*invert F) := by
  rw [fieldTrace_origin,
    show 2*((p+1 : ℕ) : ℤ)-2=2*(p : ℤ) by omega]

end WPFieldAssembly.SourceClosureTraceOrigin
