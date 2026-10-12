import WPFieldAssembly.ActualKwFieldTrace
import WPFiniteLaurentDifferential

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualKwFieldTrace

namespace WPFieldAssembly.ActualCommonFieldIBP

set_option maxHeartbeats 1200000

/-- Exact differentials have zero Cartier image on their entire signed support. -/
theorem cartier_derivative_zero {K : Type*} [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (G : K[T;T⁻¹]) :
    WPFiniteCartier.cartier p (Fact.out : p.Prime).pos (D G)=0 := by
  ext k
  rw [WPFiniteCartier.cartier_coeff,D_coeff]
  have hn : (p : ℤ)*(k+1)-1+1=(p : ℤ)*(k+1) := by ring
  rw [hn]
  simp only [Int.cast_mul,Int.cast_natCast,CharP.cast_eq_zero,zero_mul]
  rfl

/-- The complete denominator-p trace kills an exact differential. -/
theorem fieldTrace_derivative_p (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (G : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p p (D G)=0 := by
  have h := LaurentPoleField.trace_frobenius_cartier p 1 hp (D G)
  simpa only [Nat.mul_one,cartier_derivative_zero,map_zero] using h

noncomputable def kwFieldTrace (p : ℕ) [Fact p.Prime]
    (G : (ZMod p)[T;T⁻¹]) : ZMod p :=
  LaurentPoleField.fieldTrace p p (3*(R : (ZMod p)[T;T⁻¹])^p*G)

theorem kwFieldTrace_add (p : ℕ) [Fact p.Prime]
    (G J : (ZMod p)[T;T⁻¹]) :
    kwFieldTrace p (G+J)=kwFieldTrace p G+kwFieldTrace p J := by
  rw [kwFieldTrace,kwFieldTrace,kwFieldTrace,mul_add,map_add]

theorem kwFieldTrace_cartier (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (G : (ZMod p)[T;T⁻¹]) :
    kwFieldTrace p G=3*LaurentPoleField.fieldTrace p 1
      ((R : (ZMod p)[T;T⁻¹])*
        WPFiniteCartier.cartier p (Fact.out : p.Prime).pos G) :=
  fieldKw_trace_cartier p hp G

/-- This identity cancels the shared derivative before either source is evaluated. -/
theorem kwFieldTrace_IBP (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (H U : (ZMod p)[T;T⁻¹]) :
    kwFieldTrace p (D H*U)+kwFieldTrace p (H*D U)=0 := by
  have h : kwFieldTrace p (D (H*U))=0 := by
    rw [kwFieldTrace_cartier p hp,cartier_derivative_zero,mul_zero,map_zero,mul_zero]
  rw [D_mul,kwFieldTrace_add] at h
  exact h

/-- The full common sigma cancels against its original UV derivative source. -/
theorem common_sigma_cancellation (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (H U sigma B : (ZMod p)[T;T⁻¹]) (hU : D U=sigma+B) (logTrace : ZMod p) :
    kwFieldTrace p (H*sigma)+logTrace+kwFieldTrace p (D H*U)=
      logTrace-kwFieldTrace p (H*B) := by
  have h := kwFieldTrace_IBP p hp H U
  rw [hU,mul_add,kwFieldTrace_add] at h
  linear_combination h

end WPFieldAssembly.ActualCommonFieldIBP
