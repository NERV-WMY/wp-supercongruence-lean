import WPFieldAssembly.SourceClosureVbalParity
import WPFieldAssembly.SourceClosureVbalIR61FourEnds
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPActualRankTwoProper WPFieldAssembly.SourceClosureVbalParity
  WPFieldAssembly.SourceClosureVbalIR61FourEnds

namespace WPFieldAssembly.BalancedVbalSuccessorCrossSupport

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- Every coefficient of the original proper parity polynomial is retained. -/
noncomputable def actualCrossN0 : (ZMod p)[X] :=
  (parityPolynomial p (p/6+1) (properLegendreJacobi p)).comp
    (1-WPHasseIntegralTransport.fieldV p)

noncomputable def actualCrossE : ℕ :=
  ((p-1)/2+1+3*((p/6+1)%2))/2

noncomputable def actualCrossDelta : ℕ := (p-1)/2-3*(p/6)

/-- This finite numerator precedes the original signed Laurent shift. -/
noncomputable def actualCrossPositiveNumerator : (ZMod p)[X] :=
  (4-11*X)*(Polynomial.C (1/5 : ZMod p)*(X+1))^((p/6+1)%2)*
    (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)))^((p/6+1)%2)*actualCrossN0 p

/-- The original branch-cancelled Dx, with its full proper dependence. -/
noncomputable def actualCrossDx : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (6*actualCrossHasseSign p)*T (-(actualCrossE p : ℤ))*
    (actualCrossPositiveNumerator p).toLaurent*invert (actualCrossN0 p).toLaurent

/-- The Hasse-cancelled proper cross is constructed inside the Laurent ring. -/
noncomputable def actualCrossCarrier : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (actualCrossHasseSign p/25)*T (-(actualCrossE p : ℤ))*
    ((Polynomial.C (1/5 : ZMod p)*(X+1))^(p+(p/6+1)%2)*
      (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)))^((p/6+1)%2)*actualCrossN0 p).toLaurent*
        invert (actualCrossN0 p).toLaurent

theorem actual_cross_n0_degree :
    (actualCrossN0 p).natDegree≤
      3*(parityPolynomial p (p/6+1) (properLegendreJacobi p)).natDegree := by
  have hq : (1-WPHasseIntegralTransport.fieldV p : (ZMod p)[X]).natDegree≤3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hq).trans (by omega))

theorem actual_cross_positive_degree :
    (actualCrossPositiveNumerator p).natDegree≤
      1+3*((p/6+1)%2)+
        3*(parityPolynomial p (p/6+1) (properLegendreJacobi p)).natDegree := by
  have hC : (4-11*X : (ZMod p)[X]).natDegree≤1 := by compute_degree
  have hs : (Polynomial.C (1/5 : ZMod p)*(X+1) : (ZMod p)[X]).natDegree≤1 := by compute_degree
  have hbc : (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)) : (ZMod p)[X]).natDegree≤2 := by
    compute_degree
  have hsr : ((Polynomial.C (1/5 : ZMod p)*(X+1))^((p/6+1)%2)).natDegree≤(p/6+1)%2 := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left _ hs).trans (by omega)
  have hbcr : ((Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)))^((p/6+1)%2)).natDegree≤
      2*((p/6+1)%2) := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left _ hbc).trans (by omega)
  exact (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le hC hsr) hbcr)
    (actual_cross_n0_degree p)).trans (by omega)

/-- Both exact support bounds use the actual proper degree and both prime classes. -/
theorem actual_cross_Dx_support (hp : 19≤p) :
    Above (actualCrossDx p) (-1-(actualCrossDelta p : ℤ)/2) ∧
      Above (invert (actualCrossDx p)) (((p-3-actualCrossDelta p : ℕ) : ℤ)/2) := by
  let k := (parityPolynomial p (p/6+1) (properLegendreJacobi p)).natDegree
  let rn := (p/6+1)%2
  have hk : 2*k+rn≤p/6-1 := actual_n_parity_degree p hp
  have hmod := Nat.mod_lt (p/6+1) (by norm_num : 0<2)
  have hclass := WPActualNativeParameter.prime_six_classes p (by omega)
  have hnumU : ((1+3*rn+3*k : ℕ) : ℤ)-(actualCrossE p : ℤ)≤
      -1-(actualCrossDelta p : ℤ)/2 := by
    dsimp only [actualCrossE,actualCrossDelta,rn] at *
    rcases hclass with h1 | h5 <;> omega
  have hnumL : (actualCrossE p : ℤ)+((3*k : ℕ) : ℤ)≤
      (((p-3-actualCrossDelta p : ℕ) : ℤ)/2) := by
    dsimp only [actualCrossE,actualCrossDelta,rn] at *
    rcases hclass with h1 | h5 <;> omega
  have hP := Above_toLaurent _ _ (actual_cross_positive_degree p)
  have hn := Above_toLaurent _ _ (actual_cross_n0_degree p)
  have hinv := LaurentPolynomial.involutive_invert (actualCrossN0 p).toLaurent
  constructor
  · have hb := Above_shift
      (Above_C_mul (Above_mul hP (Above_invert_toLaurent (actualCrossN0 p)))
        (6*actualCrossHasseSign p)) (-(actualCrossE p : ℤ))
    apply Above_mono (a:=((1+3*rn+3*k : ℕ) : ℤ)-(actualCrossE p : ℤ)) _ hnumU
    convert hb using 1 <;>
      first | dsimp only [actualCrossDx]; ring | dsimp only [k,rn]; push_cast; ring
  · have hb := Above_shift
      (Above_C_mul (Above_mul (Above_invert_toLaurent (actualCrossPositiveNumerator p)) hn)
        (6*actualCrossHasseSign p)) (actualCrossE p : ℤ)
    apply Above_mono (a:=(actualCrossE p : ℤ)+((3*k : ℕ) : ℤ)) _ hnumL
    convert hb using 1 <;>
      first | simp only [actualCrossDx,map_mul,invert_C,invert_T,hinv,neg_neg]; ring
            | dsimp only [k,rn]; push_cast; ring

/-- The cleared Dx relation uses no inverse of the original branch coordinate. -/
theorem actual_cross_Dx_cleared (hp : 19≤p) :
    actualCrossDx p*(Polynomial.C (1/5 : ZMod p)*(X+1)).toLaurent^p=
      LaurentPolynomial.C (150 : ZMod p)*(4-11*X : (ZMod p)[X]).toLaurent*
        actualCrossCarrier p := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have hc : (150 : ZMod p)*(actualCrossHasseSign p/25)=6*actualCrossHasseSign p := by
    field_simp [h25]
    ring
  have hcl : LaurentPolynomial.C (150 : ZMod p)*
      LaurentPolynomial.C (actualCrossHasseSign p/25)=
        LaurentPolynomial.C (6*actualCrossHasseSign p) := by rw [←map_mul,hc]
  unfold actualCrossDx actualCrossPositiveNumerator actualCrossCarrier
  rw [←hcl]
  simp only [map_mul,map_pow,pow_add]
  ring

/-- All coefficients of the same cross remain within the two original support ends. -/
theorem actual_cross_carrier_support (hp : 19≤p) :
    Above (actualCrossCarrier p) ((p : ℤ)-2-(actualCrossDelta p : ℤ)/2) ∧
      Above (invert (actualCrossCarrier p)) (((p-3-actualCrossDelta p : ℕ) : ℤ)/2) := by
  let k := (parityPolynomial p (p/6+1) (properLegendreJacobi p)).natDegree
  let rn := (p/6+1)%2
  let U : (ZMod p)[X] := (Polynomial.C (1/5 : ZMod p)*(X+1))^(p+rn)*
    (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)))^rn*actualCrossN0 p
  have hU : U.natDegree≤p+3*rn+3*k := by
    have hs : (Polynomial.C (1/5 : ZMod p)*(X+1) : (ZMod p)[X]).natDegree≤1 := by compute_degree
    have hbc : (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)) : (ZMod p)[X]).natDegree≤2 := by
      compute_degree
    have hsr : ((Polynomial.C (1/5 : ZMod p)*(X+1))^(p+rn)).natDegree≤p+rn := by
      rw [natDegree_pow]
      exact (Nat.mul_le_mul_left _ hs).trans (by omega)
    have hbcr : ((Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X)))^rn).natDegree≤2*rn := by
      rw [natDegree_pow]
      exact (Nat.mul_le_mul_left _ hbc).trans (by omega)
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hsr hbcr)
      (actual_cross_n0_degree p)).trans (by omega)
  have hk : 2*k+rn≤p/6-1 := actual_n_parity_degree p hp
  have hmod := Nat.mod_lt (p/6+1) (by norm_num : 0<2)
  have hclass := WPActualNativeParameter.prime_six_classes p (by omega)
  have hnumU : ((p+3*rn+3*k : ℕ) : ℤ)-(actualCrossE p : ℤ)≤
      (p : ℤ)-2-(actualCrossDelta p : ℤ)/2 := by
    dsimp only [actualCrossE,actualCrossDelta,rn] at *
    rcases hclass with h1 | h5 <;> omega
  have hnumL : (actualCrossE p : ℤ)+((3*k : ℕ) : ℤ)≤
      (((p-3-actualCrossDelta p : ℕ) : ℤ)/2) := by
    dsimp only [actualCrossE,actualCrossDelta,rn] at *
    rcases hclass with h1 | h5 <;> omega
  have hinv := LaurentPolynomial.involutive_invert (actualCrossN0 p).toLaurent
  constructor
  · have hb := Above_shift
      (Above_C_mul (Above_mul (Above_toLaurent U _ hU)
        (Above_invert_toLaurent (actualCrossN0 p))) (actualCrossHasseSign p/25))
          (-(actualCrossE p : ℤ))
    apply Above_mono (a:=((p+3*rn+3*k : ℕ) : ℤ)-(actualCrossE p : ℤ)) _ hnumU
    convert hb using 1 <;>
      first | dsimp only [actualCrossCarrier,U]; ring | dsimp only [k,rn]; push_cast; ring
  · have hb := Above_shift
      (Above_C_mul (Above_mul (Above_invert_toLaurent U)
        (Above_toLaurent _ _ (actual_cross_n0_degree p))) (actualCrossHasseSign p/25))
          (actualCrossE p : ℤ)
    apply Above_mono (a:=(actualCrossE p : ℤ)+((3*k : ℕ) : ℤ)) _ hnumL
    convert hb using 1 <;>
      first | simp only [actualCrossCarrier,U,map_mul,invert_C,invert_T,hinv,neg_neg]; ring
            | dsimp only [k,rn]; push_cast; ring

end WPFieldAssembly.BalancedVbalSuccessorCrossSupport
