import WPLiteralAdapter.ConductorKernel
import WPLiteralAdapter.SquareGamma

open scoped BigOperators LaurentSeries
open Polynomial HahnSeries WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)
local notation "E" => algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ))

theorem rational_residue_regular_series (f : RatFunc (RatFunc ℚ))
    (A : PowerSeries (RatFunc ℚ)) (hf : E f=(A : LaurentSeries (RatFunc ℚ)))
    (b : ℕ) (hb : 0<b) : rationalResidue (f/bivS^b)=PowerSeries.coeff (b-1) A := by
  have he : f/bivS^b=(1/bivS^b)*f := by ring
  have hpow := actual_laurent_power_quotient 0 b
  simp only [pow_zero] at hpow
  rw [he, rationalResidue, laurentResidue, map_mul, hpow, hf,
    HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  simp only [Nat.cast_zero]
  have hi : ¬(-1-((0 : ℤ)-(b : ℤ))<0) := by omega
  have hn : Int.natAbs (-1-((0 : ℤ)-(b : ℤ)))=b-1 := by omega
  rw [if_neg hi, hn]

/-- Identification of the actual sparse-column residue with the full original numerator. -/
theorem actual_beta_full_numerator (p : ℕ) (hp : 2≤p) :
    actualBetaFunctional p=ι (originalNumerator p (p-2))/ι sourceDivisor := by
  classical
  have hl : lambda≠0 := by
    unfold lambda
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (RatFunc.algebraMap_ne_zero X_ne_zero))
  have hlam : ι lam=lambda := by
    norm_num [lam, lambda, symbol, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_mul, map_pow, map_div₀, _root_.map_ofNat]
  have hm : ι m=firstConductorMean := by
    norm_num [m, firstConductorMean, symbol, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_add, map_sub, map_mul, map_pow, map_div₀, _root_.map_ofNat]
  have hDrepr : RatFunc.C (ι sourceDivisor)=bivX*bivSourceDivisor := by
    norm_num [sourceDivisor, collision, escape, bivSourceDivisor, bivCollision, bivEscape, bivX, symbol,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_mul, map_sub, map_pow, _root_.map_ofNat]
    ring
  have hDo : RatFunc.C (ι sourceDivisor)≠0 := by
    rw [hDrepr]
    exact mul_ne_zero bivX_ne_zero actual_first_source_divisor_ne_zero
  have hD : ι sourceDivisor≠0 := by
    intro hz
    apply hDo
    rw [hz, map_zero]
  let g : RatFunc (RatFunc ℚ) :=
    RatFunc.C (ι G0)+RatFunc.C (ι G1)*bivS+RatFunc.C (ι G2)*bivS^2
  let G : PowerSeries (RatFunc ℚ) :=
    PowerSeries.C (ι G0)+PowerSeries.C (ι G1)*PowerSeries.X+PowerSeries.C (ι G2)*PowerSeries.X^2
  let A : PowerSeries (RatFunc ℚ) := PowerSeries.mk fun k => ι (scaledKernel k)/lambda^(k+1)
  let F : PowerSeries (RatFunc ℚ) := ∑ n∈Finset.range p,
    PowerSeries.C (RatFunc.C (WPReview.nativeCoefficient n))*PowerSeries.X^n
  have hg : E g=(G : LaurentSeries (RatFunc ℚ)) := by
    simp only [g, G, map_add, map_mul, map_pow, rational_laurent_coefficient,
      actual_laurent_s,
      PowerSeries.coe_C, PowerSeries.coe_X]
  have hinv : E bivConductor⁻¹=
      (finiteQuadraticInverse firstConductorMean lambda : LaurentSeries (RatFunc ℚ)) := by
    rw [← actual_first_conductor_quadratic]
    exact finite_quadratic_inverse_laurent firstConductorMean lambda hl
  have hkernelSeries : (1-PowerSeries.X)*G*
      finiteQuadraticInverse firstConductorMean lambda=A := by
    have h := original_kernel_reciprocal_transport ι (by simpa only [hlam] using hl)
    simpa only [G, A, hlam, hm, finiteQuadraticInverse, finiteQuadraticSeries,
      finiteQuadraticPolynomial, Polynomial.coe_add, Polynomial.coe_sub,
      Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X] using h
  have hkernel : E ((1-bivS)*g/bivConductor)=(A : LaurentSeries (RatFunc ℚ)) := by
    have hprod := congrArg (fun H : PowerSeries (RatFunc ℚ) =>
      (H : LaurentSeries (RatFunc ℚ))) hkernelSeries
    simp only [PowerSeries.coe_mul, PowerSeries.coe_sub, PowerSeries.coe_one,
      PowerSeries.coe_X] at hprod
    rw [div_eq_mul_inv, map_mul, map_mul, map_sub, map_one, actual_laurent_s, hg, hinv]
    exact hprod
  have hF : E (finiteNativeJet p bivS 0)=(F : LaurentSeries (RatFunc ℚ)) := by
    have h := finite_native_jet_sum p bivS (0 : Fin 3)
    simp only [Fin.val_zero, pow_zero, one_mul, outer_native_scalar] at h
    rw [h]
    change E (∑ n∈Finset.range p,
      RatFunc.C (RatFunc.C (WPReview.nativeCoefficient n))*bivS^n) =
      (HahnSeries.ofPowerSeries ℤ (RatFunc ℚ))
        (∑ n∈Finset.range p,
          PowerSeries.C (RatFunc.C (WPReview.nativeCoefficient n))*PowerSeries.X^n)
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [map_mul, map_pow, rational_laurent_coefficient, actual_laurent_s,
      HahnSeries.ofPowerSeries_C, PowerSeries.coe_X]
  have hres : rationalResidue ((finiteNativeJet p bivS 0*((1-bivS)*g/bivConductor))/
      bivS^(p-1))=PowerSeries.coeff (p-2) (F*A) := by
    have he : E (finiteNativeJet p bivS 0*((1-bivS)*g/bivConductor)) =
        ((F*A : PowerSeries (RatFunc ℚ)) : LaurentSeries (RatFunc ℚ)) := by
      rw [map_mul, hF, hkernel, ← PowerSeries.coe_mul]
    have h := rational_residue_regular_series
      (finiteNativeJet p bivS 0*((1-bivS)*g/bivConductor)) (F*A) he (p-1) (by omega)
    simpa only [show p-1-1=p-2 by omega] using h
  have hbeta : actualBetaFunctional p=(2*lambda^p/ι sourceDivisor)*
      PowerSeries.coeff (p-2) (F*A) := by
    rw [actual_beta_sparse_native, actual_beta_column_kernel]
    change lambda^p*rationalResidue
      ((2*bivS^2*(1-bivS)*finiteNativeJet p bivS 0)*
        (g/(RatFunc.C (ι sourceDivisor)*bivConductor))/bivS^(p+1)) = _
    have hpw : bivS^(p+1)=bivS^(p-1)*bivS^2 := by
      rw [← pow_add]
      congr 1
      omega
    have hi : (2*bivS^2*(1-bivS)*finiteNativeJet p bivS 0)*
        (g/(RatFunc.C (ι sourceDivisor)*bivConductor))/bivS^(p+1) =
      RatFunc.C (2/ι sourceDivisor)*
        ((finiteNativeJet p bivS 0*((1-bivS)*g/bivConductor))/bivS^(p-1)) := by
      rw [hpw]
      simp only [map_div₀, _root_.map_ofNat]
      field_simp [bivS_ne_zero, hDo, bivConductor_ne_zero]
    rw [hi, rationalResidue_coefficient_mul, hres]
    ring
  have hFsplit : F=(∑ n∈Finset.range (p-1),
      PowerSeries.C (RatFunc.C (WPReview.nativeCoefficient n))*PowerSeries.X^n)+
      PowerSeries.C (RatFunc.C (WPReview.nativeCoefficient (p-1)))*PowerSeries.X^(p-1) := by
    dsimp only [F]
    conv_lhs => rw [show p=(p-1)+1 by omega]
    rw [Finset.sum_range_succ]
  have hcoeff : PowerSeries.coeff (p-2) (F*A)=∑ n∈Finset.range (p-1),
      RatFunc.C (WPReview.nativeCoefficient n)*
        (ι (scaledKernel (p-2-n))/lambda^(p-2-n+1)) := by
    rw [hFsplit, add_mul, map_add]
    have hlast : PowerSeries.coeff (p-2)
        ((PowerSeries.C (RatFunc.C (WPReview.nativeCoefficient (p-1)))*PowerSeries.X^(p-1))*A)=0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
        if_neg (by omega), mul_zero]
    rw [hlast, add_zero, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnle : n≤p-2 := by have := Finset.mem_range.mp hn; omega
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos hnle]
    simp only [A, PowerSeries.coeff_mk]
  apply (eq_div_iff hD).mpr
  have hcancel (z : RatFunc ℚ) :
      ((2*lambda^p/ι sourceDivisor)*z)*ι sourceDivisor=2*lambda^p*z := by field_simp [hD]
  rw [hbeta, hcoeff, hcancel, Finset.mul_sum]
  unfold originalNumerator
  rw [show p-2+1=p-1 by omega, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n≤p-2 := by have := Finset.mem_range.mp hn; omega
  have hpw : p=(p-2-n+1)+(n+1) := by omega
  have hlpow : lambda^p=lambda^(p-2-n+1)*lambda^(n+1) := by
    conv_lhs => rw [hpw]
    exact pow_add _ _ _
  simp only [map_mul, map_pow, RatFunc.algebraMap_C, hlam, _root_.map_ofNat]
  rw [hlpow]
  field_simp [hl]

/-- Exact cancellation of x^5 retains both original top terms. -/
theorem actual_full_numerator_regularized (p : ℕ) (hp : 4 ≤ p) :
    actualBetaFunctional p =
      ι (conductorRegularDenominator * Be p (p - 4) +
        retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0) /
      ι conductorRegularDenominator := by
  have hD : sourceDivisor = X ^ 5 * conductorRegularDenominator := by
    unfold sourceDivisor conductorRegularDenominator
    ring
  have hx : ι (X ^ 5) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 5 X_ne_zero)
  rw [actual_beta_full_numerator p (by omega),
    original_full_numerator_regularized p hp, hD]
  simp only [map_mul]
  exact mul_div_mul_left _ _ hx

end

end WPLiteralAdapter
