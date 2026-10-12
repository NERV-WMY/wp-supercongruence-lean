import WPActualOrdinaryJet
import WPActualFirstConductorEndpoint
import WPFiniteConductorCoefficient
import WPFullConductorPrecision

open scoped BigOperators
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

theorem actual_conductor_column_zero_sparsity (a : Fin 3) (ha : a≠2) :
    bivBsDivU a 0=0 ∧ bivBU a 0=0 := by
  fin_cases a
  · norm_num [bivBsDivU, bivBU, bivLP, bivRP]
  · norm_num [bivBsDivU, bivBU, bivLP, bivRP]
  · exact (ha rfl).elim

theorem actual_conductor_column_zero_pairing (v : Fin 3 → RatFunc (RatFunc ℚ)) :
    (∑ a : Fin 3, v a*((6*(1-bivX)*bivS/bivX)*bivBsDivU a 0-bivBU a 0)) =
      v 2*((6*(1-bivX)*bivS/bivX)*bivBsDivU 2 0-bivBU 2 0) := by
  classical
  apply Finset.sum_eq_single (2 : Fin 3)
  · intro a _ha ha2
    rcases actual_conductor_column_zero_sparsity a ha2 with ⟨hs, hu⟩
    simp [hs, hu]
  · intro h
    exact (h (Finset.mem_univ (2 : Fin 3))).elim

theorem actual_beta_sparse_native (p : ℕ) :
    actualBetaFunctional p = lambda^p*rationalResidue
      ((2*bivS^2*(1-bivS)*finiteNativeJet p bivS 0)*
        ((6*(1-bivX)*bivS/bivX)*bivBsDivU 2 0-bivBU 2 0)/bivS^(p+1)) := by
  rw [actual_beta_functional_ordinary, actual_conductor_column_zero_pairing,
    actual_native_ordinary_value]
  have hj : Polynomial.aeval bivS (nativeOrdinaryPolynomial p 2) =
      2*bivS^2*(1-bivS)*finiteNativeJet p bivS 0 := by
    dsimp only [nativeOrdinaryPolynomial, Matrix.cons_val]
    norm_num [finiteNativeJet, Polynomial.aeval_def,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      native_algebraMap_rat]
  rw [hj]

/-- The retained scaled kernel recurrence is unchanged under the actual coefficient-field map. -/
theorem original_kernel_series_identity_transport {K : Type*} [Field K]
    (φ : ℚ[X] →+* K) (hl : φ lam≠0) :
    (PowerSeries.X^2-PowerSeries.C (2*φ m)*PowerSeries.X+PowerSeries.C (φ lam))*
      (PowerSeries.mk fun k => φ (scaledKernel k)/(φ lam)^(k+1)) =
      (1-PowerSeries.X)*(PowerSeries.C (φ G0)+PowerSeries.C (φ G1)*PowerSeries.X+
        PowerSeries.C (φ G2)*PowerSeries.X^2) := by
  let A : PowerSeries K := PowerSeries.mk fun k => φ (scaledKernel k)/(φ lam)^(k+1)
  let f : PowerSeries K := PowerSeries.X^2-PowerSeries.C (2*φ m)*PowerSeries.X+
    PowerSeries.C (φ lam)
  let H : PowerSeries K := (1-PowerSeries.X)*
    (PowerSeries.C (φ G0)+PowerSeries.C (φ G1)*PowerSeries.X+PowerSeries.C (φ G2)*PowerSeries.X^2)
  have hin (k : ℕ) : PowerSeries.coeff k H=φ (kernelInput k) := by
    rcases k with (_ | (_ | (_ | (_ | k))))
    all_goals norm_num [H, kernelInput, sub_mul, mul_add, mul_sub, mul_assoc,
      ← pow_succ, map_sub, map_neg, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X]
    all_goals try split_ifs
    all_goals first | omega | ring
  have hstep (k : ℕ) : φ (scaledKernel (k+2)) =
      2*φ m*φ (scaledKernel (k+1))-φ lam*φ (scaledKernel k)+
        (φ lam)^(k+2)*φ (kernelInput (k+2)) := by
    rw [scaledKernel]
    simp only [map_add, map_sub, map_mul, map_pow, _root_.map_ofNat]
  have hX (k : ℕ) : PowerSeries.coeff k (PowerSeries.X*A)=
      if 1≤k then PowerSeries.coeff (k-1) A else 0 := by
    rw [← pow_one (PowerSeries.X : PowerSeries K), PowerSeries.coeff_X_pow_mul']
  have hcoef (k : ℕ) : PowerSeries.coeff k (f*A)=
      (if 2≤k then PowerSeries.coeff (k-2) A else 0)-
      (2*φ m)*(if 1≤k then PowerSeries.coeff (k-1) A else 0)+
      φ lam*PowerSeries.coeff k A := by
    dsimp only [f]
    simp only [sub_mul, add_mul, mul_assoc, map_add, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', hX]
  change f*A=H
  apply PowerSeries.ext
  intro k
  rw [hcoef, hin]
  rcases k with (_ | (_ | k))
  · norm_num [A, scaledKernel, kernelInput,
      map_add, map_sub, map_mul, map_pow, _root_.map_ofNat]
    field_simp [hl]
  · norm_num [A, scaledKernel, kernelInput,
      map_add, map_sub, map_mul, map_pow, _root_.map_ofNat]
    field_simp [hl]
    ring
  · norm_num [A, Nat.add_sub_cancel]
    rw [hstep]
    simp only [pow_succ]
    field_simp [hl]
    rw [show k+1+1-2=k by omega]
    ring

theorem original_kernel_reciprocal_transport {K : Type*} [Field K]
    (φ : ℚ[X] →+* K) (hl : φ lam≠0) :
    ((1-PowerSeries.X)*(PowerSeries.C (φ G0)+PowerSeries.C (φ G1)*PowerSeries.X+
      PowerSeries.C (φ G2)*PowerSeries.X^2))*
      (PowerSeries.X^2-PowerSeries.C (2*φ m)*PowerSeries.X+PowerSeries.C (φ lam))⁻¹ =
      (PowerSeries.mk fun k => φ (scaledKernel k)/(φ lam)^(k+1)) := by
  let f : PowerSeries K := PowerSeries.X^2-PowerSeries.C (2*φ m)*PowerSeries.X+
    PowerSeries.C (φ lam)
  let A : PowerSeries K := PowerSeries.mk fun k => φ (scaledKernel k)/(φ lam)^(k+1)
  let H : PowerSeries K := (1-PowerSeries.X)*
    (PowerSeries.C (φ G0)+PowerSeries.C (φ G1)*PowerSeries.X+PowerSeries.C (φ G2)*PowerSeries.X^2)
  have hf : PowerSeries.constantCoeff f≠0 := by simpa [f] using hl
  have hid : f*A=H := original_kernel_series_identity_transport φ hl
  change H*f⁻¹=A
  calc
    H*f⁻¹=f*A*f⁻¹ := by rw [hid]
    _=A*(f*f⁻¹) := by ring
    _=A := by rw [PowerSeries.mul_inv_cancel _ hf, mul_one]

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

theorem actual_beta_column_kernel :
    (6*(1-bivX)*bivS/bivX)*bivBsDivU 2 0-bivBU 2 0 =
      (RatFunc.C (ι G0)+RatFunc.C (ι G1)*bivS+RatFunc.C (ι G2)*bivS^2)/
        (RatFunc.C (ι sourceDivisor)*bivConductor) := by
  have hD : RatFunc.C (ι sourceDivisor)=bivX*bivSourceDivisor := by
    norm_num [sourceDivisor, collision, escape, bivSourceDivisor, bivCollision, bivEscape, bivX, symbol,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_mul, map_sub, map_pow, _root_.map_ofNat]
    ring
  rw [hD]
  norm_num only [bivBsDivU, bivBU, bivLP, bivRP, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  field_simp [bivX_ne_zero, actual_first_source_divisor_ne_zero, bivConductor_ne_zero]
  norm_num [G0, G1, G2, K, LP20, RP20, m, lam, ell, collision, bivConductorX,
    bivMean, bivMeanX, bivEll, bivEllX, bivCollision, bivX, symbol,
    Polynomial.derivative_mul, Polynomial.derivative_pow_succ, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_add, map_sub, map_mul, map_pow, map_div₀, map_neg, _root_.map_ofNat]
  ring

end

end WPLiteralAdapter
