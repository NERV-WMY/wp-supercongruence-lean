import WPActualConductorRows
import WPFiniteNativeJet

open scoped BigOperators

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

local instance tensorIntAlgebra : Algebra ℤ (RatFunc (RatFunc ℚ)) :=
  Ring.toIntAlgebra (RatFunc (RatFunc ℚ))

noncomputable def actualNativeTensor (p : ℕ) (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  finiteNativeJet p bivS i * finiteNativeJet p bivB j

noncomputable def actualAngularResidual (p : ℕ) (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  -(algebraMap ℚ (RatFunc (RatFunc ℚ)) (WPReview.nativeEndpoint p) / bivS) *
    ((if i = 2 then bivS^p/(1-bivS) * finiteNativeJet p bivB j else 0) -
      (if j = 2 then bivB^p/(1-bivB) * finiteNativeJet p bivS i else 0))

noncomputable def actualRadialResidual (p : ℕ) (i j : Fin 3) : RatFunc (RatFunc ℚ) :=
  -(3*algebraMap ℚ (RatFunc (RatFunc ℚ)) (WPReview.nativeEndpoint p) / bivX) *
    (if j = 2 then bivB^p/(1-bivB) * finiteNativeJet p bivS i else 0)

noncomputable def actualTensorPairing (p : ℕ)
    (r : Fin 3 → Fin 3 → RatFunc (RatFunc ℚ)) : RatFunc (RatFunc ℚ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, r i j * actualNativeTensor p i j

noncomputable def actualResidualPairing
    (r e : Fin 3 → Fin 3 → RatFunc (RatFunc ℚ)) : RatFunc (RatFunc ℚ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, r i j * e i j

theorem bivLambda_ne_zero : bivLambda ≠ 0 := by
  rw [bivLambda]
  have hl : lambda ≠ 0 := by
    simp only [lambda]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3
      (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))
  simpa only [map_zero] using (RatFunc.C_injective (K := RatFunc ℚ)).ne hl

theorem bivB_ne_zero : bivB ≠ 0 := div_ne_zero bivLambda_ne_zero bivS_ne_zero

theorem biv_one_sub_s_ne_zero : 1-bivS ≠ 0 := by
  have h : bivS-1 ≠ 0 := by simpa using bivS_sub_coefficient_ne_zero 1
  simpa only [neg_sub] using neg_ne_zero.mpr h

theorem biv_one_sub_b_ne_zero : 1-bivB ≠ 0 := by
  have h : 1-bivB = (bivS-bivLambda)/bivS := by
    unfold bivB
    field_simp [bivS_ne_zero]
  rw [h]
  exact div_ne_zero (bivS_sub_coefficient_ne_zero lambda) bivS_ne_zero

theorem partialS_bivB : partialS bivB = -bivB/bivS := by
  simp only [bivB, bivLambda, bivS, Derivation.leibniz_div,
    partialS_coefficient, partialS_s, smul_eq_mul]
  ring

theorem partialX_bivB : partialX bivB = 3*bivB/bivX := by
  rw [bivB, Derivation.leibniz_div]
  simp only [bivS, partialX_s, smul_eq_mul, mul_zero, sub_zero]
  have h : partialX bivLambda = (2187/15625)*bivX^2 := by
    have hl : bivLambda = (729/15625)*bivX^3 := by
      simp only [bivLambda, lambda, bivX, map_mul, map_pow, map_div₀, _root_.map_ofNat]
    rw [hl]
    norm_num [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
      smul_eq_mul, nsmul_eq_mul, bivX]
    ring
  rw [h]
  simp only [bivLambda, lambda, bivX, map_mul, map_pow, map_div₀, _root_.map_ofNat]
  field_simp [bivX_ne_zero, bivS_ne_zero]
  ring

theorem actual_tensor_s_derivative (p : ℕ) (hp : 0<p) (i j : Fin 3) :
    partialS (actualNativeTensor p i j) =
      ((∑ u : Fin 3, bivNativeMatrix bivS i u * actualNativeTensor p u j) -
        (∑ v : Fin 3, bivNativeMatrix bivB j v * actualNativeTensor p i v))/bivS +
      actualAngularResidual p i j := by
  have hi := finite_native_jet_derivative (rationalLinearDerivation partialS) p hp
    bivS bivS_ne_zero biv_one_sub_s_ne_zero i
  have hj := finite_native_jet_derivative (rationalLinearDerivation partialS) p hp
    bivB bivB_ne_zero biv_one_sub_b_ne_zero j
  change partialS (finiteNativeJet p bivS i) = _ at hi
  change partialS (finiteNativeJet p bivB j) = _ at hj
  simp only [show rationalLinearDerivation partialS bivS = 1 from partialS_s,
    show rationalLinearDerivation partialS bivB = -bivB/bivS from partialS_bivB] at hi hj
  rw [actualNativeTensor, Derivation.leibniz, hi, hj]
  simp only [smul_eq_mul]
  simp only [actualNativeTensor, actualAngularResidual, bivNativeMatrix,
    finiteNativeMatrix, Fin.sum_univ_succ]
  split_ifs <;> field_simp [bivS_ne_zero, bivB_ne_zero,
    biv_one_sub_s_ne_zero, biv_one_sub_b_ne_zero] <;> ring

theorem actual_tensor_x_derivative (p : ℕ) (hp : 0<p) (i j : Fin 3) :
    partialX (actualNativeTensor p i j) =
      (3/bivX)*(∑ v : Fin 3, bivNativeMatrix bivB j v * actualNativeTensor p i v) +
      actualRadialResidual p i j := by
  have hi := finite_native_jet_derivative (rationalLinearDerivation partialX) p hp
    bivS bivS_ne_zero biv_one_sub_s_ne_zero i
  have hj := finite_native_jet_derivative (rationalLinearDerivation partialX) p hp
    bivB bivB_ne_zero biv_one_sub_b_ne_zero j
  change partialX (finiteNativeJet p bivS i) = _ at hi
  change partialX (finiteNativeJet p bivB j) = _ at hj
  simp only [show rationalLinearDerivation partialX bivS = 0 from partialX_s,
    show rationalLinearDerivation partialX bivB = 3*bivB/bivX from partialX_bivB,
    zero_div, zero_mul] at hi hj
  rw [actualNativeTensor, Derivation.leibniz, hi, hj]
  simp only [smul_eq_mul, mul_zero, add_zero]
  simp only [actualNativeTensor, actualRadialResidual, bivNativeMatrix,
    finiteNativeMatrix, Fin.sum_univ_succ]
  split_ifs <;> field_simp [bivX_ne_zero, bivB_ne_zero,
    biv_one_sub_b_ne_zero] <;> ring

theorem actual_pairing_s_derivative (p : ℕ) (hp : 0<p)
    (r : Fin 3 → Fin 3 → RatFunc (RatFunc ℚ)) :
    partialS (actualTensorPairing p r) =
      actualTensorPairing p (fun i j => partialS (r i j)) +
      actualTensorPairing p (bivRowConnection r) +
      actualResidualPairing r (actualAngularResidual p) := by
  simp only [actualTensorPairing, map_add, Derivation.leibniz, smul_eq_mul,
    actual_tensor_s_derivative p hp, actualResidualPairing, bivRowConnection,
    Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, partialS.map_zero]
  ring

theorem actual_pairing_x_derivative (p : ℕ) (hp : 0<p)
    (r : Fin 3 → Fin 3 → RatFunc (RatFunc ℚ)) :
    partialX (actualTensorPairing p r) =
      actualTensorPairing p (fun i j => partialX (r i j)) +
      (3/bivX)*actualTensorPairing p (bivSecondConnection r) +
      actualResidualPairing r (actualRadialResidual p) := by
  simp only [actualTensorPairing, map_add, Derivation.leibniz, smul_eq_mul,
    actual_tensor_x_derivative p hp, actualResidualPairing, bivSecondConnection,
    Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, partialX.map_zero]
  ring

theorem actual_unintegrated_source_identity (p : ℕ) (hp : 0<p) :
    actualTensorPairing p bivNormalSource =
      -actualTensorPairing p bivConductorR +
      2*(1-bivX)*partialX (actualTensorPairing p bivConductorR) +
      partialS (actualTensorPairing p bivConductorBU - actualTensorPairing p bivEta) -
      2*(1-bivX)*actualResidualPairing bivConductorR (actualRadialResidual p) +
      actualResidualPairing (fun i j => bivEta i j - bivConductorBU i j)
        (actualAngularResidual p) := by
  have hn : actualTensorPairing p bivSourceQ =
      actualTensorPairing p bivNormalSource +
      partialS (actualTensorPairing p bivEta) -
      actualResidualPairing bivEta (actualAngularResidual p) := by
    rw [actual_pairing_s_derivative p hp]
    simp only [actualTensorPairing, actual_angular_source_row_identity,
      add_mul, Finset.sum_add_distrib]
    ring
  have hp' : actualTensorPairing p bivSourceQ =
      -actualTensorPairing p bivConductorR +
      2*(1-bivX)*partialX (actualTensorPairing p bivConductorR) +
      partialS (actualTensorPairing p bivConductorBU) -
      2*(1-bivX)*actualResidualPairing bivConductorR (actualRadialResidual p) -
      actualResidualPairing bivConductorBU (actualAngularResidual p) := by
    rw [actual_pairing_s_derivative p hp, actual_pairing_x_derivative p hp]
    simp only [actualTensorPairing, actual_positive_conductor_row_identity,
      add_mul, Finset.sum_add_distrib, neg_mul, Fin.sum_univ_succ]
    field_simp [bivX_ne_zero]
    ring
  rw [map_sub]
  simp only [actualResidualPairing, sub_mul, Finset.sum_sub_distrib] at hn hp' ⊢
  linear_combination hp' - hn

end

end WPForcedSourceStokes
