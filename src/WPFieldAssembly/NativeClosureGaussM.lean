import WPFieldAssembly.ActualFirstGreen
import WPFieldAssembly.ActualTC1Family

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualGaussBottom WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualNativeHasse WPActualNativeDegree WPActualPositivePair
  WPActualNativeQuadraticSquare WPFieldAssembly.ActualTC1Family
  WPFieldAssembly.NativeEulerPrimitive WPFieldAssembly.NativeIR28
  WPActualRankTwoHatLift WPActualCMGauss WPActualGaussProper

namespace WPFieldAssembly.NativeClosureGaussM

set_option maxHeartbeats 2200000

section Family
variable {K : Type*} [CommRing K]

noncomputable def A (u : ℕ → K) (m : ℕ) : K[X] := (scaledEta u m).coeff 0
noncomputable def N (u : ℕ → K) (m : ℕ) : K[X] := (properEta u m).coeff 0
noncomputable def B (u : ℕ → K) (m : ℕ) : K[X] := A u m * N u m

private theorem etaNat_coeff_zero (n : ℕ) :
    (n : EtaPoly K).coeff 0 = (n : K[X]) := by
  have hn : (n : EtaPoly K) = C (n : K[X]) := by simp only [_root_.map_natCast]
  rw [hn, coeff_C_zero]

private theorem eta_unit (u : ℕ → K) {m j : ℕ} (hu : UnitsTo u m)
    (hj : 0 < j) (hjm : j ≤ m) : (j : EtaPoly K) * cc (u j) = 1 := by
  simpa only [cc, _root_.map_mul, _root_.map_natCast, _root_.map_one] using
    congrArg (fun a : K => cc a) (hu j hj hjm)

private theorem eta_cancel (u : ℕ → K) {m j : ℕ} (hu : UnitsTo u m)
    (hj : 0 < j) (hjm : j ≤ m) {P Q : EtaPoly K}
    (he : (j : EtaPoly K) * P = (j : EtaPoly K) * Q) : P = Q := by
  linear_combination cc (u j) * he - (P - Q) * eta_unit u hu hj hjm

private theorem eta_cleared (u : ℕ → K) {m j : ℕ} (hu : UnitsTo u m)
    (hj : j + 2 ≤ m) :
    (j + 2 : EtaPoly K) * scaledEta u (j + 2) =
      (((2 * j + 3 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * tx * scaledEta u (j + 1) -
        (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * scaledEta u j ∧
    (j + 2 : EtaPoly K) * properEta u (j + 2) =
      (((2 * j + 3 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * tx * properEta u (j + 1) -
        (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * properEta u j := by
  have hunit := eta_unit u hu (by omega : 0 < j + 2) hj
  simp only [Nat.cast_add, Nat.cast_ofNat] at hunit
  constructor
  · rw [scaledEta, etaStep, ← mul_assoc, hunit, one_mul]
  · rw [properEta, etaStep, ← mul_assoc, hunit, one_mul]

/-- The adjacent identities retain the same scaled and proper ActualTC1Family.eta sources. -/
theorem family_eta_ladders (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    ∀ j, j + 1 ≤ m →
    tq * DT (scaledEta u j) =
      (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * tx * scaledEta u j -
        (j + 1 : EtaPoly K) * scaledEta u (j + 1) ∧
    tq * DT (scaledEta u (j + 1)) =
      (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * scaledEta u j -
        (j + 1 : EtaPoly K) * tx * scaledEta u (j + 1) ∧
    tq * DT (properEta u j) =
      (j + 1 : EtaPoly K) * (tx * properEta u j - properEta u (j + 1)) -
        scaledEta u j ∧
    tq * DT (properEta u (j + 1)) =
      (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) *
        (properEta u j - tx * properEta u (j + 1)) - scaledEta u (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro _
      simp only [scaledEta, properEta, DT_mul, DT_tx, DT_eta, DT_one,
        _root_.map_sub, _root_.map_zero, _root_.map_neg, tq]
      constructor
      · ring
      constructor
      · ring
      constructor <;> ring
  | succ j ih =>
      intro hj
      obtain ⟨hLa, hUa, hLn, hUn⟩ := ih (by omega)
      obtain ⟨hRa, hRn⟩ := eta_cleared u hu (by omega : j + 2 ≤ m)
      have hDa := congrArg (fun P : EtaPoly K => DT P) hRa
      have hDn := congrArg (fun P : EtaPoly K => DT P) hRn
      have hD2 : DT (2 : EtaPoly K) = 0 := by
        simpa only [Nat.cast_ofNat] using (DT_nat (K := K) 2)
      simp only [DT_mul, DT_nat, DT_tx, DT_eta, hD2, _root_.map_sub,
        _root_.map_add, zero_add] at hDa hDn
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        at hLa hUa hLn hUn hRa hRn hDa hDn ⊢
      dsimp only [tq] at hLa hUa hLn hUn ⊢
      constructor
      · linear_combination hUa + hRa
      constructor
      · apply eta_cancel u hu (by omega : 0 < j + 2) (by omega : j + 2 ≤ m)
        simp only [Nat.cast_add, Nat.cast_ofNat]
        linear_combination (1 - tx ^ 2) * hDa +
          ((2 * (j : EtaPoly K) + 3) - ActualTC1Family.eta) * tx * hUa -
          (((j : EtaPoly K) + 1) - ActualTC1Family.eta) * hLa +
          ((j : EtaPoly K) + 2) * tx * hRa
      constructor
      · linear_combination hUn + hRn
      · apply eta_cancel u hu (by omega : 0 < j + 2) (by omega : j + 2 ≤ m)
        simp only [Nat.cast_add, Nat.cast_ofNat]
        linear_combination (1 - tx ^ 2) * hDn +
          ((2 * (j : EtaPoly K) + 3) - ActualTC1Family.eta) * tx * hUn -
          (((j : EtaPoly K) + 1) - ActualTC1Family.eta) * hLn +
          (((j : EtaPoly K) + 2) - ActualTC1Family.eta) * tx * hRn + hRa

theorem family_ladders (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m)
    (j : ℕ) (hj : j + 1 ≤ m) :
    (1 - X ^ 2) * (A u j).derivative =
      C ((j + 1 : ℕ) : K) * (X * A u j - A u (j + 1)) ∧
    (1 - X ^ 2) * (A u (j + 1)).derivative =
      C ((j + 1 : ℕ) : K) * (A u j - X * A u (j + 1)) ∧
    (1 - X ^ 2) * (N u j).derivative =
      C ((j + 1 : ℕ) : K) * (X * N u j - N u (j + 1)) - A u j ∧
    (1 - X ^ 2) * (N u (j + 1)).derivative =
      C ((j + 1 : ℕ) : K) * (N u j - X * N u (j + 1)) - A u (j + 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := family_eta_ladders u m hu j hj
  have h := fun (he : (tq : EtaPoly K) * DT (scaledEta u j) =
      (((j + 1 : ℕ) : EtaPoly K) - ActualTC1Family.eta) * tx * scaledEta u j -
        (j + 1 : EtaPoly K) * scaledEta u (j + 1)) =>
    congrArg (fun P : EtaPoly K => P.eval 0) he
  have h0' := h h0
  have h1' := congrArg (fun P : EtaPoly K => P.eval 0) h1
  have h2' := congrArg (fun P : EtaPoly K => P.eval 0) h2
  have h3' := congrArg (fun P : EtaPoly K => P.eval 0) h3
  simp only [eval_mul, eval_sub, eval_pow, eval_one, eval_natCast, tq, tx, ActualTC1Family.eta,
    eval_C, eval_X, sub_zero, ← coeff_zero_eq_eval_zero, DT_coeff,
    coeff_add, etaNat_coeff_zero, coeff_one, ite_true] at h0' h1' h2' h3'
  simp only [Nat.cast_add, Nat.cast_one] at h0' h1' h3'
  have hcast : C ((j + 1 : ℕ) : K) = (j : K[X]) + 1 := by simp
  dsimp only [A, N]
  rw [hcast]
  constructor
  · linear_combination h0'
  constructor
  · linear_combination h1'
  exact ⟨h2', h3'⟩

noncomputable def Hpull (u : ℕ → K) (m : ℕ) : K[X] :=
  ∑ j ∈ Finset.range m, C (u (j + 1)) * (A u (j + 1) ^ 2 + A u j ^ 2 - 2)
noncomputable def Mfamily (u : ℕ → K) (m : ℕ) : K[X] :=
  -2 * ∑ j ∈ Finset.range m, C (u (j + 1)) * (B u (j + 1) + B u j)

theorem Hpull_succ (u : ℕ → K) (m : ℕ) :
    Hpull u (m + 1) = Hpull u m +
      C (u (m + 1)) * (A u (m + 1) ^ 2 + A u m ^ 2 - 2) := by
  simp only [Hpull, Finset.sum_range_succ]
theorem Mfamily_succ (u : ℕ → K) (m : ℕ) :
    Mfamily u (m + 1) = Mfamily u m -
      2 * C (u (m + 1)) * (B u (m + 1) + B u m) := by
  simp only [Mfamily, Finset.sum_range_succ]
  ring

theorem family_product_sources (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m)
    (j : ℕ) (hj : j + 1 ≤ m) :
    (1 - X ^ 2) * (A u (j + 1) ^ 2 + A u j ^ 2).derivative =
      -2 * C ((j + 1 : ℕ) : K) * X * (A u (j + 1) ^ 2 - A u j ^ 2) ∧
    (1 - X ^ 2) * (B u (j + 1) + B u j).derivative =
      -2 * C ((j + 1 : ℕ) : K) * X * (B u (j + 1) - B u j) -
        A u (j + 1) ^ 2 - A u j ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := family_ladders u m hu j hj
  constructor
  · simp only [derivative_add, pow_two, derivative_mul]
    linear_combination 2 * A u (j + 1) * h1 + 2 * A u j * h0
  · simp only [B, derivative_add, derivative_mul]
    linear_combination N u (j + 1) * h1 + A u (j + 1) * h3 +
      N u j * h0 + A u j * h2

theorem Hpull_source (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    (1 - X ^ 2) * (Hpull u m).derivative = -2 * X * (A u m ^ 2 - 1) := by
  induction m with
  | zero => simp [Hpull, A, scaledEta]
  | succ m ih =>
      have hunit : C (u (m + 1)) * C ((m + 1 : ℕ) : K) = (1 : K[X]) := by
        rw [← C_mul, mul_comm, hu (m + 1) (by omega) le_rfl, C_1]
      have hs := (family_product_sources u (m + 1) hu m le_rfl).1
      have hi := ih (fun j hj hjm => hu j hj (by omega))
      rw [Hpull_succ, derivative_add, derivative_C_mul, derivative_sub, derivative_ofNat]
      linear_combination hi + C (u (m + 1)) * hs -
        2 * X * (A u (m + 1) ^ 2 - A u m ^ 2) * hunit

theorem Mfamily_source (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    (1 - X ^ 2) * (Mfamily u m).derivative =
      2 * Hpull u m + 4 * X * B u m + 4 * C (harmonic u m) := by
  induction m with
  | zero => simp [Mfamily, Hpull, B, A, N, scaledEta, properEta, harmonic]
  | succ m ih =>
      have hunit : C (u (m + 1)) * C ((m + 1 : ℕ) : K) = (1 : K[X]) := by
        rw [← C_mul, mul_comm, hu (m + 1) (by omega) le_rfl, C_1]
      have hs := (family_product_sources u (m + 1) hu m le_rfl).2
      have hi := ih (fun j hj hjm => hu j hj (by omega))
      rw [Mfamily_succ, Hpull_succ]
      simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
        zero_mul, zero_add, harmonic, Finset.sum_range_succ, _root_.map_add] at *
      linear_combination hi - 2 * C (u (m + 1)) * hs +
        4 * X * (B u (m + 1) - B u m) * hunit

theorem Hpull_one (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    (Hpull u m).eval 1 = 0 := by
  simp only [Hpull, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hunit : UnitsTo u (j + 1) := fun k hk hkj => hu k hk
    (by have := Finset.mem_range.mp hj; omega)
  have hunit0 : UnitsTo u j := fun k hk hkj => hunit k hk (by omega)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_ofNat, A,
    scaledEta_origin_endpoint u (j + 1) hunit, scaledEta_origin_endpoint u j hunit0]
  ring

theorem Mfamily_one (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    (Mfamily u m).eval 1 = 2 * harmonic u m ^ 2 := by
  induction m with
  | zero => simp [Mfamily, harmonic]
  | succ m ih =>
      have hum : UnitsTo u m := fun j hj hjm => hu j hj (by omega)
      rw [Mfamily_succ, eval_sub, ih hum]
      simp only [eval_mul, eval_ofNat, eval_C, eval_add, B, A, N,
        scaledEta_origin_endpoint u (m + 1) hu, scaledEta_origin_endpoint u m hum,
        properEta_origin_endpoint u (m + 1) hu, properEta_origin_endpoint u m hum,
        one_mul, harmonic, Finset.sum_range_succ]
      ring

theorem B_zero (u : ℕ → K) (m : ℕ) : (B u m).eval 0 = 0 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [B, A, N, scaledEta, properEta]
  | one => simp [B, A, N, scaledEta, properEta, tx, ActualTC1Family.eta, mul_coeff_zero]
  | more j ih0 _ =>
      have ha : (A u (j + 2)).eval 0 =
          -u (j + 2) * ((j + 1 : ℕ) : K) * (A u j).eval 0 := by
        simp [A, scaledEta, etaStep, cc, tx, ActualTC1Family.eta, mul_coeff_zero, mul_assoc]
      have hn : (N u (j + 2)).eval 0 =
          -u (j + 2) * ((j + 1 : ℕ) : K) * (N u j).eval 0 := by
        simp [N, properEta, etaStep, cc, tx, ActualTC1Family.eta, mul_coeff_zero, mul_assoc]
      simp only [B, eval_mul] at ih0 ⊢
      rw [ha, hn]
      linear_combination (u (j + 2) * ((j + 1 : ℕ) : K)) ^ 2 * ih0

theorem Mfamily_zero (u : ℕ → K) (m : ℕ) : (Mfamily u m).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [Mfamily, eval_finsetSum, B_zero]

theorem Hpull_degree (u : ℕ → K) (m : ℕ) : (Hpull u m).natDegree ≤ 2 * m := by
  rw [Hpull]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have h1 : (A u (j + 1) ^ 2).natDegree ≤ 2 * m :=
    (natDegree_pow_le_of_le 2 (scaledEta_coeff_degree u (j + 1) 0)).trans (by omega)
  have h0 : (A u j ^ 2).natDegree ≤ 2 * m :=
    (natDegree_pow_le_of_le 2 (scaledEta_coeff_degree u j 0)).trans (by omega)
  have hs : (A u (j + 1) ^ 2 + A u j ^ 2).natDegree ≤ 2 * m := by
    simpa only [max_self] using natDegree_add_le_of_le h1 h0
  have hc : (2 : K[X]).natDegree ≤ 2 * m := by simp
  exact (natDegree_C_mul_le _ _).trans
    (by simpa only [max_self] using natDegree_sub_le_of_le hs hc)

theorem Mfamily_degree (u : ℕ → K) (m : ℕ) :
    (Mfamily u m).natDegree ≤ 2 * m - 1 := by
  have hb (j : ℕ) : (B u j).natDegree ≤ 2 * j - 1 := by
    change ((scaledEta u j).coeff 0 * (properEta u j).coeff 0).natDegree ≤ _
    exact (natDegree_mul_le_of_le (scaledEta_coeff_degree u j 0)
      (properEta_coeff_degree u j 0)).trans (by omega)
  rw [Mfamily]
  have hC : (-2 : K[X]) = C (-2 : K) := by simp only [_root_.map_neg, C_ofNat]
  rw [hC]
  apply (natDegree_C_mul_le (-2 : K) _).trans
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjm := Finset.mem_range.mp hj
  apply (natDegree_C_mul_le _ _).trans
  have h1 : (B u (j + 1)).natDegree ≤ 2 * m - 1 := (hb (j + 1)).trans (by omega)
  have h0 : (B u j).natDegree ≤ 2 * m - 1 := (hb j).trans (by omega)
  simpa only [max_self] using natDegree_add_le_of_le h1 h0

theorem family_map {L : Type*} [CommRing L] (f : K →+* L) (u : ℕ → K) (m : ℕ) :
    (scaledEta u m).map (Polynomial.mapRingHom f) = scaledEta (fun j => f (u j)) m ∧
    (properEta u m).map (Polynomial.mapRingHom f) = properEta (fun j => f (u j)) m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [scaledEta, properEta]
  | one => simp [scaledEta, properEta, ActualTC1Family.eta, tx]
  | more j ih0 ih1 =>
      obtain ⟨ha0, hn0⟩ := ih0
      obtain ⟨ha1, hn1⟩ := ih1
      constructor <;>
        simp only [scaledEta, properEta, etaStep, cc, tx, ActualTC1Family.eta, Polynomial.map_mul,
          Polynomial.map_sub, Polynomial.map_natCast, Polynomial.map_X,
          Polynomial.map_C, Polynomial.coe_mapRingHom, ha0, ha1, hn0, hn1]

end Family

variable (p : ℕ) [Fact p.Prime]

noncomputable def u (j : ℕ) : ZMod p := residueHom p (smallIntegralInverse p j)

theorem actual_units (m : ℕ) (hm : m < p) : UnitsTo (u p) m := by
  intro j hj hjm
  simpa only [u, _root_.map_mul, _root_.map_natCast, _root_.map_one] using
    congrArg (residueHom p) (integral_small_unit p j hj (by omega))

theorem actual_A (hp : 19 ≤ p) : A (u p) (p / 6) = actualLegendreJacobi p := by
  have h := congrArg (fun P : (ZMod p)[X][X] => P.coeff 0)
    (family_map (residueHom p) (fun j => smallIntegralInverse p j) (p / 6)).1
  simp only [coeff_map, Polynomial.coe_mapRingHom] at h
  change (scaledEta (fun j => residueHom p (smallIntegralInverse p j)) (p / 6)).coeff 0 = _
  rw [← h, actual_scaled_origin_field p hp]

theorem actual_N (hp : 19 ≤ p) : N (u p) (p / 6) = properLegendreJacobi p := by
  have h := congrArg (fun P : (ZMod p)[X][X] => P.coeff 0)
    (family_map (residueHom p) (fun j => smallIntegralInverse p j) (p / 6)).2
  simp only [coeff_map, Polynomial.coe_mapRingHom] at h
  change (properEta (fun j => residueHom p (smallIntegralInverse p j)) (p / 6)).coeff 0 = _
  rw [← h, ← properEtaIntegral_generic,
    ← ActualBalancedCarry.properEtaOrigin, actual_proper_origin_field p hp]

theorem actual_harmonic (m : ℕ) (hm : m < p) : harmonic (u p) m = fieldHarmonic p m := by
  unfold harmonic fieldHarmonic
  apply Finset.sum_congr rfl
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have hn := small_cast_ne_zero p (j + 1) (by omega) (by omega)
  have hunit := actual_units p m hm (j + 1) (by omega) (by omega)
  calc
    u p (j + 1) = (((j + 1 : ℕ) : ZMod p)⁻¹ *
        (((j + 1 : ℕ) : ZMod p) * u p (j + 1))) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = _ := by rw [hunit, mul_one]

private theorem small_derivative_unique (P Q : (ZMod p)[X])
    (hP : P.natDegree < p) (hQ : Q.natDegree < p)
    (hd : P.derivative = Q.derivative) (h0 : P.coeff 0 = Q.coeff 0) : P = Q := by
  ext n
  cases n with
  | zero => exact h0
  | succ n =>
      by_cases hn : n + 1 < p
      · have hu := small_cast_ne_zero p (n + 1) (by omega) hn
        have hc := congrArg (fun R : (ZMod p)[X] => R.coeff n) hd
        rw [coeff_derivative, coeff_derivative] at hc
        exact mul_right_cancel₀ (by simpa only [Nat.cast_add, Nat.cast_one] using hu) hc
      · rw [coeff_eq_zero_of_natDegree_lt (by omega),
          coeff_eq_zero_of_natDegree_lt (by omega)]

theorem actual_native_H_source (hp : 19 ≤ p) :
    X * (nativeHField p).derivative = nativeField p (p / 6) - 1 := by
  ext n
  cases n with
  | zero => simp [nativeField_coeff, WPReview.nativeCoefficient_zero]
  | succ n =>
      rw [coeff_X_mul, coeff_derivative, nativeHField_coeff, coeff_sub,
        nativeField_coeff]
      have hone : (1 : (ZMod p)[X]).coeff (n + 1) = 0 := by
        rw [coeff_one, if_neg (by omega : n + 1 ≠ 0)]
      rw [hone, sub_zero]
      by_cases hn : n + 1 ≤ p / 6
      · have hu := small_cast_ne_zero p (n + 1) (by omega) (by omega)
        simp only [Nat.lt_succ_iff, if_pos hn]
        simpa only [Nat.cast_add, Nat.cast_one] using div_mul_cancel₀
          (WPReview.nativeCoefficient (n + 1) : ZMod p) hu
      · simp only [Nat.lt_succ_iff, if_neg hn, zero_div, zero_mul]

theorem actual_Hpull (hp : 19 ≤ p) :
    Hpull (u p) (p / 6) = (nativeHField p).comp (1 - X ^ 2) := by
  have hd : p / 6 < p := by omega
  have hu := actual_units p (p / 6) hd
  have hs := Hpull_source (u p) (p / 6) hu
  rw [actual_A p hp] at hs
  have he := congrArg (fun P : (ZMod p)[X] => P.comp (1 - X ^ 2))
    (actual_native_H_source p hp)
  simp only [mul_comp, X_comp, sub_comp, one_comp,
    actual_native_Jacobi_square p hp] at he
  have hder : (1 - X ^ 2) * ((nativeHField p).comp (1 - X ^ 2)).derivative =
      -2 * X * (actualLegendreJacobi p ^ 2 - 1) := by
    have hqD : (1 - X ^ 2 : (ZMod p)[X]).derivative = -2 * X := by
      simp [derivative_pow_succ]
      ring
    rw [derivative_comp, hqD]
    linear_combination -2 * X * he
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
    simp at hc
  have heq := mul_left_cancel₀ hq (hs.trans hder.symm)
  have hHd : ((nativeHField p).comp (1 - X ^ 2)).natDegree ≤ 2 * (p / 6) :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (nativeHField_degree p)
      (show (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 by compute_degree)).trans (by omega))
  have hconst : (Hpull (u p) (p / 6) -
      (nativeHField p).comp (1 - X ^ 2)).derivative = 0 := by
    rw [derivative_sub, heq, sub_self]
  have hdiff := small_derivative_unique p
    (Hpull (u p) (p / 6) - (nativeHField p).comp (1 - X ^ 2))
    (C ((Hpull (u p) (p / 6) - (nativeHField p).comp (1 - X ^ 2)).coeff 0))
    ((natDegree_sub_le_of_le (Hpull_degree (u p) (p / 6)) hHd).trans_lt (by omega))
    (by simp; omega) (by simpa only [derivative_C] using hconst) (by simp)
  have h1 := congrArg (fun P : (ZMod p)[X] => P.eval 1) hdiff
  have hH0 : (nativeHField p).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, nativeHField_origin]
  simp only [eval_sub, Hpull_one (u p) (p / 6) hu, eval_comp, eval_sub,
    eval_one, eval_pow, eval_X, one_pow, sub_self, hH0, sub_self, eval_C] at h1
  rw [← h1, C_0] at hdiff
  exact sub_eq_zero.mp hdiff

/-- The finite mixed-product primitive is identified with the original native M. -/
theorem actual_M_source (hp : 19 ≤ p) :
    Mfamily (u p) (p / 6) = ActualFirstGreen.M p := by
  have hu := actual_units p (p / 6) (by omega)
  have hs := Mfamily_source (u p) (p / 6) hu
  rw [actual_Hpull p hp, B, actual_A p hp, actual_N p hp,
    actual_harmonic p (p / 6) (by omega)] at hs
  change (1 - X ^ 2) * (Mfamily (u p) (p / 6)).derivative = ActualFirstGreen.U p at hs
  obtain ⟨hJ, _, _, _, hMD, hM0, _, hMd⟩ := ActualFirstGreen.actual_low_primitive p hp
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
    simp at hc
  apply small_derivative_unique p
    (Mfamily (u p) (p / 6)) (ActualFirstGreen.M p)
    ((Mfamily_degree (u p) (p / 6)).trans_lt (by omega)) (hMd.trans_lt (by omega))
  · rw [hMD]
    exact mul_left_cancel₀ hq (hs.trans hJ.symm)
  · rw [Mfamily_zero, hM0]

theorem actual_M_endpoint (hp : 19 ≤ p) :
    (ActualFirstGreen.M p).eval 1 = 2 * fieldHarmonic p (p / 6) ^ 2 := by
  rw [← actual_M_source p hp, Mfamily_one (u p) (p / 6)
    (actual_units p (p / 6) (by omega)), actual_harmonic p (p / 6) (by omega)]

end WPFieldAssembly.NativeClosureGaussM
