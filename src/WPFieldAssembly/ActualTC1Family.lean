import WPFieldAssembly.ActualBalancedCarry
import WPFieldAssembly.ActualNextHermite
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Derivation.MapCoeffs

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction
  WPActualNativeParameter WPActualRankTwoParameter
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField
  WPActualRankTwoFirstLift WPActualRankTwoFixedDegree
  WPActualRankTwoLowTaylor WPActualRankTwoHatLift
  WPActualRankTwoFiniteLegendre WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualNextHermite WPActualRankTwoProper
  WPActualRankTwoComparison WPActualCMGauss WPFieldAssembly.NativeIR28
  WPActualGaussBottom

namespace WPFieldAssembly.ActualTC1Family
set_option maxHeartbeats 1600000

abbrev EtaPoly (K : Type*) [CommRing K] := K[X][X]

section Generic
variable {K : Type*} [CommRing K]

noncomputable def cc (a : K) : EtaPoly K := C (C a)
noncomputable def tx : EtaPoly K := C (X : K[X])
noncomputable def eta : EtaPoly K := X
noncomputable def tq : EtaPoly K := 1 - tx ^ 2
noncomputable def DT : Derivation K (EtaPoly K) (EtaPoly K) :=
  PolynomialModule.equivPolynomialSelf.compDer
    (Polynomial.derivative' (R := K)).mapCoeffs

@[simp] theorem DT_coeff (P : EtaPoly K) (j : ℕ) :
    (DT P).coeff j = (P.coeff j).derivative := rfl
@[simp] theorem DT_C (P : K[X]) : DT (C P) = C P.derivative := by
  apply Polynomial.ext
  intro j
  by_cases hj : j = 0 <;> simp [DT_coeff, coeff_C, hj]
@[simp] theorem DT_cc (a : K) : DT (cc a) = 0 := by
  simp [cc]
@[simp] theorem DT_tx : DT (tx : EtaPoly K) = 1 := by simp [tx]
@[simp] theorem DT_eta : DT (eta : EtaPoly K) = 0 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j = 1 <;> simp [DT_coeff, eta, coeff_X, eq_comm, hj]
@[simp] theorem DT_nat (n : ℕ) : DT (n : EtaPoly K) = 0 := by
  have hn : (n : EtaPoly K) = cc (n : K) := by simp [cc]
  rw [hn, DT_cc]
@[simp] theorem DT_mul (P Q : EtaPoly K) :
    DT (P * Q) = P * DT Q + Q * DT P := by
  simpa only [smul_eq_mul] using (DT (K := K)).leibniz P Q
@[simp] theorem DT_one : DT (1 : EtaPoly K) = 0 := by
  have h := DT_mul (1 : EtaPoly K) 1
  simp only [one_mul, mul_one] at h
  linear_combination -h
private theorem DT_two : DT (2 : EtaPoly K) = 0 := by
  simpa only [Nat.cast_ofNat] using (DT_nat (K := K) 2)
@[simp] theorem DT_tq : DT (tq : EtaPoly K) = -2 * tx := by
  simp [tq, pow_two]; ring

noncomputable def etaStep (u : ℕ → K) (j : ℕ)
    (U V : EtaPoly K) : EtaPoly K :=
  cc (u (j + 2)) *
    ((((2 * j + 3 : ℕ) : EtaPoly K) - eta) * tx * V -
      (((j + 1 : ℕ) : EtaPoly K) - eta) * U)
noncomputable def scaledEta (u : ℕ → K) : ℕ → EtaPoly K
  | 0 => 1
  | 1 => (1 - eta) * tx
  | j + 2 => etaStep u j (scaledEta u j) (scaledEta u (j + 1))
noncomputable def properEta (u : ℕ → K) : ℕ → EtaPoly K
  | 0 => 0
  | 1 => -1
  | j + 2 => etaStep u j (properEta u j) (properEta u (j + 1))
noncomputable def metricFactor (u : ℕ → K) : ℕ → EtaPoly K
  | 0 => 1
  | j + 1 => metricFactor u j * (1 - cc (u (j + 1)) * eta)
noncomputable def harmonic (u : ℕ → K) (m : ℕ) : K :=
  ∑ j ∈ Finset.range m, u (j + 1)
def UnitsTo (u : ℕ → K) (m : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ m → (j : K) * u j = 1

private theorem natCoeff_zero (n : ℕ) : (n : EtaPoly K).coeff 0 = (n : K[X]) := by
  have hn : (n : EtaPoly K) = C (n : K[X]) := by simp only [_root_.map_natCast]
  rw [hn, coeff_C_zero]
private theorem natCoeff_succ (n j : ℕ) : (n : EtaPoly K).coeff (j + 1) = 0 := by
  have hn : (n : EtaPoly K) = C (n : K[X]) := by simp only [_root_.map_natCast]
  rw [hn, coeff_C_succ]
private theorem twoCoeff_zero : (2 : EtaPoly K).coeff 0 = (2 : K[X]) := by
  change (C (2 : K[X])).coeff 0 = _
  rw [coeff_C_zero]
private theorem twoCoeff_one : (2 : EtaPoly K).coeff 1 = 0 := by
  change (C (2 : K[X])).coeff 1 = _
  rw [coeff_C_succ]

private theorem lift_unit (u : ℕ → K) {j m : ℕ}
    (h : UnitsTo u m) (hj : 0 < j) (hjm : j ≤ m) :
    (j : EtaPoly K) * cc (u j) = 1 := by
  have he := congrArg (fun a : K => cc a) (h j hj hjm)
  simpa only [cc, _root_.map_mul, _root_.map_natCast, _root_.map_one] using he

private theorem nat_cancel (u : ℕ → K) {j m : ℕ}
    (h : UnitsTo u m) (hj : 0 < j) (hjm : j ≤ m)
    {P Q : EtaPoly K} (he : (j : EtaPoly K) * P = (j : EtaPoly K) * Q) : P = Q := by
  have hu := lift_unit u h hj hjm
  linear_combination cc (u j) * he - (P - Q) * hu

private theorem scaledEta_cleared (u : ℕ → K) {j m : ℕ}
    (h : UnitsTo u m) (hj : j + 2 ≤ m) :
    (j + 2 : EtaPoly K) * scaledEta u (j + 2) =
      (((2 * j + 3 : ℕ) : EtaPoly K) - eta) * tx * scaledEta u (j + 1) -
        (((j + 1 : ℕ) : EtaPoly K) - eta) * scaledEta u j := by
  have hu := lift_unit u h (by omega : 0 < j + 2) hj
  simp only [Nat.cast_add, Nat.cast_ofNat] at hu
  rw [scaledEta, etaStep, ← mul_assoc, hu, one_mul]
private theorem properEta_cleared (u : ℕ → K) {j m : ℕ}
    (h : UnitsTo u m) (hj : j + 2 ≤ m) :
    (j + 2 : EtaPoly K) * properEta u (j + 2) =
      (((2 * j + 3 : ℕ) : EtaPoly K) - eta) * tx * properEta u (j + 1) -
        (((j + 1 : ℕ) : EtaPoly K) - eta) * properEta u j := by
  have hu := lift_unit u h (by omega : 0 < j + 2) hj
  simp only [Nat.cast_add, Nat.cast_ofNat] at hu
  rw [properEta, etaStep, ← mul_assoc, hu, one_mul]

theorem metricFactor_product (u : ℕ → K) (m : ℕ) :
    metricFactor u m =
      ∏ j ∈ Finset.range m, (1 - cc (u (j + 1)) * eta) := by
  induction m with
  | zero => simp [metricFactor]
  | succ m ih => simp [metricFactor, Finset.prod_range_succ, ih]

private theorem eta_ladders (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) : ∀ j, j + 1 ≤ m →
    tq * DT (scaledEta u j) =
      (((j + 1 : ℕ) : EtaPoly K) - eta) * tx * scaledEta u j -
        (j + 1 : EtaPoly K) * scaledEta u (j + 1) ∧
    tq * DT (scaledEta u (j + 1)) =
      (((j + 1 : ℕ) : EtaPoly K) - eta) * scaledEta u j -
        (j + 1 : EtaPoly K) * tx * scaledEta u (j + 1) ∧
    tq * DT (properEta u j) =
      (j + 1 : EtaPoly K) * (tx * properEta u j - properEta u (j + 1)) -
        scaledEta u j ∧
    tq * DT (properEta u (j + 1)) =
      (((j + 1 : ℕ) : EtaPoly K) - eta) *
        (properEta u j - tx * properEta u (j + 1)) - scaledEta u (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro hj
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
      have hRa := scaledEta_cleared u hu (by omega : j + 2 ≤ m)
      have hRn := properEta_cleared u hu (by omega : j + 2 ≤ m)
      have hDa := congrArg (fun P : EtaPoly K => DT P) hRa
      have hDn := congrArg (fun P : EtaPoly K => DT P) hRn
      simp only [DT_mul, DT_nat, DT_tx, DT_eta, DT_two, _root_.map_sub, _root_.map_add,
        zero_add] at hDa hDn
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        at hLa hUa hLn hUn hRa hRn hDa hDn ⊢
      dsimp only [tq] at hLa hUa hLn hUn ⊢
      constructor
      · linear_combination hUa + hRa
      constructor
      · apply nat_cancel u hu (by omega : 0 < j + 2) (by omega : j + 2 ≤ m)
        simp only [Nat.cast_add, Nat.cast_ofNat]
        linear_combination
          (1 - tx ^ 2) * hDa +
          ((2 * (j : EtaPoly K) + 3) - eta) * tx * hUa -
          (((j : EtaPoly K) + 1) - eta) * hLa +
          ((j : EtaPoly K) + 2) * tx * hRa
      constructor
      · linear_combination hUn + hRn
      · apply nat_cancel u hu (by omega : 0 < j + 2) (by omega : j + 2 ≤ m)
        simp only [Nat.cast_add, Nat.cast_ofNat]
        linear_combination
          (1 - tx ^ 2) * hDn +
          ((2 * (j : EtaPoly K) + 3) - eta) * tx * hUn -
          (((j : EtaPoly K) + 1) - eta) * hLn +
          (((j : EtaPoly K) + 2) - eta) * tx * hRn + hRa

private theorem metricFactor_cleared (u : ℕ → K) {j m : ℕ}
    (hu : UnitsTo u m) (hj : j + 1 ≤ m) :
    (j + 1 : EtaPoly K) * metricFactor u (j + 1) =
      (((j + 1 : ℕ) : EtaPoly K) - eta) * metricFactor u j := by
  have hunit := lift_unit u hu (by omega : 0 < j + 1) hj
  rw [metricFactor]
  simp only [Nat.cast_add, Nat.cast_one] at hunit ⊢
  linear_combination -(metricFactor u j * eta) * hunit

private theorem eta_casoratian (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) : ∀ j, j + 1 ≤ m →
    (((j + 1 : ℕ) : EtaPoly K) - eta) *
      (scaledEta u (j + 1) * properEta u j -
        scaledEta u j * properEta u (j + 1)) = metricFactor u (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro hj
      have hunit : cc (u 1) = (1 : EtaPoly K) := by
        simpa using lift_unit u hu (by omega : 0 < 1) (by omega : 1 ≤ m)
      simp [scaledEta, properEta, metricFactor, hunit]
  | succ j ih =>
      intro hj
      have hc := ih (by omega)
      have hRa := scaledEta_cleared u hu (by omega : j + 2 ≤ m)
      have hRn := properEta_cleared u hu (by omega : j + 2 ≤ m)
      have hG := metricFactor_cleared u hu (by omega : j + 2 ≤ m)
      apply nat_cancel u hu (by omega : 0 < j + 2) (by omega : j + 2 ≤ m)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        at hc hRa hRn hG ⊢
      linear_combination
        (((j : EtaPoly K) + 2) - eta) *
          (properEta u (j + 1) * hRa - scaledEta u (j + 1) * hRn + hc) - hG

theorem eta_metric (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    tq * (scaledEta u m * DT (properEta u m) -
      DT (scaledEta u m) * properEta u m) -
      eta * tx * scaledEta u m * properEta u m =
        metricFactor u m - scaledEta u m ^ 2 := by
  cases m with
  | zero => simp [scaledEta, properEta, metricFactor]
  | succ j =>
      obtain ⟨_, hUa, _, hUn⟩ := eta_ladders u (j + 1) hu j (by omega)
      have hc := eta_casoratian u (j + 1) hu j (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hUa hUn hc ⊢
      linear_combination scaledEta u (j + 1) * hUn -
        properEta u (j + 1) * hUa + hc

noncomputable def endLift : EtaPoly K →+* EtaPoly K :=
  (Polynomial.mapRingHom (Polynomial.C : K →+* K[X])).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom (1 : K)))
@[simp] theorem endLift_coeff (P : EtaPoly K) (j : ℕ) :
    (endLift P).coeff j = C ((P.coeff j).eval 1) := by
  simp [endLift]
@[simp] theorem endLift_cc (a : K) : endLift (cc a) = cc a := by
  simp [endLift, cc]
@[simp] theorem endLift_tx : endLift (tx : EtaPoly K) = 1 := by
  simp [endLift, tx]
@[simp] theorem endLift_eta : endLift (eta : EtaPoly K) = eta := by
  simp [endLift, eta]
@[simp] theorem endLift_metricFactor (u : ℕ → K) (m : ℕ) :
    endLift (metricFactor u m) = metricFactor u m := by
  induction m with
  | zero => simp [metricFactor]
  | succ m ih => simp [metricFactor, ih]

private theorem metricFactor_three_term (u : ℕ → K) {j m : ℕ}
    (hu : UnitsTo u m) (hj : j + 2 ≤ m) :
    (j + 2 : EtaPoly K) * metricFactor u (j + 2) =
      (((2 * j + 3 : ℕ) : EtaPoly K) - eta) * metricFactor u (j + 1) -
      (((j + 1 : ℕ) : EtaPoly K) - eta) * metricFactor u j := by
  have h0 := metricFactor_cleared u hu (by omega : j + 1 ≤ m)
  have h1 := metricFactor_cleared u hu (by omega : j + 2 ≤ m)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h0 h1 ⊢
  linear_combination h1 - h0

theorem scaledEta_endpoint (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    endLift (scaledEta u m) = metricFactor u m := by
  have h : ∀ j, j ≤ m → endLift (scaledEta u j) = metricFactor u j := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => intro _; simp [scaledEta, metricFactor]
    | one =>
        intro hj
        have hunit : cc (u 1) = (1 : EtaPoly K) := by
          simpa using lift_unit u hu (by omega : 0 < 1) hj
        simp [scaledEta, metricFactor, hunit]
    | more j ih0 ih1 =>
        intro hj
        have he := congrArg endLift (scaledEta_cleared u hu hj)
        simp only [_root_.map_mul, _root_.map_sub, _root_.map_add,
          _root_.map_natCast, _root_.map_ofNat, endLift_tx,
          endLift_eta, ih0 (by omega), ih1 (by omega), mul_one] at he
        apply nat_cancel u hu (by omega : 0 < j + 2) hj
        have hg := metricFactor_three_term u hu hj
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at he hg ⊢
        linear_combination he - hg
  exact h m le_rfl

theorem properEta_endpoint (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    eta * endLift (properEta u m) = metricFactor u m - 1 := by
  have h : ∀ j, j ≤ m → eta * endLift (properEta u j) = metricFactor u j - 1 := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => intro _; simp [properEta, metricFactor]
    | one =>
        intro hj
        have hunit : cc (u 1) = (1 : EtaPoly K) := by
          simpa using lift_unit u hu (by omega : 0 < 1) hj
        simp [properEta, metricFactor, hunit]
        ring
    | more j ih0 ih1 =>
        intro hj
        have he := congrArg endLift (properEta_cleared u hu hj)
        simp only [_root_.map_mul, _root_.map_sub, _root_.map_add,
          _root_.map_natCast, _root_.map_ofNat, endLift_tx, endLift_eta,
          mul_one] at he
        have h0 := ih0 (by omega)
        have h1 := ih1 (by omega)
        have hg := metricFactor_three_term u hu hj
        apply nat_cancel u hu (by omega : 0 < j + 2) hj
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at he hg ⊢
        linear_combination eta * he +
          ((2 * (j : EtaPoly K) + 3) - eta) * h1 -
          (((j : EtaPoly K) + 1) - eta) * h0 - hg
  exact h m le_rfl

theorem metricFactor_coeff_zero (u : ℕ → K) (m : ℕ) :
    (metricFactor u m).coeff 0 = 1 := by
  induction m with
  | zero => simp [metricFactor]
  | succ m ih => simp [metricFactor, mul_coeff_zero, ih, eta]

theorem metricFactor_coeff_one (u : ℕ → K) (m : ℕ) :
    (metricFactor u m).coeff 1 = -C (harmonic u m) := by
  induction m with
  | zero => simp [metricFactor, harmonic, coeff_one]
  | succ m ih =>
      simp only [metricFactor, mul_coeff_one, metricFactor_coeff_zero, ih,
        harmonic, Finset.sum_range_succ, _root_.map_add, eta, cc]
      simp [coeff_one]

theorem scaledEta_origin_endpoint (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    ((scaledEta u m).coeff 0).eval 1 = 1 := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 0) (scaledEta_endpoint u m hu)
  rw [endLift_coeff, metricFactor_coeff_zero] at he
  exact Polynomial.C_injective he

theorem properEta_origin_endpoint (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    ((properEta u m).coeff 0).eval 1 = -harmonic u m := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 1) (properEta_endpoint u m hu)
  simp only [eta, coeff_X_mul, coeff_sub,
    endLift_coeff, metricFactor_coeff_one, coeff_one] at he
  exact Polynomial.C_injective (by simpa using he)

theorem swap_coeff (P : EtaPoly K) (i j : ℕ) :
    ((Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [_root_.map_add, coeff_add, ihP, ihQ]
  | monomial n P =>
      induction P using Polynomial.induction_on' with
      | add P Q ihP ihQ => simp only [_root_.map_add, coeff_add, ihP, ihQ]
      | monomial m a =>
          rw [Bivariate.swap_monomial_monomial]
          by_cases hm : m = i <;> by_cases hn : n = j <;>
            simp [coeff_monomial, hm, hn]

private theorem etaStep_T_degree (u : ℕ → K) (j a : ℕ)
    (U V : EtaPoly K) (hU : (Bivariate.swap U).natDegree ≤ a)
    (hV : (Bivariate.swap V).natDegree ≤ a) :
    (Bivariate.swap (etaStep u j U V)).natDegree ≤ a + 1 := by
  have he : Bivariate.swap (etaStep u j U V) =
      C (C (u (j + 2))) *
        (C (((2 * j + 3 : ℕ) : K[X]) - X) * X * Bivariate.swap V -
         C (((j + 1 : ℕ) : K[X]) - X) * Bivariate.swap U) := by
    simp only [etaStep, cc, tx, eta, _root_.map_mul, _root_.map_sub, _root_.map_natCast,
      Bivariate.swap_C_C, Bivariate.swap_X, Bivariate.swap_Y]
  rw [he]
  apply (natDegree_C_mul_le _ _).trans
  have hleft : (C (((2 * j + 3 : ℕ) : K[X]) - X) * X * Bivariate.swap V).natDegree ≤ a + 1 := by
    exact (natDegree_mul_le_of_le
      ((natDegree_C_mul_le _ _).trans natDegree_X_le) hV).trans (by omega)
  have hright : (C (((j + 1 : ℕ) : K[X]) - X) * Bivariate.swap U).natDegree ≤ a + 1 :=
    ((natDegree_C_mul_le _ _).trans hU).trans (by omega)
  exact (natDegree_sub_le_of_le hleft hright).trans (by simp)

theorem scaledEta_T_degree (u : ℕ → K) (m : ℕ) :
    (Bivariate.swap (scaledEta u m)).natDegree ≤ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [scaledEta]
  | one =>
      have he : Bivariate.swap (scaledEta u 1) =
          C (1 - (X : K[X])) * (X : EtaPoly K) := by
        simp only [scaledEta, eta, tx, _root_.map_mul, _root_.map_sub, _root_.map_one,
          Bivariate.swap_X, Bivariate.swap_Y]
      rw [he]
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  | more j ih0 ih1 =>
      rw [scaledEta]
      exact etaStep_T_degree u j (j + 1) _ _ (ih0.trans (by omega)) ih1

theorem properEta_T_degree (u : ℕ → K) (m : ℕ) :
    (Bivariate.swap (properEta u m)).natDegree ≤ m - 1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [properEta]
  | one => simp [properEta]
  | more j ih0 ih1 =>
      rw [properEta]
      exact (etaStep_T_degree u j j _ _ (ih0.trans (by omega))
        (ih1.trans (by omega))).trans (by omega)

theorem scaledEta_coeff_degree (u : ℕ → K) (m k : ℕ) :
    ((scaledEta u m).coeff k).natDegree ≤ m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [← swap_coeff]
  rw [coeff_eq_zero_of_natDegree_lt ((scaledEta_T_degree u m).trans_lt hi)]
  simp

theorem properEta_coeff_degree (u : ℕ → K) (m k : ℕ) :
    ((properEta u m).coeff k).natDegree ≤ m - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [← swap_coeff]
  rw [coeff_eq_zero_of_natDegree_lt ((properEta_T_degree u m).trans_lt hi)]
  simp

noncomputable def etaAOperator (m : ℕ) (P : EtaPoly K) : EtaPoly K :=
  tq * DT (DT P) - (2 - eta) * tx * DT P +
    (m : EtaPoly K) * ((m : EtaPoly K) + 1 - eta) * P
noncomputable def etaNOperator (m : ℕ) (P : EtaPoly K) : EtaPoly K :=
  tq * DT (DT P) - (2 + eta) * tx * DT P +
    ((m : EtaPoly K) + 1) * ((m : EtaPoly K) - eta) * P

private theorem tq_ne_zero [IsDomain K] : (tq : EtaPoly K) ≠ 0 := by
  intro hz
  have he := congrArg (fun P : EtaPoly K => (P.coeff 0).coeff 2) hz
  norm_num [tq, tx, pow_two, coeff_one] at he

theorem scaledEta_equation [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) : etaAOperator m (scaledEta u m) = 0 := by
  cases m with
  | zero => simp [etaAOperator, scaledEta]
  | succ j =>
      obtain ⟨hLa, hUa, _, _⟩ := eta_ladders u (j + 1) hu j (by omega)
      have hd := congrArg (fun P : EtaPoly K => DT P) hUa
      simp only [DT_mul, DT_tq, DT_nat, DT_eta, DT_tx, DT_one, _root_.map_sub,
        _root_.map_add, mul_zero, add_zero] at hd
      have hz : tq * etaAOperator (j + 1) (scaledEta u (j + 1)) = 0 := by
        dsimp only [etaAOperator, tq] at *
        simp only [Nat.cast_add, Nat.cast_one] at hLa hUa hd ⊢
        linear_combination (1 - tx ^ 2) * hd +
          (((j : EtaPoly K) + 1) - eta) * hLa -
          (((j : EtaPoly K) + 1) - eta) * tx * hUa
      exact (mul_eq_zero.mp hz).resolve_left tq_ne_zero

theorem properEta_equation [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) : etaNOperator m (properEta u m) = -2 * DT (scaledEta u m) := by
  cases m with
  | zero => simp [etaNOperator, properEta, scaledEta]
  | succ j =>
      obtain ⟨_, hUa, hLn, hUn⟩ := eta_ladders u (j + 1) hu j (by omega)
      have hd := congrArg (fun P : EtaPoly K => DT P) hUn
      simp only [DT_mul, DT_tq, DT_nat, DT_eta, DT_tx, _root_.map_sub] at hd
      have hz : tq * (etaNOperator (j + 1) (properEta u (j + 1)) +
          2 * DT (scaledEta u (j + 1))) = 0 := by
        dsimp only [etaNOperator, tq] at *
        simp only [Nat.cast_add, Nat.cast_one] at hUa hLn hUn hd ⊢
        linear_combination (1 - tx ^ 2) * hd +
          (((j : EtaPoly K) + 1) - eta) * hLn -
          ((j : EtaPoly K) + 1) * tx * hUn + hUa
      have he := (mul_eq_zero.mp hz).resolve_left tq_ne_zero
      linear_combination he

theorem scaledEta_origin_source [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) :
    legendreJacobi m ((scaledEta u m).coeff 0) = 0 := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 0) (scaledEta_equation u m hu)
  simp only [etaAOperator, tq, tx, eta, pow_two, mul_coeff_zero, coeff_sub,
    coeff_add, coeff_one, coeff_X_zero, coeff_C_zero, natCoeff_zero,
    twoCoeff_zero, DT_coeff, ite_true, sub_zero, coeff_zero] at he
  dsimp only [legendreJacobi]
  simp only [_root_.map_mul, _root_.map_add, _root_.map_natCast, _root_.map_one]
  linear_combination he

theorem scaledEta_jet_source [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) :
    legendreJacobi m ((scaledEta u m).coeff 1) =
      -(X * ((scaledEta u m).coeff 0).derivative -
        C (m : K) * (scaledEta u m).coeff 0) := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 1) (scaledEta_equation u m hu)
  simp only [etaAOperator, tq, tx, eta, mul_coeff_zero, mul_coeff_one,
    coeff_sub, coeff_add, coeff_one, coeff_X_zero, coeff_X_one,
    coeff_C_zero, coeff_C_succ, natCoeff_zero, natCoeff_succ,
    twoCoeff_zero, twoCoeff_one, pow_two, DT_coeff, ite_true,
    Nat.one_ne_zero, ite_false, zero_mul, mul_zero, sub_zero, add_zero, coeff_zero] at he
  dsimp only [legendreJacobi]
  simp only [_root_.map_mul, _root_.map_add, _root_.map_natCast, _root_.map_one]
  linear_combination he

theorem properEta_origin_source [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) :
    legendreJacobi m ((properEta u m).coeff 0) =
      -2 * ((scaledEta u m).coeff 0).derivative := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 0) (properEta_equation u m hu)
  simp only [etaNOperator, tq, tx, eta, pow_two, mul_coeff_zero, coeff_sub,
    coeff_add, coeff_one, coeff_X_zero, coeff_C_zero, natCoeff_zero,
    twoCoeff_zero, coeff_neg, DT_coeff, ite_true,
    sub_zero, add_zero] at he
  dsimp only [legendreJacobi]
  simp only [_root_.map_mul, _root_.map_add, _root_.map_natCast, _root_.map_one]
  linear_combination he

theorem eta_metric_first_source (u : ℕ → K) (m : ℕ) (hu : UnitsTo u m) :
    (1 - X ^ 2) *
      ((scaledEta u m).coeff 0 * ((properEta u m).coeff 1).derivative +
       (scaledEta u m).coeff 1 * ((properEta u m).coeff 0).derivative -
       ((scaledEta u m).coeff 0).derivative * (properEta u m).coeff 1 -
       ((scaledEta u m).coeff 1).derivative * (properEta u m).coeff 0) -
      X * (scaledEta u m).coeff 0 * (properEta u m).coeff 0 =
      -C (harmonic u m) - 2 * (scaledEta u m).coeff 0 * (scaledEta u m).coeff 1 := by
  have he := congrArg (fun P : EtaPoly K => P.coeff 1) (eta_metric u m hu)
  simp only [tq, tx, eta, pow_two, mul_coeff_zero, mul_coeff_one,
    coeff_sub, coeff_one, coeff_X_zero, coeff_X_one,
    coeff_C_zero, coeff_C_succ, DT_coeff, metricFactor_coeff_one,
    ite_true, Nat.one_ne_zero, ite_false,
    zero_mul, mul_zero, one_mul, sub_zero, add_zero] at he
  linear_combination he

end Generic

private theorem rational_regular_kernel_zero (d : ℕ) (P : ℚ[X])
    (h0 : P.eval 0 = 0) (hs : legendreRegular d P = 0) : P = 0 := by
  have he : legendreEuler d P = 0 := by rw [legendreEuler_eq_X_regular, hs, mul_zero]
  have hc : ∀ n, P.coeff n = 0 := by
    intro n
    induction n with
    | zero => simpa only [coeff_zero_eq_eval_zero] using h0
    | succ n ih =>
        have h := congrArg (fun Q : ℚ[X] => Q.coeff (n + 1)) he
        rw [legendreEuler_coeff_succ, coeff_zero, ih, mul_zero, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (by positivity))
  ext n; simpa only [coeff_zero] using hc n

private theorem rational_jacobi_kernel_zero (d : ℕ) (P : ℚ[X])
    (h1 : P.eval 1 = 0) (hs : legendreJacobi d P = 0) : P = 0 := by
  let q : ℚ[X] := C (1 / 2) * (1 - X)
  let g : ℚ[X] := 1 - 2 * X
  have hi := jacobi_coordinate_inverse (1 / 2 : ℚ) (by norm_num)
  have hqg : q.comp g = X := hi.1
  have hgq : g.comp q = X := hi.2
  have he := legendre_coordinate d (1 / 2 : ℚ) (by norm_num) (P.comp g)
  change (legendreRegular d (P.comp g)).comp q =
    legendreJacobi d ((P.comp g).comp q) at he
  rw [comp_assoc, hgq, comp_X, hs] at he
  have hr := congrArg (fun Q : ℚ[X] => Q.comp g) he
  rw [comp_assoc, hqg, comp_X, zero_comp] at hr
  have hz := rational_regular_kernel_zero d (P.comp g)
    (by simp [eval_comp, g, h1]) hr
  have hh := congrArg (fun Q : ℚ[X] => Q.comp q) hz
  simpa only [comp_assoc, hgq, comp_X, zero_comp] using hh

variable (p : ℕ) [Fact p.Prime]

theorem integral_small_unit (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (j : integralRationals p) * smallIntegralInverse p j = 1 := by
  apply Subtype.ext
  change (j : ℚ) * (smallIntegralInverse p j).val = 1
  rw [smallIntegralInverse_value p j hj hjp]
  exact mul_one_div_cancel (by exact_mod_cast (Nat.ne_of_gt hj))

theorem integral_units (m : ℕ) (hm : m < p) :
    UnitsTo (fun j => smallIntegralInverse p j) m := by
  intro j hj hjm
  exact integral_small_unit p j hj (by omega)

theorem properEtaIntegral_generic (m : ℕ) :
    ActualBalancedCarry.properEtaIntegral p m = properEta (fun j => smallIntegralInverse p j) m := by
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more j ih0 ih1 =>
      rw [ActualBalancedCarry.properEtaIntegral, properEta, etaStep, ← ih0, ← ih1]
      simp only [cc, tx, eta, _root_.map_natCast]

theorem actual_scaled_origin_value (m : ℕ) (_hp : 7 ≤ p) (hm : m < p) :
    ((scaledEta (fun j => smallIntegralInverse p j) m).coeff 0).map
      (integralRationals p).subtype = rationalLegendre m := by
  let P := ((scaledEta (fun j => smallIntegralInverse p j) m).coeff 0).map
    (integralRationals p).subtype
  have hs : legendreJacobi m P = 0 := by
    have h := congrArg (fun Q : (integralRationals p)[X] =>
      Q.map (integralRationals p).subtype)
      (scaledEta_origin_source (fun j => smallIntegralInverse p j) m (integral_units p m hm))
    simpa only [legendreJacobi_map, Polynomial.map_zero] using h
  have h1 : P.eval 1 = 1 := by
    have h := congrArg (integralRationals p).subtype
      (scaledEta_origin_endpoint (fun j => smallIntegralInverse p j) m (integral_units p m hm))
    simpa only [← eval_map_apply, _root_.map_one] using h
  have hz := rational_jacobi_kernel_zero m (P - rationalLegendre m)
    (by rw [eval_sub, h1, rationalLegendre_endpoint_one]; ring)
    (by rw [legendreJacobi_sub, hs, rationalLegendre_ODE, sub_self])
  exact sub_eq_zero.mp hz

theorem actual_scaled_origin_integral (m : ℕ) (hp : 7 ≤ p) (hm : m < p) :
    (scaledEta (fun j => smallIntegralInverse p j) m).coeff 0 = integralLegendre p m hp := by
  apply polynomial_subtype_injective p
  change ((scaledEta (fun j => smallIntegralInverse p j) m).coeff 0).map
    (integralRationals p).subtype = (integralLegendre p m hp).map
      (integralRationals p).subtype
  rw [actual_scaled_origin_value p m hp hm, integralLegendre_value]

theorem actual_proper_origin_value (hp : 19 ≤ p) :
    (ActualBalancedCarry.properEtaOrigin p).map (integralRationals p).subtype =
      rationalProperJacobi (p / 6) := by
  have hd : p / 6 < p := by omega
  have he : ActualBalancedCarry.properEtaOrigin p =
      (properEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 0 := by
    rw [ActualBalancedCarry.properEtaOrigin, properEtaIntegral_generic]
  let P := (ActualBalancedCarry.properEtaOrigin p).map (integralRationals p).subtype
  have hs : legendreJacobi (p / 6) P = -2 * (rationalLegendre (p / 6)).derivative := by
    have h := congrArg (fun Q : (integralRationals p)[X] =>
      Q.map (integralRationals p).subtype)
      (properEta_origin_source (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ hd))
    simp only [legendreJacobi_map, Polynomial.map_mul, Polynomial.map_neg,
      Polynomial.map_ofNat, ←Polynomial.derivative_map,
      actual_scaled_origin_value p (p / 6) (by omega) hd] at h
    simpa only [P, he] using h
  have h1 : P.eval 1 = -rationalHarmonic (p / 6) := by
    have h := congrArg (integralRationals p).subtype
      (properEta_origin_endpoint (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ hd))
    have hh : harmonic (fun j => smallIntegralInverse p j) (p / 6) = integralHarmonic p (p / 6) := rfl
    rw [hh, _root_.map_neg, integralHarmonic_value p (p / 6) hd] at h
    simpa only [← eval_map_apply, _root_.map_one, P, he] using h
  have hz := rational_jacobi_kernel_zero (p / 6) (P - rationalProperJacobi (p / 6))
    (by rw [eval_sub, h1, rationalProperJacobi_endpoint_one]; ring)
    (by rw [legendreJacobi_sub, hs, rationalProperJacobi_source, sub_self])
  exact sub_eq_zero.mp hz

theorem actual_proper_origin_integral (hp : 19 ≤ p) :
    ActualBalancedCarry.properEtaOrigin p = integralProperJacobi p (by omega) := by
  apply polynomial_subtype_injective p
  change (ActualBalancedCarry.properEtaOrigin p).map (integralRationals p).subtype =
    (integralProperJacobi p (by omega)).map (integralRationals p).subtype
  rw [actual_proper_origin_value p hp, integralProperJacobi_value]

theorem properEtaJet_degree (_hp : 19 ≤ p) :
    (ActualBalancedCarry.properEtaJet p).natDegree ≤ p / 6 - 1 := by
  rw [ActualBalancedCarry.properEtaJet, properEtaIntegral_generic]
  exact properEta_coeff_degree _ _ _

noncomputable def actualScaledJet : (ZMod p)[X] :=
  ((scaledEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 1).map (residueHom p)
noncomputable def actualN1 : (ZMod p)[X] :=
  (ActualBalancedCarry.properEtaJet p).map (residueHom p)

theorem actual_scaled_origin_field (hp : 19 ≤ p) :
    ((scaledEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 0).map (residueHom p) =
      actualLegendreJacobi p := by
  rw [actual_scaled_origin_integral p (p / 6) (by omega) (by omega), integralLegendre_field]

theorem actual_proper_origin_field (hp : 19 ≤ p) :
    (ActualBalancedCarry.properEtaOrigin p).map (residueHom p) = properLegendreJacobi p := by
  rw [actual_proper_origin_integral p hp, integralProperJacobi_field]

theorem actualScaledJet_degree : (actualScaledJet p).natDegree ≤ p / 6 := by
  change (((scaledEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 1).map
    (residueHom p)).natDegree ≤ p / 6
  exact natDegree_map_le.trans
    (scaledEta_coeff_degree (fun j => smallIntegralInverse p j) (p / 6) 1)
theorem actualN1_degree (hp : 19 ≤ p) : (actualN1 p).natDegree ≤ p / 6 - 1 :=
  natDegree_map_le.trans (properEtaJet_degree p hp)

theorem actualScaledJet_endpoint (hp : 19 ≤ p) :
    (actualScaledJet p).eval 1 = -fieldHarmonic p (p / 6) := by
  have he := congrArg (fun P : EtaPoly (integralRationals p) => P.coeff 1)
    (scaledEta_endpoint (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ (by omega)))
  rw [endLift_coeff, metricFactor_coeff_one] at he
  rw [←C_neg] at he
  have hs := Polynomial.C_injective he
  have hh : harmonic (fun j => smallIntegralInverse p j) (p / 6) = integralHarmonic p (p / 6) := rfl
  have hr := congrArg (residueHom p) hs
  rw [hh, _root_.map_neg, integralHarmonic_field p (p / 6) (by omega)] at hr
  simpa only [actualScaledJet, ←eval_map_apply, _root_.map_one] using hr

theorem actualScaledJet_source (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (actualScaledJet p) =
      -(X * (actualLegendreJacobi p).derivative -
        C ((p / 6 : ℕ) : ZMod p) * actualLegendreJacobi p) := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (scaledEta_jet_source (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ (by omega)))
  simpa only [legendreJacobi_map, Polynomial.map_neg, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, _root_.map_natCast,
    Polynomial.map_natCast, ←Polynomial.derivative_map,
    actual_scaled_origin_field p hp, actualScaledJet] using h

theorem actual_scaled_jet_variation (hp : 19 ≤ p) :
    actualScaledJet p =
      -C (1 / 2 : ZMod p) * actualVariationField p (by omega) -
        C (fieldHarmonic p (p / 6)) * actualLegendreJacobi p := by
  let Y := actualLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let h := fieldHarmonic p (p / 6)
  let P := 2 * (actualScaledJet p + C h * Y) + A
  have hPdeg : P.natDegree < p := by
    have hY : (C h * Y).natDegree ≤ p / 6 :=
      (natDegree_C_mul_le _ _).trans (actualLegendreJacobi_degree p)
    have hsum : (actualScaledJet p + C h * Y).natDegree ≤ p / 6 :=
      (natDegree_add_le_of_le (actualScaledJet_degree p) hY).trans (by simp)
    have htwo : (2 * (actualScaledJet p + C h * Y)).natDegree ≤ p / 6 := by
      change (C (2 : ZMod p) * (actualScaledJet p + C h * Y)).natDegree ≤ p / 6
      exact (natDegree_C_mul_le _ _).trans hsum
    have hb : P.natDegree ≤ p / 6 :=
      (natDegree_add_le_of_le htwo (actualVariationField_degree p (by omega))).trans (by simp)
    exact hb.trans_lt (by omega)
  have hP1 : P.eval 1 = 0 := by
    simp only [P, eval_add, eval_mul, eval_ofNat, eval_C, actualScaledJet_endpoint p hp,
      Y, actualLegendreJacobi_endpoint_one, A, actualVariationField_endpoint_one, mul_one]
    dsimp only [h]; ring
  have hPs : legendreJacobi (p / 6) P = 0 := by
    change legendreJacobi (p / 6)
      (C (2 : ZMod p) * (actualScaledJet p + C h * Y) + A) = 0
    dsimp only [A, Y]
    simp only [legendreJacobi_add, legendreJacobi_C_mul,
      actualScaledJet_source p hp, actualLegendreJacobi_source_zero p (by omega),
      mul_zero, add_zero]
    simp only [_root_.map_ofNat]
    linear_combination actualVariationField_ODE p (by omega : 7 ≤ p)
  have hz := legendre_jacobi_kernel_zero p (p / 6) (by omega : 7 ≤ p) P hPdeg hP1 hPs
  have hu : (2 : (ZMod p)[X]) * C (1 / 2 : ZMod p) = 1 := by
    have h2 : (2 : ZMod p) ≠ 0 := by
      simpa only [Nat.cast_ofNat] using
        (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
    change C (2 : ZMod p) * C (1 / 2 : ZMod p) = 1
    rw [← C_mul, mul_one_div_cancel h2, C_1]
  dsimp only [P, A, Y, h] at hz
  linear_combination C (1 / 2 : ZMod p) * hz -
    (actualScaledJet p + C (fieldHarmonic p (p / 6)) * actualLegendreJacobi p) * hu

theorem actual_metric_first_source (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      (actualLegendreJacobi p * (actualN1 p).derivative +
       actualScaledJet p * (properLegendreJacobi p).derivative -
       (actualLegendreJacobi p).derivative * actualN1 p -
       (actualScaledJet p).derivative * properLegendreJacobi p) -
      X * actualLegendreJacobi p * properLegendreJacobi p =
      -C (fieldHarmonic p (p / 6)) -
        2 * actualLegendreJacobi p * actualScaledJet p := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (eta_metric_first_source (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ (by omega)))
  have hn : (properEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 0 =
      ActualBalancedCarry.properEtaOrigin p := by
    rw [ActualBalancedCarry.properEtaOrigin, properEtaIntegral_generic]
  have hn1 : (properEta (fun j => smallIntegralInverse p j) (p / 6)).coeff 1 =
      ActualBalancedCarry.properEtaJet p := by
    rw [ActualBalancedCarry.properEtaJet, properEtaIntegral_generic]
  have hh : harmonic (fun j => smallIntegralInverse p j) (p / 6) = integralHarmonic p (p / 6) := rfl
  simpa only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_neg,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_ofNat, ←Polynomial.derivative_map,
    actual_scaled_origin_field p hp, hn, hn1, actual_proper_origin_field p hp,
    hh, integralHarmonic_field p (p / 6) (by omega), actualScaledJet, actualN1] using h

private theorem metric_jet_hermite {F : Type*} [Field F]
    (Y n A N : F[X]) (h : F) (h2 : (2 : F) ≠ 0)
    (hW : (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hm : (1 - X ^ 2) *
      (Y * N.derivative + (-C (1 / 2 : F) * A - C h * Y) * n.derivative -
       Y.derivative * N - (-C (1 / 2 : F) * A - C h * Y).derivative * n) -
      X * Y * n = -C h - 2 * Y * (-C (1 / 2 : F) * A - C h * Y)) :
    hermiteOperator Y (Y * N + C (1 / 2 : F) * n * A) =
      X * n * Y ^ 2 + A + C h * Y ^ 3 := by
  have hu : (2 : F[X]) * C (1 / 2 : F) = 1 := by
    change C (2 : F) * C (1 / 2 : F) = 1
    rw [← C_mul]; simp [h2]
  dsimp only [hermiteOperator]
  simp only [derivative_add, derivative_sub, derivative_neg,
    derivative_mul, derivative_C] at hm ⊢
  linear_combination Y * hm +
    (C h * Y + 2 * C (1 / 2 : F) * A) * hW + A * hu

noncomputable def actualCmetric (hp : 19 ≤ p) : (ZMod p)[X] :=
  actualLegendreJacobi p * actualN1 p +
    C (1 / 2 : ZMod p) * properLegendreJacobi p * actualVariationField p (by omega)

theorem actual_Cmetric_degree (hp : 19 ≤ p) :
    (actualCmetric p hp).natDegree ≤ 2 * (p / 6) - 1 := by
  have hd : 1 ≤ p / 6 := by omega
  have hn := properLegendreJacobi_degree p (by omega : 7 ≤ p)
  have hn1 := actualN1_degree p hp
  have hy := actualLegendreJacobi_degree p
  have ha := actualVariationField_degree p (by omega : 7 ≤ p)
  have hnle : (properLegendreJacobi p).natDegree ≤ p / 6 - 1 := by omega
  have hleft : (actualLegendreJacobi p * actualN1 p).natDegree ≤ 2 * (p / 6) - 1 :=
    (natDegree_mul_le_of_le hy hn1).trans (by omega)
  have hcn : (C (1 / 2 : ZMod p) * properLegendreJacobi p).natDegree ≤ p / 6 - 1 :=
    (natDegree_C_mul_le _ _).trans hnle
  have hright : (C (1 / 2 : ZMod p) * properLegendreJacobi p *
      actualVariationField p (by omega : 7 ≤ p)).natDegree ≤ 2 * (p / 6) - 1 :=
    (natDegree_mul_le_of_le hcn ha).trans (by omega)
  exact (natDegree_add_le_of_le hleft hright).trans (by simp)

theorem actual_Cmetric_source (hp : 19 ≤ p) :
    hermiteOperator (actualLegendreJacobi p) (actualCmetric p hp) =
      X * properLegendreJacobi p * actualLegendreJacobi p ^ 2 +
        actualVariationField p (by omega) +
        C (fieldHarmonic p (p / 6)) * actualLegendreJacobi p ^ 3 := by
  have hm := actual_metric_first_source p hp
  rw [actual_scaled_jet_variation p hp] at hm
  exact metric_jet_hermite _ _ _ _ _
    (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
    (properLegendreJacobi_wronskian p (by omega)) hm

theorem actual_Cmetric_eq_actualC (hp : 19 ≤ p) :
    actualCmetric p hp = ActualNextHermite.actualC p hp := by
  have hY : actualLegendreJacobi p ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
    rw [actualLegendreJacobi_endpoint_one, eval_zero] at he
    exact one_ne_zero he
  apply hermite_low_unique (p / 6) (actualLegendreJacobi p) (properLegendreJacobi p)
    (actualCmetric p hp) (ActualNextHermite.actualC p hp)
    (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)) hY
    (actual_legendre_exact_degree p hp) (properLegendreJacobi_wronskian p (by omega))
    ((actual_Cmetric_degree p hp).trans_lt (by omega))
    ((actual_C_source_degree p hp).1.trans_lt (by omega))
  rw [actual_Cmetric_source p hp]
  exact (actual_C_source_degree p hp).2.symm

end WPFieldAssembly.ActualTC1Family
