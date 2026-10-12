import WPActualHasseReciprocal
import Mathlib.Tactic

open scoped Polynomial

namespace WPMomentPrecision.ConicCoordinates

variable {K : Type*} [Field K]

def cubic (t : K) : K := 4 * t ^ 3 - 3 * t
def q (t : K) : K := (1 - t ^ 2) * (4 * t ^ 2 - 1) ^ 2
def A (t : K) : K := (1 - t ^ 2) * (4 * t ^ 2 - 1)
def V (x : K) : K := (4 * x - 1) ^ 2 * (4 - x) / 125
def Q (x : K) : K := (4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)
def L (u : K) : K := u * (3 - 11 * u ^ 2) / (5 * u ^ 2 - 1)

/-- The original cubic parameter and its quadratic conic cover. -/
def conicT (a r : K) : K := (1 + r ^ 2) / (a * (1 - r ^ 2))
def conicW (r : K) : K := 2 * r / (1 - r ^ 2)

theorem cubic_square (t : K) : cubic t ^ 2 = 1 - q t := by
  unfold cubic q
  ring

theorem conic_parameterization (a r : K) (ha : a ^ 2 = 5)
    (ha0 : a ≠ 0) (hr : 1 - r ^ 2 ≠ 0) :
    conicW r ^ 2 = 5 * conicT a r ^ 2 - 1 := by
  unfold conicW conicT
  field_simp [ha0, hr]
  linear_combination (1 + r ^ 2) ^ 2 * ha

theorem conic_involution (a r : K) :
    conicT a (-r) = conicT a r ∧ conicW (-r) = -conicW r := by
  unfold conicT conicW
  constructor <;> ring

/-- Native V is q(t), with x=w^2, on both conic branches. -/
theorem native_V_on_conic (t w : K) (h5 : (5 : K) ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    V (w ^ 2) = q t := by
  unfold V q
  rw [hc]
  have h125 : (125 : K) ≠ 0 := by
    have h : (125 : K) = 5 ^ 3 := by norm_num
    rw [h]; exact pow_ne_zero _ h5
  field_simp [h125]
  ring

/-- The actual reciprocal Q is q(t/w); it is not V(x)/x^3. -/
theorem native_Q_on_conic (t w : K) (h5 : (5 : K) ≠ 0)
    (hw : w ≠ 0) (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    Q (w ^ 2) = q (t / w) := by
  unfold Q q
  have h125 : (125 : K) ≠ 0 := by
    have h : (125 : K) = 5 ^ 3 := by norm_num
    rw [h]; exact pow_ne_zero _ h5
  field_simp [hw, h125]
  linear_combination
    (-121 * w ^ 4 + (520 * t ^ 2 + 88) * w ^ 2 -
      400 * t ^ 4 - 80 * t ^ 2 - 16) * hc

/-- Exact denominator transport before any residue or finite part is taken. -/
theorem conic_A_transport (t w : K) (hw : w ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    A (t / w) = A t / w ^ 4 := by
  unfold A
  field_simp [hw]
  linear_combination -(w ^ 2 - 1) * hc

theorem conic_L_transport (t w : K) (hw : w ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    L (t / w) = cubic t / w := by
  unfold L cubic
  have hu : 5 * (t / w) ^ 2 - 1 = 1 / w ^ 2 := by
    field_simp [hw]
    linear_combination -hc
  rw [hu]
  field_simp [hw]
  linear_combination 3 * t * hc

/-- The exact Jacobian du/dt=-w^-3 follows from w^2=5t^2-1. -/
theorem conic_u_jacobian (t w : K) (hw : w ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    1 / w - t * (5 * t / w) / w ^ 2 = -1 / w ^ 3 := by
  field_simp [hw]
  linear_combination hc

/-- Literal inversion x -> 1/x exchanges the two native cubic roots. -/
theorem native_inverse (x : K) (hx : x ≠ 0) :
    V x⁻¹ = Q x := by
  unfold V Q
  field_simp [hx]

/-- The original x-line logarithmic density pulls back with its full negative sign. -/
theorem conic_dlog_V (t w : K) (h5 : (5 : K) ≠ 0)
    (ha : 1 - t ^ 2 ≠ 0) (hb : 4 * t ^ 2 - 1 ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    10 * t * (8 / (4 * w ^ 2 - 1) + 1 / (w ^ 2 - 4)) =
      -6 * cubic t / A t := by
  have he1 : 4 * w ^ 2 - 1 = 5 * (4 * t ^ 2 - 1) := by
    rw [hc]; ring
  have he2 : w ^ 2 - 4 = -5 * (1 - t ^ 2) := by
    rw [hc]; ring
  rw [he1, he2]
  unfold cubic A
  have hb' : (-1 + t ^ 2 * 4 : K) ≠ 0 := by
    convert hb using 1
    ring
  field_simp [ha, hb, hb', h5]
  have hi : (-1 + t ^ 2 * 4)⁻¹ * (-1 + t ^ 2 * 4) = 1 := inv_mul_cancel₀ hb'
  linear_combination 10 * t * hi

theorem fieldV_eval (p : ℕ) [Fact p.Prime] (f : ZMod p →+* K) (x : K) :
    ((WPHasseIntegralTransport.fieldV p).map f).eval x = V x := by
  have h125 : ((1 / 125 : ℚ) : ZMod p) = 1 / 125 := by
    norm_num [Rat.cast_def]
  simp only [Polynomial.eval_map, WPHasseIntegralTransport.fieldV,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
    Polynomial.eval₂_X, h125, map_div₀, map_one, map_ofNat]
  unfold V
  ring

/-- Whole native Hasse reciprocity after an arbitrary field extension. -/
theorem native_reciprocal_evaluation (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (f : ZMod p →+* K) (x : K) (hx : x ≠ 0) :
    ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (V x) =
      x ^ ((p - 1) / 2) *
        ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (Q x) := by
  have h := congrArg (fun P : (ZMod p)[X] => (P.map f).eval x)
    (WPActualHasseReciprocal.actual_native_Hasse_reciprocal p hp)
  rw [← Polynomial.reflect_map, WPActualHasseReciprocal.eval_reflect _ _
    (Polynomial.natDegree_map_le.trans (WPHasseIntegralTransport.actual_native_V_degree p hp))
    x hx] at h
  simp only [Polynomial.map_comp, Polynomial.eval_comp] at h
  rw [fieldV_eval p f x, fieldV_eval p f x⁻¹, native_inverse x hx] at h
  exact h

/-- The actual native square denominator on the two conic charts. -/
theorem native_conic_reciprocity (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (f : ZMod p →+* K) (t w : K) (h5 : (5 : K) ≠ 0) (hw : w ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (q (t / w)) =
      ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (q t) /
        w ^ (2 * ((p - 1) / 2)) := by
  apply (eq_div_iff (pow_ne_zero _ hw)).mpr
  have h := native_reciprocal_evaluation p hp f (w ^ 2) (pow_ne_zero 2 hw)
  rw [native_V_on_conic t w h5 hc, native_Q_on_conic t w h5 hw hc,
    ← pow_mul] at h
  linear_combination -h

private theorem density_cancellation (N : ℕ) (T B F H w : K) (hw : w ≠ 0) :
    H * T ^ (2 * N) / F * (-6 * T / B) =
      6 * (T / w) ^ (2 * N + 1) * H /
        ((B / w ^ 4) * (F / w ^ (2 * N))) * (-1 / w ^ 3) := by
  by_cases hB : B = 0
  · simp [hB]
  by_cases hF : F = 0
  · simp [hF]
  rw [div_pow, pow_succ]
  field_simp [hw, hB, hF]
  ring

/-- Complete IR19 native differential transport, before local residues are taken. -/
theorem actual_native_cross_density (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (f : ZMod p →+* K) (H : K[X]) (t w : K) (h5 : (5 : K) ≠ 0)
    (hw : w ≠ 0) (ha : 1 - t ^ 2 ≠ 0) (hb : 4 * t ^ 2 - 1 ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    H.eval (q (t / w)) * (1 - q t) ^ ((p - 1) / 2) /
        ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (q t) *
        (10 * t * (8 / (4 * w ^ 2 - 1) + 1 / (w ^ 2 - 4))) =
      6 * L (t / w) ^ p * H.eval (q (t / w)) /
        (A (t / w) *
          ((WPActualNativeHasse.nativeField p (p / 6)).map f).eval (q (t / w))) *
        (-1 / w ^ 3) := by
  rw [conic_dlog_V t w h5 ha hb hc, conic_A_transport t w hw hc,
    native_conic_reciprocity p hp f t w h5 hw hc, conic_L_transport t w hw hc,
    ← cubic_square t, ← pow_mul]
  rw [← congrArg (fun n : ℕ => (cubic t / w) ^ n)
    (WPActualHasseReciprocal.actual_half_exponent p hp)]
  exact density_cancellation ((p - 1) / 2) (cubic t) (A t) _ _ w hw

end WPMomentPrecision.ConicCoordinates
