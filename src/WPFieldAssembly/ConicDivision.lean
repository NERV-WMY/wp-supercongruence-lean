import WPActualRankTwoProper

open scoped Polynomial
open Polynomial

namespace WPFieldAssembly.ConicDivision

set_option maxHeartbeats 800000

variable {K : Type*} [CommRing K]

noncomputable def conicC (A v F G : K[X]) : K[X] :=
  A ^ 2 * (F * G.derivative.derivative + G * F.derivative.derivative - F.derivative * G.derivative) +
  A * A.derivative * (F * G.derivative + G * F.derivative) + v * F * G

noncomputable def firstNumerator (A y H E : K[X]) : K[X] :=
  A * (y * H.derivative - 2 * y.derivative * H) + E * y ^ 3

theorem firstNumerator_identity (A v y H E : K[X]) :
    A * y ^ 2 * (y * (firstNumerator A y H E).derivative -
      y.derivative * firstNumerator A y H E) =
    y ^ 2 * (conicC A v (y ^ 2) H +
      A * (E.derivative * (y ^ 2) ^ 2 + E * y ^ 2 * (y ^ 2).derivative)) -
      H * conicC A v (y ^ 2) (y ^ 2) := by
  simp [firstNumerator, conicC, derivative_mul, derivative_pow, map_ofNat]
  ring

/-- The proper Wronskian gives a whole polynomial quotient without pointwise inverses. -/
theorem wronskian_division [IsDomain K] (A y m M : K[X]) (hy : y ≠ 0)
    (hW : A * (y * m.derivative - y.derivative * m) = 1 - y ^ 2)
    (hM : y * M.derivative - y.derivative * M = 0) :
    ∃ b : K[X], M = y * b ∧ b.derivative = 0 := by
  let b : K[X] := M * (y + A * m.derivative) - A * M.derivative * m
  have hb : M = y * b := by
    dsimp [b]
    linear_combination -M * hW + A * m * hM
  refine ⟨b, hb, ?_⟩
  have hz : y ^ 2 * b.derivative = 0 := by
    rw [hb] at hM
    simp only [derivative_mul] at hM
    linear_combination hM
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hy)

theorem source_divided_kernel [IsDomain K] (A v y m H E : K[X])
    (hA : A ≠ 0) (hy : y ≠ 0)
    (hW : A * (y * m.derivative - y.derivative * m) = 1 - y ^ 2)
    (hself : conicC A v (y ^ 2) (y ^ 2) = 0)
    (hsource : conicC A v (y ^ 2) H +
      A * (E.derivative * (y ^ 2) ^ 2 + E * y ^ 2 * (y ^ 2).derivative) = 0) :
    ∃ b : K[X], firstNumerator A y H E = y * b ∧ b.derivative = 0 := by
  have hz : (A * y ^ 2) * (y * (firstNumerator A y H E).derivative -
      y.derivative * firstNumerator A y H E) = 0 := by
    calc
      _ = y ^ 2 * (conicC A v (y ^ 2) H +
          A * (E.derivative * (y ^ 2) ^ 2 + E * y ^ 2 * (y ^ 2).derivative)) -
          H * conicC A v (y ^ 2) (y ^ 2) := firstNumerator_identity A v y H E
      _ = 0 := by rw [hsource, hself]; ring
  have hM : y * (firstNumerator A y H E).derivative -
      y.derivative * firstNumerator A y H E = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hA (pow_ne_zero 2 hy))
  exact wronskian_division A y m (firstNumerator A y H E) hy hW hM

theorem source_kernel_divisor (A y m M b L : K[X])
    (hW : A * (y * m.derivative - y.derivative * m) = 1 - y ^ 2)
    (hMb : M = y * b) (hML : M = A * L) :
    b = A * (y * L + (y * m.derivative - y.derivative * m) * b) := by
  linear_combination -b * hW - y * hMb + y * hML

end WPFieldAssembly.ConicDivision
