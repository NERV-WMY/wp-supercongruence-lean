import WPFieldAssembly.ActualBpairLowHSeries

open scoped LaurentSeries
open HahnSeries

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

/-- This replaces every original integer exponent n by 2n, including arbitrary poles. -/
def lowHSeriesSquareEmbedding : ℤ ↪o ℤ where
  toFun n := 2 * n
  inj' := by
    intro a b h
    change (2 * a : ℤ) = 2 * b at h
    omega
  map_rel_iff' := by
    intro a b
    change (2 * a : ℤ) ≤ 2 * b ↔ a ≤ b
    omega

/-- The full x=w^2 differential pullback includes its literal Jacobian 2w. -/
noncomputable def lowHSeriesSquarePullback (Q : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.single 1 (2 : K) * HahnSeries.embDomain lowHSeriesSquareEmbedding Q

theorem lowHSeriesSquarePullback_monomial (a : K) (n : ℤ) :
    lowHSeriesSquarePullback (HahnSeries.single n a) = HahnSeries.single (2 * n + 1) (2 * a) := by
  rw [lowHSeriesSquarePullback, HahnSeries.embDomain_single, HahnSeries.single_mul_single]
  congr 1
  congr 1
  change 1 + 2 * n = 2 * n + 1
  omega

theorem lowHSeriesSquarePullback_coeff (Q : LaurentSeries K) (n : ℤ) :
    (lowHSeriesSquarePullback Q).coeff (2 * n + 1) = 2 * Q.coeff n := by
  rw [lowHSeriesSquarePullback, HahnSeries.coeff_single_mul]
  rw [show 2 * n + 1 - 1 = lowHSeriesSquareEmbedding n by change 2 * n + 1 - 1 = 2 * n; omega,
    HahnSeries.embDomain_coeff]

/-- The ramification-two residue formula is valid on the entire local expansion. -/
theorem lowHSeriesSquarePullback_residue (Q : LaurentSeries K) :
    (lowHSeriesSquarePullback Q).coeff (-1) = 2 * Q.coeff (-1) := by
  simpa only [show 2 * (-1 : ℤ) + 1 = -1 by rfl] using lowHSeriesSquarePullback_coeff Q (-1)

/-- A change w=epsilon*z multiplies the coefficient of z^j dz by epsilon^(j+1). -/
noncomputable def lowHSignedSeriesSquarePullback (ε : Kˣ) (Q : LaurentSeries K) : LaurentSeries K where
  coeff j := ((ε ^ (j + 1)).val : K) * (lowHSeriesSquarePullback Q).coeff j
  isPWO_support' := (lowHSeriesSquarePullback Q).isPWO_support.mono (by
    intro j hj
    change ((ε ^ (j + 1)).val : K) * (lowHSeriesSquarePullback Q).coeff j ≠ 0 at hj
    change (lowHSeriesSquarePullback Q).coeff j ≠ 0
    intro h
    exact hj (by rw [h, mul_zero]))

theorem lowHSignedSeriesSquarePullback_coeff (ε : Kˣ) (Q : LaurentSeries K) (n : ℤ) :
    (lowHSignedSeriesSquarePullback ε Q).coeff (2 * n + 1) =
      ((ε ^ (2 * n + 2)).val : K) * (2 * Q.coeff n) := by
  change ((ε ^ (2 * n + 1 + 1)).val : K) *
    (lowHSeriesSquarePullback Q).coeff (2 * n + 1) = _
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega, lowHSeriesSquarePullback_coeff]

/-- Both signs, and every nonzero local rescaling, keep the same tame factor two. -/
theorem lowHSignedSeriesSquarePullback_residue (ε : Kˣ) (Q : LaurentSeries K) :
    (lowHSignedSeriesSquarePullback ε Q).coeff (-1) = 2 * Q.coeff (-1) := by
  change ((ε ^ (-1 + 1 : ℤ)).val : K) * (lowHSeriesSquarePullback Q).coeff (-1) = _
  rw [show (-1 + 1 : ℤ) = 0 by rfl, zpow_zero, Units.val_one, one_mul,
    lowHSeriesSquarePullback_residue]

theorem lowHSignedSeriesSquarePullback_zero_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (Q : LaurentSeries K) :
    (lowHSignedSeriesSquarePullback ε Q).coeff (-1) = 0 ↔ Q.coeff (-1) = 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  rw [lowHSignedSeriesSquarePullback_residue]
  exact mul_eq_zero.trans (by simp only [h2, false_or])

end WPFieldAssembly.ActualBpairContraction
