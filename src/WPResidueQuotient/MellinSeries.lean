import WPResidueQuotient.MellinOrder
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Five actual formal Mellin coordinate series

The rho coordinate is extracted through the actual fraction-field embedding
into Laurent series. The independent u-series is a power series supported
in degrees divisible by six, multiplied by its displayed finite negative
monomial. Thus the construction supplies its support bound explicitly.
-/

noncomputable section

namespace WPResidueQuotient
namespace MellinFactors

open scoped BigOperators LaurentSeries RatFunc

abbrev LS := LaurentSeries ℚ

/-- The actual rho-coordinate map of the rational-function field. -/
def rhoCoordinate (r : Fin 5) : RF →ₗ[ℚ] ℚ :=
  (HahnSeries.coeff.linearMap (R := ℚ) (V := ℚ) (r.val : ℤ)).comp
    (algebraMap RF LS).toAddMonoidHom.toRatLinearMap

theorem rhoCoordinate_apply (r : Fin 5) (f : RF) :
    rhoCoordinate r f = (f : LS).coeff (r.val : ℤ) := rfl

def termCoordinate (r : Fin 5) (m n : ℤ) (a : ExponentVector) : ℚ :=
  rhoCoordinate r (mellinTerm m n a)

theorem termCoordinate_pole_relation (r : Fin 5) (m n : ℤ) (a : ExponentVector) :
    termCoordinate r (m + 1) n a -
        ∑ i, termCoordinate r (m + 1) n (increment a i) =
      (m : ℚ) * termCoordinate r m n a := by
  have hp := congrArg (rhoCoordinate r) (mellinTerm_pole_relation m n a)
  have hmul : (m : RF) * mellinTerm m n a = m • mellinTerm m n a :=
    (zsmul_eq_mul _ _).symm
  rw [hmul] at hp
  simp only [map_sub, map_sum, map_zsmul] at hp
  simpa only [termCoordinate, zsmul_eq_mul] using hp

theorem termCoordinate_derivative_relation
    (r : Fin 5) (m n : ℤ) (a : ExponentVector) (i j : Fin 6) :
    (a i - a j : ℚ) * termCoordinate r m n a +
        termCoordinate r (m + 1) n (increment a i) -
        termCoordinate r (m + 1) n (increment a j) = 0 := by
  have hd := congrArg (rhoCoordinate r) (mellinTerm_derivative_relation m n a i j)
  have hmul : ((a i - a j : ℤ) : RF) * mellinTerm m n a =
      (a i - a j : ℤ) • mellinTerm m n a :=
    (zsmul_eq_mul _ _).symm
  rw [hmul] at hd
  simp only [map_add, map_sub, map_zsmul, map_zero] at hd
  simpa only [termCoordinate, zsmul_eq_mul, Int.cast_sub] using hd

/-- Insert five zero coefficients between successive sequence entries. -/
def sparsePowerSeries : (ℕ → ℚ) →ₗ[ℚ] PowerSeries ℚ where
  toFun F := PowerSeries.mk (fun t => if t % 6 = 0 then F (t / 6) else 0)
  map_add' F G := by
    ext t
    simp only [map_add, PowerSeries.coeff_mk, Pi.add_apply]
    by_cases ht : t % 6 = 0 <;> simp [ht]
  map_smul' q F := by
    ext t
    simp only [map_smul, RingHom.id_apply, PowerSeries.coeff_mk, Pi.smul_apply]
    by_cases ht : t % 6 = 0 <;> simp [ht]

@[simp] theorem sparsePowerSeries_coeff (F : ℕ → ℚ) (t : ℕ) :
    PowerSeries.coeff t (sparsePowerSeries F) =
      if t % 6 = 0 then F (t / 6) else 0 := by
  simp only [sparsePowerSeries, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]

/-- The actual formal sum `sum_(n>=0) F_n u^(6n-A)`. -/
def seriesOfSequence (A : ℤ) : (ℕ → ℚ) →ₗ[ℚ] LS where
  toFun F := HahnSeries.single (-A) 1 * (sparsePowerSeries F : LS)
  map_add' F G := by
    change HahnSeries.single (-A) 1 * (sparsePowerSeries (F + G) : LS) = _
    rw [map_add, PowerSeries.coe_add, mul_add]
  map_smul' q F := by
    change HahnSeries.single (-A) 1 * (sparsePowerSeries (q • F) : LS) = _
    rw [map_smul, PowerSeries.coe_smul]
    exact mul_smul_comm _ _ _

theorem seriesOfSequence_coeff (A : ℤ) (F : ℕ → ℚ) (d : ℤ) :
    (seriesOfSequence A F).coeff d =
      if d + A < 0 then 0 else
        if (d + A).natAbs % 6 = 0 then F ((d + A).natAbs / 6) else 0 := by
  change (HahnSeries.single (-A) 1 * (sparsePowerSeries F : LS)).coeff d = _
  rw [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  have hi : d - -A = d + A := by ring
  rw [hi]
  simp only [sparsePowerSeries_coeff]

theorem seriesOfSequence_coeff_at (A : ℤ) (F : ℕ → ℚ) (n : ℕ) :
    (seriesOfSequence A F).coeff (6 * (n : ℤ) - A) = F n := by
  rw [seriesOfSequence_coeff]
  have hi : 6 * (n : ℤ) - A + A = ((6 * n : ℕ) : ℤ) := by push_cast; ring
  rw [hi]
  rw [if_neg (not_lt_of_ge (Int.natCast_nonneg (6 * n))), Int.natAbs_natCast]
  simp

theorem seriesOfSequence_coeff_below (A : ℤ) (F : ℕ → ℚ)
    (d : ℤ) (hd : d < -A) : (seriesOfSequence A F).coeff d = 0 := by
  rw [seriesOfSequence_coeff]
  have hi : d + A < 0 := by omega
  simp [hi]

/-- One of the five actual truncated coordinate series in the u-variable. -/
def mellinSeries (r : Fin 5) (m : ℤ) (a : ExponentVector) : LS :=
  seriesOfSequence (∑ i, a i) (fun n => termCoordinate r m (n : ℤ) a)

theorem mellinSeries_coeff_at (r : Fin 5) (m : ℤ) (a : ExponentVector) (n : ℕ) :
    (mellinSeries r m a).coeff (6 * (n : ℤ) - ∑ i, a i) =
      termCoordinate r m (n : ℤ) a :=
  seriesOfSequence_coeff_at _ _ _

theorem mellinSeries_coeff_below (r : Fin 5) (m : ℤ) (a : ExponentVector)
    (d : ℤ) (hd : d < -(∑ i, a i)) : (mellinSeries r m a).coeff d = 0 :=
  seriesOfSequence_coeff_below _ _ d hd

/-- The independent u-variable, distinct from the earlier rho-variable. -/
def uMonomial : LS := HahnSeries.single 1 1

theorem u_mul_seriesOfSequence_succ (A : ℤ) (F : ℕ → ℚ) :
    uMonomial * seriesOfSequence (A + 1) F = seriesOfSequence A F := by
  change HahnSeries.single 1 1 *
      (HahnSeries.single (-(A + 1)) 1 * (sparsePowerSeries F : LS)) =
    HahnSeries.single (-A) 1 * (sparsePowerSeries F : LS)
  rw [← mul_assoc, HahnSeries.single_mul_single, one_mul]
  have hi : 1 + -(A + 1) = -A := by ring
  rw [hi]

theorem u_mul_mellinSeries_increment
    (r : Fin 5) (m : ℤ) (a : ExponentVector) (i : Fin 6) :
    uMonomial * mellinSeries r (m + 1) (increment a i) =
      seriesOfSequence (∑ j, a j)
        (fun n => termCoordinate r (m + 1) (n : ℤ) (increment a i)) := by
  unfold mellinSeries
  rw [sum_increment]
  exact u_mul_seriesOfSequence_succ _ _

/-- The actual five coordinate series satisfy the pole-raising relation. -/
theorem mellinSeries_pole_relation (r : Fin 5) (m : ℤ) (a : ExponentVector) :
    mellinSeries r (m + 1) a -
        ∑ i, uMonomial * mellinSeries r (m + 1) (increment a i) =
      (m : ℚ) • mellinSeries r m a := by
  have hseq :
      (fun n : ℕ => termCoordinate r (m + 1) (n : ℤ) a) -
          ∑ i, (fun n : ℕ => termCoordinate r (m + 1) (n : ℤ) (increment a i)) =
        (m : ℚ) • (fun n : ℕ => termCoordinate r m (n : ℤ) a) := by
    funext n
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact termCoordinate_pole_relation r m (n : ℤ) a
  have hs := congrArg (seriesOfSequence (∑ i, a i)) hseq
  simp only [map_sub, map_sum, map_smul] at hs
  simp_rw [u_mul_mellinSeries_increment]
  exact hs

/-- The actual coordinate series kill the logarithmic derivative identity. -/
theorem mellinSeries_derivative_relation
    (r : Fin 5) (m : ℤ) (a : ExponentVector) (i j : Fin 6) :
    (a i - a j : ℚ) • mellinSeries r m a +
        uMonomial * mellinSeries r (m + 1) (increment a i) -
        uMonomial * mellinSeries r (m + 1) (increment a j) = 0 := by
  have hseq :
      (a i - a j : ℚ) • (fun n : ℕ => termCoordinate r m (n : ℤ) a) +
          (fun n : ℕ => termCoordinate r (m + 1) (n : ℤ) (increment a i)) -
          (fun n : ℕ => termCoordinate r (m + 1) (n : ℤ) (increment a j)) = 0 := by
    funext n
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact termCoordinate_derivative_relation r m (n : ℤ) a i j
  have hs := congrArg (seriesOfSequence (∑ i, a i)) hseq
  simp only [map_add, map_sub, map_smul, map_zero] at hs
  rw [u_mul_mellinSeries_increment, u_mul_mellinSeries_increment]
  exact hs

/-- Subtract a common diagonal exponent without canonicalizing individual
coordinates by any additional convention. -/
def subtractDiagonal (a : ExponentVector) (v : ℤ) : ExponentVector :=
  fun i => a i - v

theorem sum_subtractDiagonal (a : ExponentVector) (v : ℤ) :
    (∑ i, subtractDiagonal a v i) = (∑ i, a i) - 6 * v := by
  simp [subtractDiagonal, Finset.sum_sub_distrib]

theorem mellinTerm_reindex (m n : ℤ) (a : ExponentVector) (v : ℤ) :
    mellinTerm m n a = mellinTerm m (n - v) (subtractDiagonal a v) := by
  unfold mellinTerm
  have hp : poleIndex m n a = poleIndex m (n - v) (subtractDiagonal a v) := by
    unfold poleIndex
    rw [sum_subtractDiagonal]
    ring
  have hl : denominatorIndices n a = denominatorIndices (n - v) (subtractDiagonal a v) := by
    funext i
    unfold denominatorIndices subtractDiagonal
    ring
  rw [hp, hl]

theorem termCoordinate_reindex (r : Fin 5) (m n : ℤ) (a : ExponentVector) (v : ℤ) :
    termCoordinate r m n a = termCoordinate r m (n - v) (subtractDiagonal a v) := by
  unfold termCoordinate
  rw [mellinTerm_reindex m n a v]

theorem termCoordinate_lowerEndpoint_zero
    (r : Fin 5) (m n : ℤ) (a : ExponentVector) (hn : ∀ i, n < a i) :
    termCoordinate r m n a = 0 := by
  unfold termCoordinate
  rw [rhoCoordinate_apply]
  apply mellinTerm_lowerEndpoint_coeff_zero m n a hn
  exact_mod_cast r.isLt

/-- Discard a finite zero lower segment and reindex the sparse power series. -/
theorem sparsePowerSeries_shift (v : ℕ) (F : ℕ → ℚ) (hz : ∀ n, n < v → F n = 0) :
    sparsePowerSeries F =
      PowerSeries.X ^ (6 * v) * sparsePowerSeries (fun n => F (v + n)) := by
  ext t
  rw [PowerSeries.coeff_X_pow_mul']
  simp only [sparsePowerSeries_coeff]
  change (if t % 6 = 0 then F (t / 6) else 0) =
    if 6 * v ≤ t then
      (if (t - 6 * v) % 6 = 0 then F (v + (t - 6 * v) / 6) else 0) else 0
  by_cases ht : 6 * v ≤ t
  · rw [if_pos ht]
    have hmod : (t - 6 * v) % 6 = t % 6 := by omega
    have hdiv : v + (t - 6 * v) / 6 = t / 6 := by omega
    rw [hmod, hdiv]
  · rw [if_neg ht]
    by_cases hm : t % 6 = 0
    · rw [if_pos hm, hz (t / 6) (by omega)]
    · rw [if_neg hm]

theorem seriesOfSequence_shift (A : ℤ) (v : ℕ) (F : ℕ → ℚ)
    (hz : ∀ n, n < v → F n = 0) :
    seriesOfSequence A F =
      seriesOfSequence (A - 6 * (v : ℤ)) (fun n => F (v + n)) := by
  change HahnSeries.single (-A) 1 * (sparsePowerSeries F : LS) =
    HahnSeries.single (-(A - 6 * (v : ℤ))) 1 *
      (sparsePowerSeries (fun n => F (v + n)) : LS)
  rw [sparsePowerSeries_shift v F hz, PowerSeries.coe_mul, PowerSeries.coe_pow,
    PowerSeries.coe_X, ← mul_assoc]
  have hs : (HahnSeries.single (1 : ℤ) (1 : ℚ)) ^ (6 * v) =
      HahnSeries.single (((6 * v : ℕ) : ℤ)) 1 := by
    simp [HahnSeries.single_pow]
  rw [hs, HahnSeries.single_mul_single, one_mul]
  have hi : -A + ((6 * v : ℕ) : ℤ) = -(A - 6 * (v : ℤ)) := by push_cast; ring
  rw [hi]

/-- Actual canonicalization invariance of each of the five coordinate series.
The omitted n<v terms are zero by the proved Laurent order-five endpoint. -/
theorem mellinSeries_subtractDiagonal
    (r : Fin 5) (m : ℤ) (a : ExponentVector) (v : ℕ)
    (hv : ∀ i, (v : ℤ) ≤ a i) :
    mellinSeries r m a = mellinSeries r m (subtractDiagonal a (v : ℤ)) := by
  unfold mellinSeries
  rw [sum_subtractDiagonal]
  have hz : ∀ n : ℕ, n < v → termCoordinate r m (n : ℤ) a = 0 := by
    intro n hn
    apply termCoordinate_lowerEndpoint_zero
    intro i
    have hi := hv i
    omega
  rw [seriesOfSequence_shift (∑ i, a i) v _ hz]
  congr 1
  funext n
  rw [termCoordinate_reindex r m ((v + n : ℕ) : ℤ) a (v : ℤ)]
  have hi : ((v + n : ℕ) : ℤ) - (v : ℤ) = (n : ℤ) := by omega
  rw [hi]

end MellinFactors
end WPResidueQuotient
