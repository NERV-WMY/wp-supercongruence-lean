import WPFieldAssembly.ActualBpairLowHLinearSource
import WPFieldAssembly.ActualBpairLowHRemainingLogs
import WPFieldAssembly.ActualBpairLowHLocalPole

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairLowHLocalPole

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: This is the entire original IR71d Omega_hat source
   multiplied by y=H(V), for prime p >= 19 and any characteristic-p field K,
   with H(0)=0 attaching the actual y/Abar polynomial quotient.
   The original IR70 affine u/v and Cslot are printed literally. KB and DK
   remain arbitrary full Laurent inputs. The exact whole-source equality
   retains all origin and Frobenius phases, and is transported back through
   the injective full-coefficient Laurent-series embedding. There is no
   generated manifest, actual-u identification, IR71c reduction or final
   residue contraction asserted here. -/

/-- The exact rational coefficient residual before G*Xp is cancelled. -/
theorem lowH_whole_field_residual {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (G Xp Ds Dv A B κ h q2 y yl ylq z Q RD RvD KB DK : F) :
    let Bp := 4 * G - 11
    let φ := 4 * Xp - 11
    let w := Ds + Dv
    let M := A - B
    let L := 4 * A - B / 4
    let uc := κ - 4 * q2 * G / 5
    let vc := κ - 4 * q2 * Xp / 5
    let u := 3 * Bp * Ds / 5 + 2 * L / 5 + uc
    let v := 3 * φ * Dv / 5 + 2 * Xp * M / 5 + vc
    let c := q2 - h
    let Cslot := (4 * Xp - 6) * Ds / 5 - 2 * Xp * M / 15 + 4 * q2 * Xp / 15 - κ / 3
    (Cslot * y * DK - 5 * KB * yl / 6 +
      2 * φ * (u + h - 3 * Bp * w / 5) * RD / 15 +
      φ * (133 * G - 12) * w * RvD / 100 -
      (15 * G + 8) * v * ylq / 72 + Ds * ylq / 3 + G * φ * w * ylq / 8 +
      φ * w * yl / 15 - φ * w * z / 5 +
      (-5 * (v - c) / 3 - φ * (u + h) / 3 + φ * (33 * G - 20) * w / 8) * Q) -
    ((Cslot * y * DK - 5 * KB * yl / 6) +
      (4 * φ * L * RD / 75 - (15 + 8 * Xp) * M * ylq / 180 -
        2 * Xp * M * Q / 3 - 2 * φ * L * Q / 15) +
      ((5 / 6 - 11 * G / 8) * Ds * ylq + (11 / 15 - 4 * Xp / 15) * Dv * ylq +
        φ * w * yl / 15 - φ * w * z / 5 +
        φ * (133 * G - 12) * Ds * Q / 40 + φ * (33 * G - 28) * Dv * Q / 8) +
      (-2 * φ * Bp * Dv * RD / 25 + φ * (133 * G - 12) * w * RvD / 100) +
      2 * φ * (uc + h) * RD / 15 +
      (-5 * (vc - c) / 3 - φ * (uc + h) / 3) * Q -
      (15 * G + 8) * vc * ylq / 72) =
      (G * Xp - 1) * (6 * Ds - (A - B)) * ylq / 12 := by
  have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h6 : (6 : F) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; ring
  have h8 : (8 : F) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  have h12 : (12 : F) ≠ 0 := by convert mul_ne_zero h4 h3 using 1; ring
  have h15 : (15 : F) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; ring
  have h25 : (25 : F) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  have h40 : (40 : F) ≠ 0 := by convert mul_ne_zero h8 h5 using 1; ring
  have h72 : (72 : F) ≠ 0 := by convert mul_ne_zero h8 (pow_ne_zero 2 h3) using 1; ring
  have h75 : (75 : F) ≠ 0 := by convert mul_ne_zero h3 h25 using 1; ring
  have h100 : (100 : F) ≠ 0 := by convert mul_ne_zero h4 h25 using 1; ring
  have h180 : (180 : F) ≠ 0 := by
    convert mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 h3)) h5 using 1
    ring
  dsimp only
  field_simp [h3, h4, h5, h6, h8, h12, h15, h25, h40, h72, h75, h100, h180]
  ring

theorem lowH_whole_finiteSeries_injective : Function.Injective (localFiniteSeriesHom (K := K)) := by
  intro F G h
  apply LaurentPolynomial.ext
  intro n
  have he := congrArg (fun S : LaurentSeries K => S.coeff n) h
  change F.coeff n = G.coeff n at he
  exact he

noncomputable def lowHWholeCslot (p : ℕ) (κ q2 : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 5 : K) * (4 * T (-(p : ℤ)) - 6) * (Dstar p).toLaurent -
    LaurentPolynomial.C (2 / 15 : K) * T (-(p : ℤ)) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) +
    LaurentPolynomial.C (4 * q2 / 15) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)

noncomputable def lowHWholeCubicKernelSource (p : ℕ) (H : K[X])
    (KB DK : K[T;T⁻¹]) (κ q2 : K) : K[T;T⁻¹] :=
  lowHWholeCslot p κ q2 * (lowHCubicY H).toLaurent * DK -
    LaurentPolynomial.C (5 / 6 : K) * KB * (lowHqCubicDensity H).toLaurent

noncomputable def lowHWholeQuadraticSource (p : ℕ) (H : K[X]) : K[T;T⁻¹] :=
  -(LaurentPolynomial.C (2 / 25 : K) * (4 * T (-(p : ℤ)) - 11) * (4 * T (p : ℤ) - 11)) *
      ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent) +
    LaurentPolynomial.C (1 / 100 : K) * (4 * T (-(p : ℤ)) - 11) * (133 * T (p : ℤ) - 12) *
      ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent))

noncomputable def lowHWholeRegularDSource (p : ℕ) (H : K[X]) (κ h q2 : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 15 : K) * (4 * T (-(p : ℤ)) - 11) *
    (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ)) *
    (lowHCubicY H * (Dstar p).derivative).toLaurent

noncomputable def lowHWholeRegularRSource (p : ℕ) (H : K[X]) (κ h q2 : K) : K[T;T⁻¹] :=
  (-LaurentPolynomial.C (5 / 3 : K) *
      (LaurentPolynomial.C (κ - q2 + h) - LaurentPolynomial.C (4 * q2 / 5) * T (-(p : ℤ))) -
    LaurentPolynomial.C (1 / 3 : K) * (4 * T (-(p : ℤ)) - 11) *
      (LaurentPolynomial.C (κ + h) - LaurentPolynomial.C (4 * q2 / 5) * T (p : ℤ))) *
    (lowHBranchYQuotient H).toLaurent

/-- The entire IR71d source with the original affine u/v and arbitrary original KB/DK inputs. -/
noncomputable def lowHWholeOriginalKernelSource (p : ℕ) (H : K[X])
    (KB DK : K[T;T⁻¹]) (κ h q2 : K) : K[T;T⁻¹] :=
  let G := T (p : ℤ)
  let Xp := T (-(p : ℤ))
  let Bp := 4 * G - 11
  let φ := 4 * Xp - 11
  let Ds := (Dstar p : K[X]).toLaurent
  let Dv := invert Ds
  let w := Dsym p
  let A := (lowHLog p 4).toLaurent
  let B := (lowHLog p (1 / 4)).toLaurent
  let uc := LaurentPolynomial.C κ - LaurentPolynomial.C (4 * q2 / 5) * G
  let vc := LaurentPolynomial.C κ - LaurentPolynomial.C (4 * q2 / 5) * Xp
  let u := LaurentPolynomial.C (3 / 5 : K) * Bp * Ds +
    LaurentPolynomial.C (2 / 5 : K) * (4 * A - LaurentPolynomial.C (1 / 4 : K) * B) + uc
  let v := LaurentPolynomial.C (3 / 5 : K) * φ * Dv +
    LaurentPolynomial.C (2 / 5 : K) * Xp * (A - B) + vc
  let y := (lowHCubicY H).toLaurent
  let yl := (lowHqCubicDensity H).toLaurent
  let ylq := lowHLinearYQLog H
  let z := lowHLinearYOverX H
  let Q := (lowHBranchYQuotient H).toLaurent
  lowHWholeCslot p κ q2 * y * DK - LaurentPolynomial.C (5 / 6 : K) * KB * yl +
    LaurentPolynomial.C (2 / 15 : K) * φ *
      (u + LaurentPolynomial.C h - LaurentPolynomial.C (3 / 5 : K) * Bp * w) * (y * D Ds) +
    LaurentPolynomial.C (1 / 100 : K) * φ * (133 * G - 12) * w * (y * D Dv) -
    LaurentPolynomial.C (1 / 72 : K) * (15 * G + 8) * v * ylq +
    LaurentPolynomial.C (1 / 3 : K) * Ds * ylq + LaurentPolynomial.C (1 / 8 : K) * G * φ * w * ylq +
    LaurentPolynomial.C (1 / 15 : K) * φ * w * yl - LaurentPolynomial.C (1 / 5 : K) * φ * w * z +
    (-LaurentPolynomial.C (5 / 3 : K) * (v - LaurentPolynomial.C (q2 - h)) -
      LaurentPolynomial.C (1 / 3 : K) * φ * (u + LaurentPolynomial.C h) +
      LaurentPolynomial.C (1 / 8 : K) * φ * (33 * G - 20) * w) * Q

/-- The whole source is collected before any residue, endpoint, or phase is removed. -/
theorem lowH_whole_original_kernel_decomposition (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0)
    (KB DK : K[T;T⁻¹]) (κ h q2 : K) :
    lowHWholeOriginalKernelSource p H KB DK κ h q2 =
      lowHWholeCubicKernelSource p H KB DK κ q2 +
      lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
        (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0) +
      lowHOriginalDLinearSource p H + lowHWholeQuadraticSource p H +
      lowHWholeRegularDSource p H κ h q2 + lowHWholeRegularRSource p H κ h q2 +
      lowHOriginalQLogConstantSource p H κ q2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2S : (2 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (2 : K) ≠ 0
    exact HahnSeries.C_ne_zero h2
  have h3S : (3 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (3 : K) ≠ 0
    exact HahnSeries.C_ne_zero h3
  have h5S : (5 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (5 : K) ≠ 0
    exact HahnSeries.C_ne_zero h5
  have hGX : (localFiniteSeriesHom (T (p : ℤ) : K[T;T⁻¹])) *
      localFiniteSeriesHom (T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have he := lowH_whole_field_residual h2S h3S h5S
    (localFiniteSeriesHom (T (p : ℤ))) (localFiniteSeriesHom (T (-(p : ℤ))))
    (localFiniteSeriesHom (Dstar p).toLaurent) (localFiniteSeriesHom (invert (Dstar p).toLaurent))
    (localFiniteSeriesHom (lowHLog p 4).toLaurent)
    (localFiniteSeriesHom (lowHLog p (1 / 4)).toLaurent)
    (algebraMap K (LaurentSeries K) κ) (algebraMap K (LaurentSeries K) h)
    (algebraMap K (LaurentSeries K) q2)
    (localFiniteSeriesHom (lowHCubicY H).toLaurent) (localFiniteSeriesHom (lowHqCubicDensity H).toLaurent)
    (localFiniteSeriesHom (lowHLinearYQLog H)) (localFiniteSeriesHom (lowHLinearYOverX H))
    (localFiniteSeriesHom (lowHBranchYQuotient H).toLaurent)
    (localFiniteSeriesHom ((lowHCubicY H).toLaurent * D (Dstar p).toLaurent))
    (localFiniteSeriesHom ((lowHCubicY H).toLaurent * D (invert (Dstar p).toLaurent)))
    (localFiniteSeriesHom KB) (localFiniteSeriesHom DK)
  dsimp only at he
  rw [hGX, sub_self, zero_mul, zero_mul, zero_div] at he
  apply lowH_whole_finiteSeries_injective
  rw [lowHWholeOriginalKernelSource, lowHWholeCubicKernelSource, lowHWholeQuadraticSource,
    lowHWholeRegularDSource, lowHWholeRegularRSource, lowHOriginalDLinearSource,
    lowHOriginalQLogConstantSource, lowHWholeCslot, lowHRemainingLogDensity]
  rw [← lowH_linear_JQ_origin_source p hp H]
  simp only [lowHBranchYQuotient_source H h0, Dsym, map_mul, D_toLaurent] at he ⊢
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, localFiniteSeries_C,
    map_div₀, map_one] at he ⊢
  apply sub_eq_zero.mp
  convert he using 1; ring

end WPFieldAssembly.ActualBpairContraction
