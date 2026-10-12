import WPFieldAssembly.SourceClosurePeriodTransport
import WPFieldAssembly.SourceClosureBalancedHFSource
import WPFieldAssembly.BalancedVbalSuccessorHFBracketDefinition
import WPFieldAssembly.NativeClosureReflectionSource
import WPFieldAssembly.NativeClosureLowHCarrier

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualCommonTraceReduction
  WPFieldAssembly.ActualBpairContraction WPFieldAssembly.ActualGreenResidue
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedOriginalDensity
  WPFieldAssembly.SourceClosureBalancedHFSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.ActualBpairLowHLocalPole

namespace WPFieldAssembly.SourceClosureHFNativeTransport

set_option maxHeartbeats 2200000

variable {K : Type*} [Field K]

/-- Inversion identifies the original Green carrier with the same native H pullback. -/
theorem actual_common_H_inverse (p : ℕ) [Fact p.Prime] [CharP K p] :
    invert (coefficientMap (ActualThreePhase.φ (K := K) p) (commonHField p)) =
      (HpullK (K := K) p).toLaurent := by
  have hinv (G : K[T;T⁻¹]) : invert (invert G) = G :=
    LaurentPolynomial.involutive_invert G
  simp only [commonHField, coefficientMap_invert, hinv,
    coefficientMap_toLaurent, HpullK, Hpull]
  rfl

/-- The inverse-coordinate H is the terminating original native Euler polynomial. -/
theorem actual_common_H_native_cubic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    invert (coefficientMap (ActualThreePhase.φ (K := K) p) (commonHField p)) =
      (lowHCubicY (NativeClosureLowH.nativeH (K := K) p)).toLaurent := by
  rw [actual_common_H_inverse, NativeClosureLowH.nativeH_original_Hpull p hp]

theorem actual_LV_transport (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteLVSource.LV p : (ZMod p)[X]).map (ActualThreePhase.φ (K := K) p) =
      (WPFiniteLVSource.LV p : K[X]) := by
  simp only [WPFiniteLVSource.LV, WPFiniteLVSource.evenSquared, WPFiniteLVSource.V,
    WPFiniteWSource.squaredCoordinate, WPFiniteNC122.q, Polynomial.map_add,
    Polynomial.map_C, map_intCast, Polynomial.map_intCast, Polynomial.map_comp,
    Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_ofNat, Polynomial.map_sub, map_div₀, map_one, map_mul,
    map_ofNat, map_natCast, map_inv₀]

/-- Both full logarithmic halves retain the same harmonic shift. -/
theorem actual_LV_native_pair (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteLVSource.LV p : K[X]).toLaurent =
      (actualAK (K := K) p).toLaurent + LaurentPolynomial.C (hK (K := K) p) ∧
    invert (WPFiniteLVSource.LV p : K[X]).toLaurent =
      invert (actualAK (K := K) p).toLaurent + LaurentPolynomial.C (hK (K := K) p) := by
  have he := congrArg (fun Q : K[X] => Q.toLaurent) (actual_AK_source (K := K) p hp)
  simp only [map_sub, Polynomial.toLaurent_C] at he
  have h : (WPFiniteLVSource.LV p : K[X]).toLaurent =
      (actualAK (K := K) p).toLaurent + LaurentPolynomial.C (hK (K := K) p) := by
    exact (eq_add_of_sub_eq he.symm)
  exact ⟨h, by simpa only [map_add, invert_C] using congrArg invert h⟩

/-- The original comparison and its true reciprocal are attached before HF clearing. -/
theorem actual_comparison_native_P (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    coefficientMap (ActualThreePhase.φ (K := K) p) (comparisonField p) =
      WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u) := by
  rw [comparisonField_transport, ← descendedP_actual_comparison p hp,
    ← originalP_descended p hp u hu]

private theorem clearing_transport {J : Type*} [CommRing J] (f : J →+* K) :
    coefficientMap f (nativeClearingL : J[T;T⁻¹]) = (nativeClearingL : K[T;T⁻¹]) := by
  simp only [nativeClearingL, map_mul, map_add, map_ofNat, map_one,
    coefficientMap_T, coefficientMap_toLaurent, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]

private theorem Abar_transport {J : Type*} [Field J] (f : J →+* K) :
    coefficientMap f (WPFiniteZSource.Abar : J[X]).toLaurent =
      (WPFiniteZSource.Abar : K[X]).toLaurent := by
  simp only [coefficientMap_toLaurent, WPFiniteZSource.Abar, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]

private theorem finiteSeries_injective :
    Function.Injective (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
  intro F G h
  ext j
  exact congrArg (fun Q : LaurentSeries K => Q.coeff j) h

private theorem series_T_nat (n : ℕ) :
    localFiniteSeriesHom (T (n : ℤ) : K[T;T⁻¹]) =
      (localFiniteSeriesHom (T 1 : K[T;T⁻¹])) ^ n := by
  rw [← map_pow, T_pow]
  congr 1
  ring

private theorem series_T_neg_nat (n : ℕ) :
    localFiniteSeriesHom (T (-(n : ℤ)) : K[T;T⁻¹]) =
      ((localFiniteSeriesHom (T 1 : K[T;T⁻¹])) ^ n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← series_T_nat, ← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]

private theorem series_T_two :
    localFiniteSeriesHom (T 2 : K[T;T⁻¹]) =
      (localFiniteSeriesHom (T 1 : K[T;T⁻¹])) ^ 2 :=
  series_T_nat 2

private theorem series_T_neg_one :
    localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) =
      (localFiniteSeriesHom (T 1 : K[T;T⁻¹]))⁻¹ := by
  simpa only [Nat.cast_one, pow_one] using (series_T_neg_nat (K := K) 1)

private theorem series_T_neg_two :
    localFiniteSeriesHom (T (-2) : K[T;T⁻¹]) =
      ((localFiniteSeriesHom (T 1 : K[T;T⁻¹])) ^ 2)⁻¹ :=
  series_T_neg_nat 2

private theorem series_T_neg_five :
    localFiniteSeriesHom (T (-5) : K[T;T⁻¹]) =
      ((localFiniteSeriesHom (T 1 : K[T;T⁻¹])) ^ 5)⁻¹ :=
  series_T_neg_nat 5

private theorem native_clearing_factored : (nativeClearingL : K[T;T⁻¹]) =
    2 * T 1 * (T 1 + 1) * (WPFiniteZSource.Abar : K[X]).toLaurent := rfl

private theorem inverse_kw_R : invert (ActualKwFieldTrace.R : K[T;T⁻¹]) =
    T (-2) * (4 - 11 * T 1) := by
  simp only [ActualKwFieldTrace.R, map_mul, map_sub, map_ofNat, invert_T]
  have h := show (T (-2) * T 1 : K[T;T⁻¹]) = T (-1) by
    rw [← T_add]; norm_num
  have h' := show (T (-1) * T (-1) : K[T;T⁻¹]) = T (-2) by
    rw [← T_add]; norm_num
  linear_combination 4 * h' + 11 * h

private theorem inverse_HF_algebra {J : Type*} [Field J]
    (x a o S r z : J) (hx : x ≠ 0) (h2 : (2 : J) ≠ 0)
    (he : (x ^ 5)⁻¹ * (2 * x * (x + 1) * a) * o =
      (3 * (x⁻¹) ^ 2 * ((x ^ 2)⁻¹ * a) ^ 2 * (4 * x⁻¹ - 1) -
        (1 / 2) * ((x ^ 5)⁻¹ * (2 * x * (x + 1) * a)) *
          ((x ^ 2)⁻¹ * a) * ((x ^ 2)⁻¹ * (4 - 11 * x)) * x) * S +
      (x ^ 5)⁻¹ * (2 * x * (x + 1) * a) * ((x ^ 2)⁻¹ * a) *
        ((x ^ 2)⁻¹ * (4 - 11 * x)) * r * z) :
    x ^ 2 * (2 * x * (x + 1) * a) * o =
      -a ^ 2 * (-11 * x ^ 2 - 4 * x - 8) * S +
        2 * (x + 1) * a ^ 2 * (4 - 11 * x) / x * r * z := by
  linear_combination (norm := (field_simp [hx, h2]; ring)) x ^ 7 * he

/-- The original HF polynomial becomes one complete native cleared differential.
The reciprocal LV remains whole; no endpoint, odd quotient or added-point value is assigned. -/
theorem actual_HF_inverse_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    let A := (WPFiniteZSource.Abar : K[X]).toLaurent
    let P := WPFiniteZSource.P (K := K) p u
    let L := (WPFiniteLVSource.LV p : K[X]).toLaurent
    let O := invert (coefficientMap (ActualThreePhase.φ (K := K) p)
      (actualOmegaHFNumerator p hp))
    T 2 * (nativeClearingL : K[T;T⁻¹]) * O =
      -A ^ 2 * nativeZlogNumerator * (P + invert P) +
      2 * (T 1 + 1) * A ^ 2 * (4 - 11 * T 1) * T (-1) *
        invert (WPFiniteZSource.R p) *
        (invert P - LaurentPolynomial.C (1 / 3 : K) *
          (invert L - T (((p - 1) / 2 : ℕ) : ℤ) * L)) := by
  dsimp only
  let f : ZMod p →+* K := ActualThreePhase.φ p
  let F : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  let x := F (T 1)
  have hx : x ≠ 0 := by
    intro hz
    have he : x.coeff 1 = 1 := by
      rw [show x = localFiniteSeriesHom (T 1 : K[T;T⁻¹]) from rfl,
        localFiniteSeries_coeff, T_apply, if_pos rfl]
    rw [hz] at he
    exact zero_ne_one he
  have h2 : (2 : LaurentSeries K) ≠ 0 := by
    have h := WPFiniteField.denominator_ne_zero (K := K) p 2
      (Finset.mem_Ico.mpr (by omega))
    have he : (algebraMap K (LaurentSeries K)) (2 : K) ≠
        (algebraMap K (LaurentSeries K)) (0 : K) :=
      (algebraMap K (LaurentSeries K)).injective.ne h
    rw [map_ofNat, map_zero] at he
    exact he
  have hL : invert (nativeClearingL : K[T;T⁻¹]) =
      T (-5) * nativeClearingL := by
    have h := congrArg (coefficientMap f)
      (SourceClosureBalancedNativeReflection.actual_clearing_L_reflection p)
    simpa only [coefficientMap_invert, map_mul, coefficientMap_T,
      clearing_transport] using h
  have hA := WPFiniteZSource.invert_Abar (K := K)
  have hinv (G : K[T;T⁻¹]) : invert (invert G) = G :=
    LaurentPolynomial.involutive_invert G
  have hi := congrArg (fun Q : (ZMod p)[T;T⁻¹] => F (invert (coefficientMap f Q)))
    (actual_original_HF_attachment p hp)
  have hprint : coefficientMap f (actualPrintedHFNumerator p hp) =
      (3 * T 1 ^ 2 * (WPFiniteZSource.Abar : K[X]).toLaurent ^ 2 * (4 * T 1 - 1) -
        LaurentPolynomial.C (1 / 2 : K) * nativeClearingL *
          (WPFiniteZSource.Abar : K[X]).toLaurent * ActualKwFieldTrace.R * T (-1)) *
          (WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u)) +
      nativeClearingL * (WPFiniteZSource.Abar : K[X]).toLaurent * ActualKwFieldTrace.R *
        WPFiniteZSource.R p * (WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
          ((WPFiniteLVSource.LV p : K[X]).toLaurent - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
            invert (WPFiniteLVSource.LV p : K[X]).toLaurent)) := by
    have hmap
        (a l r d S P0 L0 : (ZMod p)[T;T⁻¹])
        (a' l' r' d' S' P' L' : K[T;T⁻¹])
        (ha : coefficientMap f a=a') (hl : coefficientMap f l=l')
        (hr : coefficientMap f r=r') (hd : coefficientMap f d=d')
        (hS : coefficientMap f S=S') (hP : coefficientMap f P0=P')
        (hLV : coefficientMap f L0=L') :
        coefficientMap f
          ((3*T 1^2*a^2*(4*T 1-1)-
              LaurentPolynomial.C (1/2 : ZMod p)*l*a*r*T (-1))*S+
            l*a*r*d*(P0-LaurentPolynomial.C (1/3 : ZMod p)*
              (L0-T (-(((p-1)/2 : ℕ) : ℤ))*invert L0))) =
          (3*T 1^2*a'^2*(4*T 1-1)-
              LaurentPolynomial.C (1/2 : K)*l'*a'*r'*T (-1))*S'+
            l'*a'*r'*d'*(P'-LaurentPolynomial.C (1/3 : K)*
              (L'-T (-(((p-1)/2 : ℕ) : ℤ))*invert L')) := by
      simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_one,
        coefficientMap_T,coefficientMap_C,map_div₀,coefficientMap_invert,
        ha,hl,hr,hd,hS,hP,hLV]
    have hP : coefficientMap f (descendedP p)=WPFiniteZSource.P p u := by
      rw [descendedP_transport]
      exact (originalP_descended p hp u hu).symm
    have hLV : coefficientMap f (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent=
        (WPFiniteLVSource.LV p : K[X]).toLaurent := by
      rw [coefficientMap_toLaurent,actual_LV_transport]
    exact hmap (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent nativeClearingL
      ActualKwFieldTrace.R (WPFiniteZSource.R p) (comparisonField p) (descendedP p)
      (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent
      (WPFiniteZSource.Abar : K[X]).toLaurent nativeClearingL
      ActualKwFieldTrace.R (WPFiniteZSource.R p)
      (WPFiniteZSource.P p u+invert (WPFiniteZSource.P p u)) (WPFiniteZSource.P p u)
      (WPFiniteLVSource.LV p : K[X]).toLaurent
      (Abar_transport f) (clearing_transport f) (ActualKwFieldTrace.R_map f)
      (originalR_transport f p) (actual_comparison_native_P p hp u hu) hP hLV
  simp only [map_mul, clearing_transport] at hi
  rw [hprint] at hi
  dsimp only [F] at hi
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_one,
    invert_C, invert_T, neg_neg, hinv, hL, hA, inverse_kw_R,
    localFiniteSeries_C, map_div₀] at hi
  have hLs : localFiniteSeriesHom (nativeClearingL : K[T;T⁻¹]) =
      2 * x * (x + 1) * localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent := by
    simpa only [map_mul, map_add, map_ofNat, map_one] using
      congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
        (native_clearing_factored (K := K))
  simp only [hLs, series_T_neg_five, series_T_neg_two, series_T_neg_one,
    series_T_nat] at hi
  have he := inverse_HF_algebra x
    (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)
    (localFiniteSeriesHom (invert (coefficientMap f (actualOmegaHFNumerator p hp))))
    (localFiniteSeriesHom (invert (WPFiniteZSource.P p u)) +
      localFiniteSeriesHom (WPFiniteZSource.P p u))
    (localFiniteSeriesHom (invert (WPFiniteZSource.R p)))
    (localFiniteSeriesHom (invert (WPFiniteZSource.P p u)) - (1 / 3) *
      (localFiniteSeriesHom (invert (WPFiniteLVSource.LV p : K[X]).toLaurent) -
        x ^ ((p - 1) / 2) * localFiniteSeriesHom (WPFiniteLVSource.LV p : K[X]).toLaurent))
    hx h2 hi
  apply finiteSeries_injective
  simp only [map_mul, map_pow, map_sub, map_add, map_neg, map_ofNat, map_one,
    nativeZlogNumerator, localFiniteSeries_C, map_div₀, series_T_two,
    series_T_neg_one, series_T_nat, hLs]
  linear_combination he

/-- The universal derivative keeps its actual inverse half-Frobenius phase. -/
theorem actual_R_inverse_weighted (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    2 * T (-2) * (4 - 11 * T 1 : K[T;T⁻¹]) ^ p * invert (WPFiniteZSource.R p) =
      (WPFiniteZSource.Abar : K[X]).toLaurent ^ (p - 1) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) * (4 * T (-(p : ℤ)) - 11) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (2 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 2 : K) = 1 := by
    change LaurentPolynomial.C (2 : K) * LaurentPolynomial.C (1 / 2 : K) = 1
    rw [← map_mul, mul_one_div_cancel h2, map_one]
  have ht : (T (-2) * T (p : ℤ) * T (-2) ^ (p - 1) : K[T;T⁻¹]) =
      T (-(p : ℤ)) := by
    rw [T_pow, ← T_add, ← T_add]
    congr 1
    omega
  simp only [WPFiniteZSource.R, map_mul, invert_C, invert_T, neg_neg]
  rw [map_pow, WPFiniteZSource.invert_Abar, WPFiniteZSource.invert_squared_power, mul_pow]
  calc
    _ = (2 * LaurentPolynomial.C (1 / 2 : K)) *
        (T (-2) * T (p : ℤ) * T (-2) ^ (p - 1)) * (4 - 11 * T 1) ^ p *
        (WPFiniteZSource.Abar : K[X]).toLaurent ^ (p - 1) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) := by ring
    _ = (WPFiniteZSource.Abar : K[X]).toLaurent ^ (p - 1) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        ((4 - 11 * T 1) ^ p * T (-(p : ℤ))) := by rw [hc, ht]; ring
    _ = _ := by rw [native_added_point_phase p]

/-- This is the original HF contribution after the full infinity-to-origin shift. -/
noncomputable def nativeHFOriginNumerator (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[T;T⁻¹] :=
  -2 * T 2 * (4 - 11 * T 1) ^ (p - 1) * (HpullK (K := K) p).toLaurent *
    invert (coefficientMap (ActualThreePhase.φ (K := K) p) (actualOmegaHFNumerator p hp))

/-- The source is the original HF summand with the actual full shift 2p,
not a separately chosen native differential. -/
theorem actual_HF_infinity_origin_numerator (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentPolynomial.C (-2 / 3 : K) * T (2 * (p : ℤ)) *
      invert (coefficientMap (ActualThreePhase.φ (K := K) p)
        (3 * (ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) ^ (p - 1) * commonHField p *
          actualOmegaHFNumerator p hp)) = nativeHFOriginNumerator (K := K) p hp := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : LaurentPolynomial.C (-2 / 3 : K) * 3 = (-2 : K[T;T⁻¹]) := by
    have hs : (-2 / 3 : K) * 3 = -2 := div_mul_cancel₀ _ h3
    simpa only [map_mul, map_neg, map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hs
  have ht : (T (2 * (p : ℤ)) * T (-2) ^ (p - 1) : K[T;T⁻¹]) = T 2 := by
    rw [T_pow, ← T_add]
    congr 1
    omega
  simp only [map_mul, map_pow, map_ofNat, ActualKwFieldTrace.R_map,
    actual_common_H_inverse, inverse_kw_R, mul_pow]
  rw [nativeHFOriginNumerator]
  calc
    _ = (LaurentPolynomial.C (-2 / 3 : K) * 3) *
        (T (2 * (p : ℤ)) * T (-2) ^ (p - 1)) * (4 - 11 * T 1) ^ (p - 1) *
        (HpullK (K := K) p).toLaurent *
        invert (coefficientMap (ActualThreePhase.φ (K := K) p)
          (actualOmegaHFNumerator p hp)) := by ring
    _ = _ := by rw [hc, ht]

private theorem joint_HF_algebra {F : Type*} [Field F]
    (p : ℕ) (hp : 1 ≤ p) (x a b y o g S k r z s ni φ : F)
    (hx : x ≠ 0) (ha : a ≠ 0)
    (hO : x ^ 2 * (2 * x * (x + 1) * a) * o =
      -a ^ 2 * g * S + 2 * (x + 1) * a ^ 2 * b / x * r * z)
    (hK : a ^ p * k = 2 * b ^ p * S)
    (hR : 2 / x ^ 2 * b ^ p * r = a ^ (p - 1) * s * ni * φ) :
    (2 * x * (x + 1) * b) * (-2 * x ^ 2 * b ^ (p - 1) * y * o) =
      a ^ (p + 1) * y * k * g +
        (2 * x * (x + 1) * b) * a ^ p * y * s * φ * (-ni * z) := by
  have hb : b ^ p = b ^ (p - 1) * b := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have ha' : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  apply mul_left_cancel₀ ha
  linear_combination (norm :=
    (simp only [pow_succ, hb, ha']; field_simp [hx]; ring))
    -2 * b ^ p * y * hO - a ^ 2 * y * g * hK -
      2 * x * (x + 1) * a ^ 2 * b * y * z * hR

/-- The SAME original HF density is attached to the complete native H/odd bracket.
All denominators are cleared as polynomials, including the added-point factor. -/
theorem actual_HF_native_joint_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    let A := (WPFiniteZSource.Abar : K[X]).toLaurent
    let y := (HpullK (K := K) p).toLaurent
    nativeZlogDenominator * nativeHFOriginNumerator p hp =
      A ^ (p + 1) * y * nativeKSigma p * nativeZlogNumerator +
      nativeZlogDenominator * A ^ p * y *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (4 * T (-(p : ℤ)) - 11) * nativeHFBracket p u := by
  dsimp only
  let F : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  let x := F (T 1)
  let A := (WPFiniteZSource.Abar : K[X]).toLaurent
  let B : K[T;T⁻¹] := 4 - 11 * T 1
  let P := WPFiniteZSource.P (K := K) p u
  let L := (WPFiniteLVSource.LV p : K[X]).toLaurent
  let Z := invert P - LaurentPolynomial.C (1 / 3 : K) *
    (invert L - T (((p - 1) / 2 : ℕ) : ℤ) * L)
  have hx : x ≠ 0 := by
    intro hz
    have he : x.coeff 1 = 1 := by
      rw [show x = localFiniteSeriesHom (T 1 : K[T;T⁻¹]) from rfl,
        localFiniteSeries_coeff, T_apply, if_pos rfl]
    rw [hz] at he
    exact zero_ne_one he
  have ha : F A ≠ 0 := by
    intro hz
    apply WPFiniteZSource.Abar_nonzero (K := K) p hp
    apply finiteSeries_injective
    simpa only [map_zero] using hz
  have hn : (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
      T (((p - 1) / 2 : ℕ) : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hz : nativeHFBracket p u = -T (-(((p - 1) / 2 : ℕ) : ℤ)) * Z := by
    rw [nativeHFBracket, ← (actual_LV_native_pair (K := K) p hp).1,
      ← (actual_LV_native_pair (K := K) p hp).2]
    dsimp only [Z, P, L]
    linear_combination LaurentPolynomial.C (1 / 3 : K) *
      (WPFiniteLVSource.LV p : K[X]).toLaurent * hn
  let O := invert (coefficientMap (ActualThreePhase.φ (K := K) p)
    (actualOmegaHFNumerator p hp))
  have hLs : localFiniteSeriesHom (nativeClearingL : K[T;T⁻¹]) =
      2 * x * (x + 1) * localFiniteSeriesHom A := by
    simpa only [map_mul, map_add, map_ofNat, map_one] using
      congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
        (native_clearing_factored (K := K))
  have hOs : x ^ 2 * (2 * x * (x + 1) * F A) * F O =
      -(F A) ^ 2 * F nativeZlogNumerator * F (P + invert P) +
        2 * (x + 1) * (F A) ^ 2 * F B / x *
          F (invert (WPFiniteZSource.R p)) * F Z := by
    have hO := congrArg F (actual_HF_inverse_cleared (K := K) p hp u hu)
    change F (T 2 * nativeClearingL * O) =
      F (-A ^ 2 * nativeZlogNumerator * (P + invert P) +
        2 * (T 1 + 1) * A ^ 2 * B * T (-1) *
          invert (WPFiniteZSource.R p) * Z) at hO
    dsimp only [F] at hO
    simp only [map_mul, map_pow, map_add, map_neg, map_ofNat, map_one,
      series_T_two, series_T_neg_one, hLs] at hO
    simpa only [F, map_add, div_eq_mul_inv] using hO
  have hKs : (F A) ^ p * F (nativeKSigma p) =
      2 * (F B) ^ p * F (P + invert P) := by
    have hK := actual_KSigma_cleared_source (K := K) p hp u hu
    change A ^ p * nativeKSigma p = 2 * B ^ p * (P + invert P) at hK
    simpa only [map_mul, map_pow, map_ofNat] using congrArg F hK
  have hRs : 2 / x ^ 2 * (F B) ^ p * F (invert (WPFiniteZSource.R p)) =
      (F A) ^ (p - 1) *
        F (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
        F (T (-(((p - 1) / 2 : ℕ) : ℤ))) * F (4 * T (-(p : ℤ)) - 11) := by
    have hR := actual_R_inverse_weighted (K := K) p hp
    change 2 * T (-2) * B ^ p * invert (WPFiniteZSource.R p) =
      A ^ (p - 1) * WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) * (4 * T (-(p : ℤ)) - 11) at hR
    have h := congrArg F hR
    dsimp only [F] at h
    simp only [map_mul, map_pow, map_ofNat, series_T_neg_two] at h
    simpa only [F, map_pow, div_eq_mul_inv] using h
  have he := joint_HF_algebra p (by omega) x (F A) (F B)
    (F (HpullK (K := K) p).toLaurent)
    (F O)
    (F (nativeZlogNumerator : K[T;T⁻¹])) (F (P + invert P))
    (F (nativeKSigma p)) (F (invert (WPFiniteZSource.R p))) (F Z)
    (F (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)))
    (F (T (-(((p - 1) / 2 : ℕ) : ℤ)))) (F (4 * T (-(p : ℤ)) - 11)) hx ha hOs hKs hRs
  apply finiteSeries_injective
  rw [hz]
  simpa only [F, nativeZlogDenominator, nativeHFOriginNumerator,
    map_mul, map_pow, map_add, map_neg, map_ofNat, map_one, series_T_two] using he

/-- The SAME complete HF density has a literal Laurent numerator at the native simple pole. -/
theorem actual_HF_native_Laurent_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    nativeHFOriginNumerator (K := K) p hp =
      (WPFiniteZSource.Abar : K[X]).toLaurent ^ p * (HpullK (K := K) p).toLaurent *
        (nativeHFSigmaNumerator p +
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
            (4 * T (-(p : ℤ)) - 11) * nativeHFBracket p u) := by
  have h := actual_HF_native_joint_cleared (K := K) p hp u hu
  dsimp only at h
  have hs := actual_HF_sigma_Laurent_clearing (K := K) p hp
  apply mul_left_cancel₀ (nativeZlogDenominator_ne_zero (K := K) p hp)
  linear_combination (norm := (simp only [pow_succ]; ring))
    h - (WPFiniteZSource.Abar : K[X]).toLaurent ^ p * (HpullK (K := K) p).toLaurent * hs

end WPFieldAssembly.SourceClosureHFNativeTransport
