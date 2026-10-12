import WPFieldAssembly.NativeClosureEndValue
import WPFieldAssembly.NativeClosureEndKernel
import WPFieldAssembly.ActualBpairNativeTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteAffineLog
open WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairNativeTail

namespace WPFieldAssembly.ActualBpairContraction

variable {K L : Type*} [Field K] [Field L]
set_option maxHeartbeats 1800000

theorem endKernel_Dstar_map (p : ℕ) (f : K →+* L) :
    (Dstar p : K[X]).map f = (Dstar p : L[X]) := by
  simp only [Dstar, WPFiniteWSource.deltaE, WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_div₀, map_sub, map_one, map_ofNat, map_natCast,
    map_pow, map_mul, map_inv₀]

theorem endKernel_LP_map (p : ℕ) (f : K →+* L) :
    (LP p : K[X]).map f = (LP p : L[X]) := by
  simp only [LP, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, map_inv₀, map_natCast]

theorem endKernel_W0_map (p : ℕ) (f : K →+* L) :
    (endKernelW0 p : K[X]).map f = (endKernelW0 p : L[X]) := by
  simp only [endKernelW0, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_neg, Polynomial.map_C, endKernel_Dstar_map,
    WPFiniteNC122.q, map_sub, map_mul, map_div₀, map_ofNat, map_intCast]

theorem endKernel_W1_map (p : ℕ) (f : K →+* L) :
    (endKernelW1 p : K[X]).map f = (endKernelW1 p : L[X]) := by
  simp only [endKernelW1, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_X,
    Polynomial.map_ofNat,
    endKernel_Dstar_map, endKernel_LP_map, WPFiniteNC122.q,
    map_mul, map_div₀, map_ofNat, map_one, map_intCast]

/-- The complete two-band source extends coefficientwise, including its -p slot. -/
theorem endKernel_Chi0_map (p : ℕ) (f : K →+* L) :
    WPActualChiSource.coefficientMap f (endKernelChi0 p : K[T;T⁻¹]) =
      (endKernelChi0 p : L[T;T⁻¹]) := by
  simp only [endKernelChi0, map_add, map_mul,
    WPActualChiSource.coefficientMap_toLaurent, WPActualChiSource.coefficientMap_T,
    endKernel_W0_map, endKernel_W1_map]

theorem endKernel_D_map (f : K →+* L) (U : K[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (D U) =
      D (WPActualChiSource.coefficientMap f U) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, map_mul, map_intCast]

/-- The same base-field derivative is transported to any characteristic-p field. -/
theorem endKernel_derivative_rational_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (literalKB (K := K) p * D (endKernelChi0 p)).coeff (-1) =
      -(3 / 10 : K) * (Dstar p : K[X]).coeff 0 +
        223 * WPFiniteNC122.q p / 30 -
          5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 := by
  let f : ZMod p →+* K := ActualThreePhase.φ p
  have he := congrArg f (endKernel_derivative_rational p hp)
  have h0 : f ((Dstar p : (ZMod p)[X]).coeff 0) = (Dstar p : K[X]).coeff 0 := by
    rw [← Polynomial.coeff_map, endKernel_Dstar_map]
  rw [← WPActualChiSource.coefficientMap_coeff, map_mul,
    coefficientMap_literalKB, endKernel_D_map, endKernel_Chi0_map] at he
  simpa only [map_add, map_sub, map_neg, map_mul, map_div₀, map_ofNat,
    WPFiniteNC122.q, map_intCast, h0] using he

/-- The coefficient at the fifth origin is its actual entropy carrier. -/
theorem endKernel_derivative_fifth (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (literalKB (K := K) p * D (endKernelChi0 p)).coeff (-1) =
      WPFifthEntropy.C p u / 10 + 223 * WPFiniteNC122.q p / 30 -
        5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 := by
  rw [endKernel_derivative_rational_K p hp, Dstar_origin_fifth p hp u hu]
  have h3 : (3 : K) ≠ 0 := by
    simpa using WPFiniteField.denominator_ne_zero (K := K) p 3
      (Finset.mem_Ico.mpr (by omega))
  rw [show -(3 / 10 : K) * (-WPFifthEntropy.C p u / 3) =
      WPFifthEntropy.C p u / 10 by
    calc
      _ = (3 / 3 : K) * (WPFifthEntropy.C p u / 10) := by ring
      _ = _ := by rw [div_self h3, one_mul]]

/-- The derivative value belongs to the original P-(actualAK+h)/3 source. -/
theorem actual_P_endKernel_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (literalKB (K := K) p *
      D (WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
        ((actualAK p : K[X]).toLaurent +
          LaurentPolynomial.C (WPFiniteNC122.h p)))).coeff (-1) =
      WPFifthEntropy.C p u / 10 + 223 * WPFiniteNC122.q p / 30 -
        5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 := by
  rw [actual_P_endKernel_source p hp u hu, endKernel_derivative_fifth p hp u hu]

end WPFieldAssembly.ActualBpairContraction
