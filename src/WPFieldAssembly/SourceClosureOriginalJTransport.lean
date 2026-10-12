import WPFiniteZSupport
import WPActualChiSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource

namespace WPFieldAssembly.SourceClosureOriginalJTransport

set_option maxHeartbeats 1600000

variable {K L : Type*} [Field K] [Field L]

/-- The full original HJP transports directly from its finite coefficient definition. -/
theorem original_HJP_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteJSource.HJP p : K[X]).map f=WPFiniteJSource.HJP p := by
  simp only [WPFiniteJSource.HJP,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_one,Polynomial.map_ofNat,
    WPFiniteNC122.q,WPFiniteJSource.H,map_sum,map_add,map_div₀,map_pow,
    map_inv₀,map_natCast,map_intCast,map_ofNat]

/-- The whole original GJ transports with both full Frobenius phases. -/
theorem original_GJ_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (WPFiniteJCarrier.GJ p)=WPFiniteJCarrier.GJ p := by
  simp only [WPFiniteJCarrier.GJ,map_add,map_sub,map_mul,coefficientMap_C,
    coefficientMap_T,coefficientMap_toLaurent,coefficientMap_invert,
    original_HJP_transport,map_div₀,map_ofNat]

end WPFieldAssembly.SourceClosureOriginalJTransport
