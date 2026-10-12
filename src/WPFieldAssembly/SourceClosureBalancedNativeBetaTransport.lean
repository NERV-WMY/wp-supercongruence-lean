import WPFieldAssembly.SourceClosureUVFieldTransport
import WPFieldAssembly.SourceClosureOriginalJTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureUVFieldTransport

namespace WPFieldAssembly.SourceClosureBalancedNativeBetaTransport

set_option maxHeartbeats 1600000

variable {K L : Type*} [Field K] [Field L]

theorem original_HJP_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteJSource.HJP p : K[X]).map f=WPFiniteJSource.HJP p :=
  SourceClosureOriginalJTransport.original_HJP_transport f p

theorem original_GJ_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (WPFiniteJCarrier.GJ p)=WPFiniteJCarrier.GJ p :=
  SourceClosureOriginalJTransport.original_GJ_transport f p

/-- The original whole Z is specified in the base field without choosing a root. -/
noncomputable def originalDescendedZ (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  -LaurentPolynomial.C (1/2 : K)*descendedP p^2+WPFiniteJCarrier.GJ p

theorem original_descended_Z_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] :
    coefficientMap f (originalDescendedZ p)=originalDescendedZ p := by
  simp only [originalDescendedZ,map_add,map_neg,map_mul,map_pow,coefficientMap_C,
    descendedP_transport,original_GJ_transport,map_div₀,map_one,map_ofNat]

/-- This identifies the same original Z for both quadratic branches. -/
theorem original_descended_Z_original (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originalDescendedZ p=WPFiniteZSource.Z p u := by
  rw [originalDescendedZ,WPFiniteZSource.Z,originalP_descended p hp u hu]

/-- The original sharp 2p support descends faithfully; the coefficient at 2p remains. -/
theorem original_descended_Z_upper_bound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : Above (originalDescendedZ p : K[T;T⁻¹]) (2*(p : ℤ)) := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  have hz := (WPFiniteZSupport.actual_finite_whole_support p hp u hu).1
  rw [←original_descended_Z_original p hp u hu,
    ←original_descended_Z_transport f p] at hz
  intro j hj
  apply f.injective
  rw [map_zero]
  simpa only [coefficientMap_coeff] using hz j hj

end WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
