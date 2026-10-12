import WPFieldAssembly.SourceClosureUVDescent
import WPFieldAssembly.SourceClosureUVPositiveSource
import WPFieldAssembly.SourceClosureUVCanonicalHoles
import WPActualChiSource
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Algebra.CharP.Algebra

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureUVPrimitiveSource
  WPFieldAssembly.SourceClosureUVPositiveSource
  WPFieldAssembly.SourceClosureUVDescent

namespace WPFieldAssembly.SourceClosureUVFieldTransport

/- A faithful extension supplies a root only inside the proof. Every full
   carrier and numerator below is specified over the original field. -/

variable {K L : Type*} [Field K] [Field L]

theorem polynomial_eval_transport (f : K →+* L) (P : K[X]) (z : K) :
    f (P.eval z)=(P.map f).eval (f z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [eval_add,map_add,Polynomial.map_add,hP,hQ]
  | monomial n c =>
    simp only [eval_monomial,Polynomial.map_monomial,map_mul,map_pow]

theorem deltaE_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteWSource.deltaE p : K[X]).map f=WPFiniteWSource.deltaE p := by
  simp only [WPFiniteWSource.deltaE,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
    map_div₀,map_pow,map_sub,map_ofNat,map_one,map_mul,map_natCast]

theorem descendedC_transport (f : K →+* L) (p : ℕ) :
    f (descendedC p)=descendedC p := by
  rw [descendedC,polynomial_eval_transport,deltaE_transport]
  simp only [map_div₀,map_one,map_ofNat,descendedC]

theorem epsilon_transport (f : K →+* L) (p : ℕ) :
    f (WPFiniteABSourceTail.epsilon p)=WPFiniteABSourceTail.epsilon p := by
  simp only [WPFiniteABSourceTail.epsilon,map_pow,map_ofNat]

theorem squaredCoordinate_transport (f : K →+* L) :
    (WPFiniteWSource.squaredCoordinate : K[X]).map f=WPFiniteWSource.squaredCoordinate := by
  simp only [WPFiniteWSource.squaredCoordinate,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,map_inv₀,map_ofNat]

theorem W_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteWSource.W p : K[X]).map f=WPFiniteWSource.W p := by
  simp only [WPFiniteWSource.W,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_sub,Polynomial.map_comp,deltaE_transport,squaredCoordinate_transport,
    map_div₀,map_mul,map_ofNat,epsilon_transport]
  rw [polynomial_eval_transport,deltaE_transport]
  simp only [map_div₀,map_one,map_ofNat]

theorem integratedGeometric_transport (f : K →+* L) (i : ℕ) (z : K) :
    (WPFiniteProductTail.integratedGeometric i z).map f=
      WPFiniteProductTail.integratedGeometric i (f z) := by
  simp only [WPFiniteProductTail.integratedGeometric,Polynomial.map_sum,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
    map_div₀,map_pow,map_natCast]

theorem unitPrimitive_transport (f : K →+* L) (p : ℕ) (W : K[X]) (z : K) :
    (WPFiniteProductTail.unitPrimitiveP p W z).map f=
      WPFiniteProductTail.unitPrimitiveP p (W.map f) (f z) := by
  simp only [WPFiniteProductTail.unitPrimitiveP,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,integratedGeometric_transport,coeff_map]

theorem originalHsym_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (originalHsym p)=originalHsym p := by
  simp only [originalHsym,map_add,map_sub,map_mul,coefficientMap_invert,
    coefficientMap_toLaurent,coefficientMap_C,originalHx,originalHa,originalHb,originalHm,
    unitPrimitive_transport,W_transport,map_zero,map_neg,map_one,map_div₀,map_ofNat]

theorem originalK0_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (originalK0 p)=originalK0 p := by
  simp only [originalK0,map_sub,map_mul,map_add,coefficientMap_C,coefficientMap_T,
    map_div₀,map_mul,map_ofNat,epsilon_transport]

theorem scaledLog_transport (f : K →+* L) (p : ℕ) (c : K) :
    coefficientMap f (scaledLog p c)=scaledLog p (f c) := by
  simp only [scaledLog_full,map_sum,coefficientMap_monomial,
    map_div₀,map_pow,map_natCast]

theorem scaledDilog_transport (f : K →+* L) (p : ℕ) (c : K) :
    coefficientMap f (scaledDilog p c)=scaledDilog p (f c) := by
  simp only [scaledDilog_full,map_sum,coefficientMap_monomial,
    map_div₀,map_pow,map_natCast]

theorem originalJ2log_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (originalJ2log p)=originalJ2log p := by
  simp only [originalJ2log,map_mul,map_sub,coefficientMap_C,coefficientMap_T,
    scaledDilog_transport,map_div₀,map_one,map_ofNat]

theorem originalJab_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (originalJa p+originalJb p)=originalJa p+originalJb p := by
  simp only [originalJa,originalJb,map_add,map_mul,map_sub,coefficientMap_C,
    coefficientMap_T,scaledLog_transport,map_div₀,map_one,map_ofNat,epsilon_transport]

theorem descendedZE_transport (f : K →+* L) (p : ℕ) :
    f (descendedZE p)=descendedZE p := by
  simp only [descendedZE,map_add,map_div₀,map_mul,map_ofNat,epsilon_transport,
    descendedC_transport,polynomial_eval_transport,W_transport,map_one]

theorem descendedUcan_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (descendedUcan p)=descendedUcan p := by
  simp only [descendedUcan,map_sub,map_mul,coefficientMap_C,originalK0_transport,
    originalHsym_transport,descendedZE_transport,originalJab_transport,
    originalJ2log_transport,map_div₀,map_one,map_ofNat]

theorem coefficientMap_derivative (f : K →+* L) (F : K[T;T⁻¹]) :
    coefficientMap f (D F)=D (coefficientMap f F) := by
  ext j
  simp only [coefficientMap_coeff,D_coeff,map_mul,map_intCast]

theorem coefficientMap_injective_field (f : K →+* L) :
    Function.Injective (coefficientMap f) := by
  intro F G h
  ext j
  apply f.injective
  have hj := congrArg (fun P : L[T;T⁻¹] => P.coeff j) h
  simpa only [coefficientMap_coeff] using hj

theorem loopD_transport (f : K →+* L) (n : ℕ) (x y : K) :
    f (WPFiniteLoop.D n x y)=WPFiniteLoop.D n (f x) (f y) := by
  simp only [WPFiniteLoop.D,map_sum,map_div₀,map_mul,map_pow,map_natCast]

theorem finiteLog_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] (x : K) :
    f (WPFiniteField.ell p x)=WPFiniteField.ell p (f x) := by
  simp only [WPFiniteField.ell,map_sum,map_div₀,map_pow,map_natCast]

theorem finiteDilog_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] (x : K) :
    f (WPFiniteField.R p x)=WPFiniteField.R p (f x) := by
  simp only [WPFiniteField.R,map_sum,map_div₀,map_pow,map_natCast]

theorem descendedU0_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] : f (descendedU0 p)=descendedU0 p := by
  simp only [descendedU0,map_add,map_sub,map_mul,map_div₀,map_ofNat,map_one,map_zero,
    map_neg,map_intCast,WPFiniteNC122.q,loopD_transport,finiteLog_transport,
    finiteDilog_transport]

theorem descendedU_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] : coefficientMap f (descendedU p)=descendedU p := by
  simp only [descendedU,map_sub,coefficientMap_C,descendedUcan_transport,
    descendedU0_transport]

theorem branch_eval_transport (f : K →+* L) (F : K[T;T⁻¹]) :
    f (LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) F)=
      LaurentPolynomial.eval₂ (RingHom.id L) (-1 : Lˣ) (coefficientMap f F) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => simp only [map_add,hF,hG]
  | C_mul_T n a =>
    rw [coefficientMap_monomial]
    simp only [map_mul,LaurentPolynomial.eval₂_C,LaurentPolynomial.eval₂_T,
      RingHom.id_apply]
    congr 1
    have hu := map_zpow (Units.map f.toMonoidHom) (-1 : Kˣ) n
    have hm : Units.map f.toMonoidHom (-1 : Kˣ)=(-1 : Lˣ) := by
      ext
      simp
    rw [hm] at hu
    exact congrArg (fun v : Lˣ => (v : L)) hu

noncomputable def descendedInvisibleP (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  LaurentPolynomial.C (-4*(WPFiniteNC122.q p+descendedC p)/15 : K)*T (p : ℤ)+
    LaurentPolynomial.C (17*descendedC p/15 : K)+
    LaurentPolynomial.C (4*(WPFiniteNC122.q p-descendedC p)/15 : K)*T (-(p : ℤ))

noncomputable def descendedP (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  originalK0 p*(WPFiniteWSource.W p : K[X]).toLaurent+
    originalJlog p+descendedInvisibleP p

theorem originalP_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) : WPFiniteZSource.P p u=descendedP p := by
  rw [originalP_decomposition]
  simp only [originalInvisibleP,WPFiniteABSourceTail.uSlot,originalC_descended p hp u hu,
    descendedP,descendedInvisibleP]

theorem descendedP_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] : coefficientMap f (descendedP p)=descendedP p := by
  simp only [descendedP,descendedInvisibleP,originalJlog,map_add,map_mul,map_sub,
    coefficientMap_C,coefficientMap_T,coefficientMap_toLaurent,originalK0_transport,
    W_transport,scaledLog_transport,map_neg,map_div₀,map_mul,map_add,map_sub,
    map_ofNat,map_one,map_intCast,WPFiniteNC122.q,descendedC_transport]

noncomputable def descendedPositiveNumerator (p : ℕ) [Fact p.Prime] [CharP K p] :
    K[T;T⁻¹] :=
  2*poleProductOverX*invert (descendedP p)-
    2*twiceGammaNumerator*(descendedP p+invert (descendedP p))

theorem descendedPositiveNumerator_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] :
    coefficientMap f (descendedPositiveNumerator p)=descendedPositiveNumerator p := by
  simp only [descendedPositiveNumerator,poleProductOverX,twiceGammaNumerator,
    map_sub,map_mul,map_add,map_ofNat,coefficientMap_C,coefficientMap_T,
    coefficientMap_invert,descendedP_transport,map_div₀,map_one,map_ofNat]

/-- The original positive source is proved over the original field without a root hypothesis. -/
theorem descendedUcan_positive_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    4*poleProduct*D (descendedUcan p : K[T;T⁻¹])=descendedPositiveNumerator p-
      4*LaurentPolynomial.C (originalAlpha p)*poleProduct*originalFrobeniusSource p := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  have h := originalUcan_positive_source (K:=AlgebraicClosure K) p hp u hu
  rw [originalUcan_descended p hp u hu] at h
  simp only [fourPositiveSourceNumerator,originalP_descended p hp u hu] at h
  change 4*poleProduct*D (descendedUcan p)=descendedPositiveNumerator p-
    4*LaurentPolynomial.C (originalAlpha p)*poleProduct*originalFrobeniusSource p at h
  apply coefficientMap_injective_field f
  simpa only [map_mul,map_sub,map_ofNat,coefficientMap_derivative,
    descendedUcan_transport,descendedPositiveNumerator_transport,poleProduct,
    originalAlpha,originalFrobeniusSource,coefficientMap_C,coefficientMap_T,
    map_add,map_mul,map_sub,map_neg,map_div₀,map_ofNat,map_one,map_intCast,
    WPFiniteNC122.q] using h

theorem descendedPositiveQuotient_exists (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : ∃ B : K[T;T⁻¹], 4*poleProduct*B=descendedPositiveNumerator p := by
  refine ⟨D (descendedUcan p)+LaurentPolynomial.C (originalAlpha p)*
    originalFrobeniusSource p,?_⟩
  linear_combination descendedUcan_positive_source (K:=K) p hp

noncomputable def descendedBgamma (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : K[T;T⁻¹] := Classical.choose (descendedPositiveQuotient_exists p hp)

theorem descendedBgamma_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    4*poleProduct*(descendedBgamma p hp : K[T;T⁻¹])=descendedPositiveNumerator p :=
  Classical.choose_spec (descendedPositiveQuotient_exists p hp)

theorem descendedBgamma_unique (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (B : K[T;T⁻¹]) (hB : 4*poleProduct*B=descendedPositiveNumerator p) :
    B=descendedBgamma p hp := by
  apply mul_left_cancel₀ (fourPoleProduct_nonzero p hp)
  rw [hB,descendedBgamma_source]

/-- The unique quotient transports with its independently specified numerator. -/
theorem descendedBgamma_transport (f : K →+* L) (p : ℕ) [Fact p.Prime]
    [CharP K p] [CharP L p] (hp : 19≤p) :
    coefficientMap f (descendedBgamma p hp)=descendedBgamma p hp := by
  apply descendedBgamma_unique p hp
  have h := congrArg (coefficientMap f) (descendedBgamma_source (K:=K) p hp)
  simpa only [map_mul,map_ofNat,poleProduct,map_add,map_sub,
    coefficientMap_C,coefficientMap_T,map_div₀,map_one,map_ofNat,
    descendedPositiveNumerator_transport] using h

/-- The original quotient in either branch is exactly the descended quotient. -/
theorem originalBgamma_descended (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) : originalBgamma p hp u hu=descendedBgamma p hp := by
  apply descendedBgamma_unique p hp
  rw [originalBgamma_source]
  simp only [fourPositiveSourceNumerator,originalP_descended p hp u hu,
    descendedPositiveNumerator]

/-- The full original U uses the descended quotient; no derivative premise is added. -/
theorem descendedU_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    D (descendedU p : K[T;T⁻¹])=descendedBgamma p hp-
      LaurentPolynomial.C (originalAlpha p)*originalFrobeniusSource p := by
  rw [descendedU,map_sub,D_C,sub_zero]
  apply mul_left_cancel₀ (fourPoleProduct_nonzero p hp)
  rw [mul_sub,descendedBgamma_source,descendedUcan_positive_source p hp]
  ring

/-- The same full branch constant gives the original endpoint over the prime field. -/
theorem descendedU_branch_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (descendedU p)=0 := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  have h := WPFieldAssembly.SourceClosureUVEndpoint.originalU_branch_zero p hp u hu
  rw [originalU_descended p hp u hu] at h
  apply f.injective
  rw [branch_eval_transport,descendedU_transport,map_zero]
  exact h

/-- The three canonical holes belong to the same original-field Ucan. -/
theorem descendedUcan_holes (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (descendedUcan p : K[T;T⁻¹]).coeff 0=0 ∧
      (descendedUcan p : K[T;T⁻¹]).coeff (p : ℤ)=0 ∧
      (descendedUcan p : K[T;T⁻¹]).coeff (-(p : ℤ))=0 := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  have h := WPFieldAssembly.SourceClosureUVCanonicalHoles.originalUcan_holes p hp u
  rw [originalUcan_descended p hp u hu] at h
  have hzero (j : ℤ) (hj : (descendedUcan p : (AlgebraicClosure K)[T;T⁻¹]).coeff j=0) :
      (descendedUcan p : K[T;T⁻¹]).coeff j=0 := by
    apply f.injective
    rw [←coefficientMap_coeff,descendedUcan_transport,map_zero]
    exact hj
  exact ⟨hzero 0 h.1,hzero p h.2.1,hzero (-p) h.2.2⟩

/-- The original branch subtraction changes the zeroth slot and preserves both p holes. -/
theorem descendedU_pivots (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (descendedU p : K[T;T⁻¹]).coeff 0=-(descendedU0 p : K) ∧
      (descendedU p : K[T;T⁻¹]).coeff (p : ℤ)=0 ∧
      (descendedU p : K[T;T⁻¹]).coeff (-(p : ℤ))=0 := by
  have h := descendedUcan_holes (K:=K) p hp
  have hp0 : (0 : ℤ)≠(p : ℤ) := by omega
  have hmp0 : (0 : ℤ)≠-(p : ℤ) := by omega
  constructor
  · rw [descendedU,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
      h.1,original_coeff_C,if_pos rfl,zero_sub]
  · constructor
    · rw [descendedU,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
        h.2.1,original_coeff_C,if_neg hp0,sub_zero]
    · rw [descendedU,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
        h.2.2,original_coeff_C,if_neg hmp0,sub_zero]

end WPFieldAssembly.SourceClosureUVFieldTransport
