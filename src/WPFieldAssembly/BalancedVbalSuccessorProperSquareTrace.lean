import WPFieldAssembly.SourceClosureVbalProperSquareEndpoints
import WPFieldAssembly.BalancedVbalSuccessorProperSquareBase
import WPFieldAssembly.SourceClosureUVWeightedBands

open scoped Polynomial LaurentPolynomial BigOperators
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedBands
  WPFieldAssembly.ActualBpairContraction
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.SourceClosureVbalProperSquareEndpoints

namespace WPFieldAssembly.BalancedVbalSuccessorProperSquareTrace

/- The numerator below is printed as the literal original three-term square
expression. Unfolding SourceClosureSigmaNativeKernel.actualProperSquaresNumerator
gives this expression by reflexivity; importing that unrelated Sigma collector
is unnecessary. The phase and endpoint identities are retained from IR59;
the phase algebra below is factored into abstract carrier certificates.
The exact square definitions and their conic/phase proofs are in the narrower
ProperSquareBase; UVWeightedBands' remaining literal stage stays explicit. -/

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- The original signed phases retain the reflected constant slot. -/
noncomputable def properSquaresPhase (P : (ZMod p)[X]) : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (1/2250 : ZMod p)*
    ((LaurentPolynomial.C (-24)*T (2*(p : ℤ)-(((p-1)/2 : ℕ) : ℤ))*P.toLaurent+
      LaurentPolynomial.C 94*T ((p : ℤ)-(((p-1)/2 : ℕ) : ℤ))*P.toLaurent+
      LaurentPolynomial.C 26*T (-(((p-1)/2 : ℕ) : ℤ))*P.toLaurent+
      LaurentPolynomial.C (-76)*T (-(p : ℤ)-(((p-1)/2 : ℕ) : ℤ))*P.toLaurent+
      LaurentPolynomial.C 16*T (-2*(p : ℤ)-(((p-1)/2 : ℕ) : ℤ))*P.toLaurent)+
      (LaurentPolynomial.C 44*T (p : ℤ)*invert P.toLaurent+
        LaurentPolynomial.C (-159)*T 0*invert P.toLaurent+
        LaurentPolynomial.C (-91)*T (-(p : ℤ))*invert P.toLaurent+
        LaurentPolynomial.C 96*T (-2*(p : ℤ))*invert P.toLaurent+
        LaurentPolynomial.C (-16)*T (-3*(p : ℤ))*invert P.toLaurent))

private theorem squaredCoordinate_frobenius :
    (WPFiniteWSource.squaredCoordinate : (ZMod p)[X])^p=
      Polynomial.C (1/5 : ZMod p)*(X^p+1) := by
  have h5 : (5 : ZMod p)^p=5 := ZMod.pow_card (5 : ZMod p)
  rw [WPFiniteWSource.squaredCoordinate,mul_pow,←map_pow,inv_pow,h5,
    add_pow_char,one_pow,one_div]

/- Keep ring certificates abstract in their carriers. Applying these separate
declarations does not substitute the dependent native norm into a ring
normalizer's entire proof term. Both inverse phases and all ten slots remain. -/
private theorem square_phase_plus {R : Type*} [CommRing R]
    (U V : R) (hUV : U*V=1) :
    (17-4*U-4*V)*(U+1)*(6-4*V)=
      -24*U^2+94*U+26-76*V+16*V^2 := by
  linear_combination (16*U+16*V-76)*hUV

private theorem square_phase_minus {R : Type*} [CommRing R]
    (U V : R) (hUV : U*V=1) :
    (17-4*U-4*V)*(V+1)*(4*V-11)=
      44*U-159-91*V+96*V^2-16*V^3 := by
  linear_combination (-16*V+28)*hUV

private theorem square_phase_unit_solve {R : Type*} [CommRing R]
    (a b H W : R) (hu : a*b=1) (hH : a*H=W) : H=b*W := by
  calc
    H=(a*b)*H := by rw [hu,one_mul]
    _=b*(a*H) := by ring
    _=b*W := by rw [hH]

private theorem square_phase_rearrange {R : Type*} [CommRing R]
    (a b c d k S St U V F G : R)
    (hc : a*b*c*d=k) (hc' : a*b*d*d*d=k) (ht : S*St=1) :
    a*S*(b*(17-4*U-4*V)*c*(d*(U+1)*F)*(6-4*V)+
      St*(b*(17-4*U-4*V)*d*(d*(V+1)*G)*(d*(4*V-11))))=
      k*(S*((17-4*U-4*V)*(U+1)*(6-4*V))*F+
        ((17-4*U-4*V)*(V+1)*(4*V-11))*G) := by
  linear_combination
    S*((17-4*U-4*V)*(U+1)*(6-4*V))*F*hc+
    ((17-4*U-4*V)*(V+1)*(4*V-11))*G*hc'+
    ((17-4*U-4*V)*(V+1)*(4*V-11))*G*a*b*d^3*ht

private theorem proper_squares_scalar_normalization {K : Type*} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h5 : (5 : K)≠0) :
    (1/6 : K)*(1/3)*(1/25)*(1/5)=1/2250 ∧
      (1/6 : K)*(1/3)*(1/5)*(1/5)*(1/5)=1/2250 := by
  have h6 : (6 : K)≠0 := by
    rw [show (6 : K)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h2250 : (2250 : K)≠0 := by
    rw [show (2250 : K)=2*3^2*5^3 by ring]
    exact mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) (pow_ne_zero _ h5)
  constructor
  · field_simp [h6,h3,h25,h5,h2250]
    ring
  · field_simp [h6,h3,h5,h2250]
    ring

private theorem proper_squares_laurent_rearrange {K : Type*} [Field K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h5 : (5 : K)≠0)
    (r n : ℤ) (F G : K[T;T⁻¹]) :
    LaurentPolynomial.C (1/6 : K)*T (-n)*
      (LaurentPolynomial.C (1/3 : K)*(17-4*T r-4*T (-r))*
          LaurentPolynomial.C (1/25 : K)*
          (LaurentPolynomial.C (1/5 : K)*(T r+1)*F)*(6-4*T (-r))+
        T n*(LaurentPolynomial.C (1/3 : K)*(17-4*T r-4*T (-r))*
          LaurentPolynomial.C (1/5 : K)*
          (LaurentPolynomial.C (1/5 : K)*(T (-r)+1)*G)*
          (LaurentPolynomial.C (1/5 : K)*(4*T (-r)-11))))=
      LaurentPolynomial.C (1/2250 : K)*
        (T (-n)*((17-4*T r-4*T (-r))*(T r+1)*(6-4*T (-r)))*F+
          ((17-4*T r-4*T (-r))*(T (-r)+1)*(4*T (-r)-11))*G) := by
  obtain ⟨hc,hc'⟩ := proper_squares_scalar_normalization h2 h3 h5
  have hCc := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hc
  have hCc' := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hc'
  simp only [map_mul] at hCc hCc'
  have ht : (T (-n)*T n : K[T;T⁻¹])=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  exact square_phase_rearrange
    (LaurentPolynomial.C (1/6 : K)) (LaurentPolynomial.C (1/3 : K))
    (LaurentPolynomial.C (1/25 : K)) (LaurentPolynomial.C (1/5 : K))
    (LaurentPolynomial.C (1/2250 : K)) (T (-n)) (T n)
    (T r) (T (-r)) F G hCc hCc' ht

private theorem proper_squares_laurent_expand {K : Type*} [CommRing K]
    (k : K[T;T⁻¹]) (r n : ℤ) (F G : K[T;T⁻¹]) :
    k*(T (-n)*((17-4*T r-4*T (-r))*(T r+1)*(6-4*T (-r)))*F+
      ((17-4*T r-4*T (-r))*(T (-r)+1)*(4*T (-r)-11))*G)=
      k*((LaurentPolynomial.C (-24)*T (2*r-n)*F+
        LaurentPolynomial.C 94*T (r-n)*F+
        LaurentPolynomial.C 26*T (-n)*F+
        LaurentPolynomial.C (-76)*T (-r-n)*F+
        LaurentPolynomial.C 16*T (-2*r-n)*F)+
        (LaurentPolynomial.C 44*T r*G+
          LaurentPolynomial.C (-159)*T 0*G+
          LaurentPolynomial.C (-91)*T (-r)*G+
          LaurentPolynomial.C 96*T (-2*r)*G+
          LaurentPolynomial.C (-16)*T (-3*r)*G)) := by
  have hUV : (T r*T (-r) : K[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hU2 : (T r : K[T;T⁻¹])^2=T (2*r) := by
    rw [T_pow]
    congr 1
  have hV2 : (T (-r) : K[T;T⁻¹])^2=T (-2*r) := by
    rw [T_pow]
    congr 1
    ring
  have hV3 : (T (-r) : K[T;T⁻¹])^3=T (-3*r) := by
    rw [T_pow]
    congr 1
    ring
  rw [square_phase_plus (T r) (T (-r)) hUV,
    square_phase_minus (T r) (T (-r)) hUV,hU2,hV2,hV3]
  have hshift (j : ℤ) : (T (-n)*T j : K[T;T⁻¹])=T (j-n) := by
    rw [←T_add]
    congr 1
    ring
  simp only [map_neg,map_ofNat,T_zero]
  linear_combination k*F*
    (-24*hshift (2*r)+94*hshift r-76*hshift (-r)+16*hshift (-2*r))

private theorem proper_squares_phase_formula (P : (ZMod p)[X]) :
    LaurentPolynomial.C (1/2250 : ZMod p)*
      (T (-(((p-1)/2 : ℕ) : ℤ))*
          ((17-4*T (p : ℤ)-4*T (-(p : ℤ)))*(T (p : ℤ)+1)*
            (6-4*T (-(p : ℤ))))*P.toLaurent+
        ((17-4*T (p : ℤ)-4*T (-(p : ℤ)))*(T (-(p : ℤ))+1)*
          (4*T (-(p : ℤ))-11))*invert P.toLaurent)=properSquaresPhase p P := by
  exact proper_squares_laurent_expand (LaurentPolynomial.C (1/2250 : ZMod p))
    (p : ℤ) (((p-1)/2 : ℕ) : ℤ) P.toLaurent (invert P.toLaurent)

private theorem actual_proper_square_carrier_phase :
    (actualProperSquareCarrier p).toLaurent=
      LaurentPolynomial.C (1/5 : ZMod p)*(T (p : ℤ)+1)*
        (actualProperSquarePullback p).toLaurent := by
  have hs := congrArg (fun Q : (ZMod p)[X] => Q.toLaurent)
    (squaredCoordinate_frobenius p)
  simp only [map_pow,map_mul,map_add,map_one,Polynomial.toLaurent_C,
    Polynomial.toLaurent_X,T_pow,mul_one] at hs
  rw [actualProperSquareCarrier,map_mul,map_pow,hs]

private theorem actual_proper_square_reflected_high_phase (hp : 19≤p) :
    invert (actualProperHighPhase p).toLaurent=
      LaurentPolynomial.C (1/5 : ZMod p)*(4*T (-(p : ℤ))-11) := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h5C : (5 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/5 : ZMod p)=1 := by
    change LaurentPolynomial.C (5 : ZMod p)*LaurentPolynomial.C (1/5 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h5,map_one]
  have hhighi := congrArg invert (actual_proper_high_phase_frobenius p hp)
  simp only [map_mul,map_ofNat,map_sub,invert_T] at hhighi
  exact square_phase_unit_solve 5 (LaurentPolynomial.C (1/5 : ZMod p))
    (invert (actualProperHighPhase p).toLaurent) (4*T (-(p : ℤ))-11) h5C hhighi

private theorem actual_proper_square_reflected_local_phase (hp : 19≤p) :
    invert (actualProperSquareLocal p)=
      LaurentPolynomial.C (1/3 : ZMod p)*WPFiniteZSource.phase p*
        LaurentPolynomial.C (1/5 : ZMod p)*
        (LaurentPolynomial.C (1/5 : ZMod p)*(T (-(p : ℤ))+1)*
          invert (actualProperSquarePullback p).toLaurent)*
        (LaurentPolynomial.C (1/5 : ZMod p)*(4*T (-(p : ℤ))-11)) := by
  have hci := congrArg invert (actual_proper_square_carrier_phase p)
  simp only [map_mul,map_add,map_one,invert_C,invert_T] at hci
  simp only [actualProperSquareLocal,map_mul,invert_C]
  rw [native_zeta_reflection p hp,native_zeta_phase p hp,hci,
    actual_proper_square_reflected_high_phase p hp]

/-- The joint square is attached before applying the original p-hole trace. -/
theorem actual_proper_squares_phase (hp : 19≤p) :
    LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
      (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))=properSquaresPhase p (actualProperSquarePullback p) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  rw [actual_proper_square_phase_cancellation p hp,
    actual_proper_square_reflected_local_phase p hp,
    actual_proper_square_carrier_phase p,native_zeta_phase p hp]
  simp only [WPFiniteZSource.phase]
  exact (proper_squares_laurent_rearrange h2 h3 h5
    (p : ℤ) (((p-1)/2 : ℕ) : ℤ) (actualProperSquarePullback p).toLaurent
    (invert (actualProperSquarePullback p).toLaurent)).trans
      (proper_squares_phase_formula p (actualProperSquarePullback p))

private theorem actual_proper_square_pullback_degree (hp : 19≤p) :
    (actualProperSquarePullback p).natDegree≤3*(p/6)-3 := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have hq : (5*X^2-1 : (ZMod p)[X]).natDegree=2 := by
    compute_degree
    exact h5
  have ht : (4*X^3-3*X : (ZMod p)[X]).natDegree=3 := by
    compute_degree
    · exact h4
    · norm_num
  have hn := WPActualRankTwoProper.properLegendreJacobi_degree p (by omega)
  have he := congrArg Polynomial.natDegree (actual_proper_square_pullback_conic p hp)
  rw [natDegree_comp,hq,natDegree_comp,ht,natDegree_pow] at he
  omega

/-- The proper native norm has degree strictly below the half window and its two actual ends. -/
theorem actual_proper_squares_low_facts (hp : 19≤p) :
    (actualProperSquarePullback p).natDegree<(p-1)/2 ∧
      (actualProperSquarePullback p).eval (1/4)=
        WPActualGaussBottom.fieldHarmonic p (p/6)^2 ∧
      (actualProperSquarePullback p).eval 4=
        WPActualGaussBottom.fieldHarmonic p (p/6)^2 := by
  have hd := actual_proper_square_pullback_degree p hp
  have h6 := Nat.div_mul_le_self p 6
  have hhalf := WPFiniteWSource.half_exponent p hp
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1/4)=0 := by
    simp [WPHasseIntegralTransport.fieldV,one_div,h4]
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4=0 := by
    simp [WPHasseIntegralTransport.fieldV]
  refine ⟨by omega,?_,?_⟩
  all_goals rw [actualProperSquarePullback,eval_comp]
  · rw [hVa,←coeff_zero_eq_eval_zero,actual_proper_square_native_origin p hp]
  · rw [hVb,←coeff_zero_eq_eval_zero,actual_proper_square_native_origin p hp]

/-- Both strict endpoint windows use the actual norm; the reflected zero slot is excluded. -/
theorem actual_proper_squares_endpoint_windows (hp : 19≤p) :
    let J := LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
      (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
    endpointTrace (1/4 : ZMod p) 4 J=
      -41*WPActualGaussBottom.fieldHarmonic p (p/6)^2/250 ∧
    endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*J)=
      11*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125 := by
  let N := (p-1)/2
  let P := actualProperSquarePullback p
  let h : ZMod p := WPActualGaussBottom.fieldHarmonic p (p/6)
  obtain ⟨hD,ha,hb⟩ := actual_proper_squares_low_facts p hp
  change P.natDegree<N at hD
  change P.eval (1/4)=h^2 at ha
  change P.eval 4=h^2 at hb
  have hhalf : p=2*N+1 := WPFiniteWSource.half_exponent p hp
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4^2 by ring]
    exact pow_ne_zero _ h4
  have h125 : (125 : ZMod p)≠0 := by
    rw [show (125 : ZMod p)=5^3 by ring]
    exact pow_ne_zero _ h5
  have h250 : (250 : ZMod p)≠0 := by
    rw [show (250 : ZMod p)=2*125 by ring]
    exact mul_ne_zero h2 h125
  have h2250 : (2250 : ZMod p)≠0 := by
    rw [show (2250 : ZMod p)=2*3^2*5^3 by ring]
    exact mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) (pow_ne_zero _ h5)
  have h4N : (4 : ZMod p)^N=1 := WPFiniteWSource.four_half_power p hp
  have haN : (1/4 : ZMod p)^N=1 := by rw [div_pow,one_pow,h4N,div_one]
  have h4pn : (4 : ZMod p)^(p-N)=4 := by
    rw [pow_sub₀ (4 : ZMod p) h4 (by omega),ZMod.pow_card,h4N,inv_one,mul_one]
  have hapn : (1/4 : ZMod p)^(p-N)=1/4 := by
    rw [pow_sub₀ (1/4 : ZMod p) (one_div_ne_zero h4) (by omega),ZMod.pow_card,haN,
      inv_one,mul_one]
  have h4pn2 : (4 : ZMod p)^(2*p-N)=16 := by
    rw [pow_sub₀ (4 : ZMod p) h4 (by omega),show 2*p=p*2 by omega,
      pow_mul,ZMod.pow_card,h4N,inv_one,mul_one]
    ring
  have hapn2 : (1/4 : ZMod p)^(2*p-N)=1/16 := by
    rw [pow_sub₀ (1/4 : ZMod p) (one_div_ne_zero h4) (by omega),show 2*p=p*2 by omega,
      pow_mul,ZMod.pow_card,haN,inv_one,mul_one,div_pow,one_pow,
      show (4 : ZMod p)^2=16 by ring]
  have he1 : endpointTrace (1/4 : ZMod p) 4
      (T ((p : ℤ)-(N : ℤ))*P.toLaurent)=-33*h^2/4 := by
    have he := endpoint_positive_polynomial (1/4 : ZMod p) 4 P (p-N) (by omega)
    rw [show ((p-N : ℕ) : ℤ)=(p : ℤ)-(N : ℤ) by omega,h4pn,hapn,ha,hb] at he
    rw [he]
    field_simp [h4]
    ring
  have he2 : endpointTrace (1/4 : ZMod p) 4
      (T (2*(p : ℤ)-(N : ℤ))*P.toLaurent)=-513*h^2/16 := by
    have he := endpoint_positive_polynomial (1/4 : ZMod p) 4 P (2*p-N) (by omega)
    rw [show ((2*p-N : ℕ) : ℤ)=2*(p : ℤ)-(N : ℤ) by omega,h4pn2,hapn2,ha,hb] at he
    rw [he]
    field_simp [h16]
    ring
  have hei : endpointTrace (1/4 : ZMod p) 4 (T (p : ℤ)*invert P.toLaurent)=
      -33*h^2/4 := by
    have he := endpoint_positive_inverse (1/4 : ZMod p) 4 (one_div_ne_zero h4) h4
      P p (by omega)
    have hainv : P.eval (4 : ZMod p)⁻¹=h^2 := by simpa only [one_div] using ha
    have hbinv : P.eval (1/4 : ZMod p)⁻¹=h^2 := by simpa only [one_div,inv_inv] using hb
    rw [ZMod.pow_card,ZMod.pow_card,hainv,hbinv] at he
    rw [he]
    field_simp [h4]
    ring
  have hreg (s : ℤ) (hs : s+(P.natDegree : ℤ)≤0) :
      endpointTrace (1/4 : ZMod p) 4 (T s*P.toLaurent)=0 :=
    endpoint_shift_regular_zero _ _ P s hs
  have hinv (s : ℤ) (hs : s≤0) :
      endpointTrace (1/4 : ZMod p) 4 (T s*invert P.toLaurent)=0 :=
    endpoint_shift_inverse_zero _ _ P s hs
  dsimp only
  rw [actual_proper_squares_phase p hp]
  change endpointTrace (1/4 : ZMod p) 4 (properSquaresPhase p P)=-41*h^2/250 ∧
    endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*properSquaresPhase p P)=11*h^2/125
  constructor
  · simp only [properSquaresPhase,mul_assoc,map_add,endpointTrace_C_mul]
    rw [he2,he1,hreg (-(N : ℤ)) (by omega),hreg (-(p : ℤ)-(N : ℤ)) (by omega),
      hreg (-2*(p : ℤ)-(N : ℤ)) (by omega),hei,
      hinv 0 (by omega),hinv (-(p : ℤ)) (by omega),
      hinv (-2*(p : ℤ)) (by omega),hinv (-3*(p : ℤ)) (by omega)]
    field_simp [h4,h16,h250,h2250]
    ring
  · simp only [properSquaresPhase,endpoint_shift_constant,mul_add,map_add,endpoint_shift_term]
    rw [show -(p : ℤ)+(2*(p : ℤ)-(N : ℤ))=(p : ℤ)-(N : ℤ) by ring,
      show -(p : ℤ)+((p : ℤ)-(N : ℤ))= -(N : ℤ) by ring,neg_add_cancel,he1]
    rw [hreg (-(N : ℤ)) (by omega),hreg (-(p : ℤ)+ -(N : ℤ)) (by omega),
      hreg (-(p : ℤ)+(-(p : ℤ)-(N : ℤ))) (by omega),
      hreg (-(p : ℤ)+(-2*(p : ℤ)-(N : ℤ))) (by omega),
      hinv 0 (by omega),hinv (-(p : ℤ)+0) (by omega),
      hinv (-(p : ℤ)+ -(p : ℤ)) (by omega),
      hinv (-(p : ℤ)+(-2*(p : ℤ))) (by omega),
      hinv (-(p : ℤ)+(-3*(p : ℤ))) (by omega)]
    field_simp [h4,h125,h2250]
    ring

/-- The ten complete phases themselves supply the strict upper support bound.
Every negative coefficient is retained; no lower cutoff is used. -/
theorem actual_proper_squares_support (hp : 19≤p) :
    let J := LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
      (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
    Above J (2*(p : ℤ)-1) := by
  dsimp only
  rw [actual_proper_squares_phase p hp]
  let P := actualProperSquarePullback p
  let N := (p-1)/2
  have hD := (actual_proper_squares_low_facts p hp).1
  change P.natDegree<N at hD
  have hN : p=2*N+1 := WPFiniteWSource.half_exponent p hp
  have hreg (c : ZMod p) (j : ℤ) (hj : j+(P.natDegree : ℤ)≤2*(p : ℤ)-1) :
      Above (LaurentPolynomial.C c*(T j*P.toLaurent)) (2*(p : ℤ)-1) :=
    Above_C_mul (Above_mono
      (Above_shift (Above_toLaurent P P.natDegree le_rfl) j) hj) c
  have hinv (c : ZMod p) (j : ℤ) (hj : j≤2*(p : ℤ)-1) :
      Above (LaurentPolynomial.C c*(T j*invert P.toLaurent)) (2*(p : ℤ)-1) :=
    Above_C_mul (Above_mono (Above_shift (Above_invert_toLaurent P) j)
      (by omega)) c
  have hadd {F G : (ZMod p)[T;T⁻¹]}
      (hF : Above F (2*(p : ℤ)-1)) (hG : Above G (2*(p : ℤ)-1)) :
      Above (F+G) (2*(p : ℤ)-1) := by
    simpa only [max_self] using Above_add hF hG
  change Above (properSquaresPhase p P) (2*(p : ℤ)-1)
  unfold properSquaresPhase
  simp only [mul_assoc]
  apply Above_C_mul
  exact hadd
    (hadd (hadd (hadd (hadd
      (hreg (-24) (2*(p : ℤ)-(N : ℤ)) (by omega))
      (hreg 94 ((p : ℤ)-(N : ℤ)) (by omega)))
      (hreg 26 (-(N : ℤ)) (by omega)))
      (hreg (-76) (-(p : ℤ)-(N : ℤ)) (by omega)))
      (hreg 16 (-2*(p : ℤ)-(N : ℤ)) (by omega)))
    (hadd (hadd (hadd (hadd
      (hinv 44 (p : ℤ) (by omega)) (hinv (-159) 0 (by omega)))
      (hinv (-91) (-(p : ℤ)) (by omega)))
      (hinv 96 (-2*(p : ℤ)) (by omega)))
      (hinv (-16) (-3*(p : ℤ)) (by omega)))

/-- The reflected p-degree slot is retained as the actual pullback's zero coefficient. -/
theorem actual_proper_squares_p_slot (hp : 19≤p) :
    let J := LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
      (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
    J.coeff (p : ℤ)=(44/2250 : ZMod p)*(actualProperSquarePullback p).coeff 0 := by
  dsimp only
  rw [actual_proper_squares_phase p hp]
  let P := actualProperSquarePullback p
  let N := (p-1)/2
  have hD := (actual_proper_squares_low_facts p hp).1
  change P.natDegree<N at hD
  have hN : p=2*N+1 := WPFiniteWSource.half_exponent p hp
  have hz (j : ℤ) (hj : j<0 ∨ (P.natDegree : ℤ)<j) : P.toLaurent.coeff j=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside P j hj
  have hzero : P.toLaurent.coeff (0 : ℤ)=P.coeff (0 : ℕ) := by
    simpa only [Nat.cast_zero] using WPFiniteJCarrier.toLaurent_coeff_nat P 0
  change (properSquaresPhase p P).coeff (p : ℤ)=(44/2250 : ZMod p)*P.coeff 0
  simp only [properSquaresPhase,GreenLaurentOperators.C_mul_coeff,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    WPFiniteJCarrier.shifted_coeff,invert_apply,sub_self,sub_zero,neg_zero]
  rw [hz ((p : ℤ)-(2*(p : ℤ)-(N : ℤ))) (Or.inl (by omega)),
    hz ((p : ℤ)-((p : ℤ)-(N : ℤ))) (Or.inr (by omega)),
    hz ((p : ℤ)- -(N : ℤ)) (Or.inr (by omega)),
    hz ((p : ℤ)-(-(p : ℤ)-(N : ℤ))) (Or.inr (by omega)),
    hz ((p : ℤ)-(-2*(p : ℤ)-(N : ℤ))) (Or.inr (by omega)),
    hz (-(p : ℤ)) (Or.inl (by omega)),
    hz (-((p : ℤ)- -(p : ℤ))) (Or.inl (by omega)),
    hz (-((p : ℤ)-(-2*(p : ℤ)))) (Or.inl (by omega)),
    hz (-((p : ℤ)-(-3*(p : ℤ)))) (Or.inl (by omega))]
  rw [hzero]
  ring

/-- The third positive window is zero by full support, including the p-degree slot. -/
theorem actual_proper_squares_third_window (hp : 19≤p) :
    let J := LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
      (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
    endpointTrace (1/4 : ZMod p) 4 (T (-2*(p : ℤ))*J)=0 := by
  dsimp only
  apply endpoint_of_nonpositive
  exact Above_mono (Above_shift (actual_proper_squares_support p hp) (-2*(p : ℤ)))
    (by omega)

/-- IR59 is the joint proper-square contribution under the unchanged original weight. -/
theorem actual_proper_squares_original_weight (hp : 19≤p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p
      (LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
        (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p)))=
      8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125 := by
  let J : (ZMod p)[T;T⁻¹] := LaurentPolynomial.C (1/6 : ZMod p)*
    T (-(((p-1)/2 : ℕ) : ℤ))*(3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
  have hJ : Above J (2*(p : ℤ)-1) := actual_proper_squares_support p hp
  obtain ⟨ha,hb⟩ := actual_proper_squares_endpoint_windows p hp
  change endpointTrace (1/4 : ZMod p) 4 J=_ at ha
  change endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*J)=_ at hb
  change (2/3 : ZMod p)*originalWeightedFieldTrace p J=_
  rw [show originalWeightedFieldTrace p J=
    -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 J-
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*J) from
        original_weight_above p hp J hJ,ha,hb]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h125 : (125 : ZMod p)≠0 := by
    rw [show (125 : ZMod p)=5^3 by ring]
    exact pow_ne_zero _ h5
  have h250 : (250 : ZMod p)≠0 := by
    rw [show (250 : ZMod p)=2*125 by ring]
    exact mul_ne_zero h2 h125
  change (2/3 : ZMod p)*(-(3 : ZMod p)*(-41*WPActualGaussBottom.fieldHarmonic p (p/6)^2/250)-
    (9/2 : ZMod p)*(11*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125))=_
  field_simp [h2,h3,h125,h250]
  ring

theorem actual_proper_squares_density_trace (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
      ((3*(WPFieldAssembly.ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹])^p*
          (3*T (-1)*(4-11*T 1))*
          T (-(((p-1)/2 : ℕ) : ℤ)))*
        (LaurentPolynomial.C (1/6 : ZMod p)*(3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))))=
      8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125 := by
  have hinput : ((3*(WPFieldAssembly.ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹])^p*
      (3*T (-1)*(4-11*T 1))*
      T (-(((p-1)/2 : ℕ) : ℤ)))*
        (LaurentPolynomial.C (1/6 : ZMod p)*(3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))))=
      3*(WPFieldAssembly.ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹])^p*
        (3*T (-1)*(4-11*T 1))*
        (LaurentPolynomial.C (1/6 : ZMod p)*T (-(((p-1)/2 : ℕ) : ℤ))*
          (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))) := by
    ring
  rw [hinput]
  exact actual_proper_squares_original_weight p hp

end WPFieldAssembly.BalancedVbalSuccessorProperSquareTrace
