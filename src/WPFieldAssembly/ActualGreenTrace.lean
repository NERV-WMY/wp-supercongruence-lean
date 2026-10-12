import WPFieldAssembly.ActualBalancedGreenTransfer
import WPFieldAssembly.GreenLaurentOperators

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualGreenPrimitive

namespace WPFieldAssembly.ActualBalancedGreenTransfer

/-- The reciprocal Pearson polynomial retains both conic poles. -/
theorem actualAbarQ_invert :
    invert (WPFiniteZSource.Abar : ℚ[X]).toLaurent =
      T (-2) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent := by
  have hA : (WPFiniteZSource.Abar : ℚ[X]).toLaurent =
      17*T 1-4*T 2-4 := by
    simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one]
    rw [show (T 2 : ℚ[T;T⁻¹]) = T 1*T 1 by rw [←T_add]; norm_num]
    ring
  have h20 : (T (-2)*T 2 : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have h21 : (T (-2)*T 1 : ℚ[T;T⁻¹])=T (-1) := by rw [←T_add]; norm_num
  rw [hA]
  simp only [map_sub,map_mul,map_ofNat,invert_T]
  linear_combination 4*h20-17*h21

theorem greenCoordinateQ_invert (p : ℕ) :
    invert (greenCoordinateQ p).toLaurent =
      T (-1)*(greenCoordinateQ p).toLaurent := by
  have hu : (T (-1)*T 1 : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  simp only [greenCoordinateQ,map_mul,map_add,Polynomial.toLaurent_C,
    Polynomial.toLaurent_X,map_one,invert_C,invert_T]
  linear_combination -LaurentPolynomial.C (1/5 : ℚ)*hu

/-- Characteristic-zero inversion keeps the literal p times CM term. -/
theorem actual_inverted_CM_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    10*(greenCoordinateQ p).toLaurent*(WPFiniteZSource.Abar : ℚ[X]).toLaurent*
        D (invert (greenCMq p hp).toLaurent) =
      -15*(greenCoordinateQ p).toLaurent^(((p-1)/2)+1)*
        T (-(((p-1)/2 : ℕ) : ℤ))*greenSourceAtQ p hp -
      LaurentPolynomial.C (p : ℚ)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent*
        T (-1)*invert (greenCMq p hp).toLaurent := by
  let N := (p-1)/2
  let s := (greenCoordinateQ p).toLaurent
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let CM := invert (greenCMq p hp).toLaurent
  let der := invert (greenCMq p hp).derivative.toLaurent
  let SQ := greenSourceAtQ p hp
  have h20 : (T 2*T (-2) : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have h12 : (T 1*T (-2) : ℚ[T;T⁻¹])=T (-1) := by rw [←T_add]; norm_num
  have hunit : (T 1*T (-1) : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have hd : der = -T 2*D CM := by
    have he := D_invert (greenCMq p hp).toLaurent
    rw [D_toLaurent] at he
    change D CM = -(T (-2)*der) at he
    calc
      der = (T 2*T (-2))*der := by rw [h20,one_mul]
      _ = -T 2*(-(T (-2)*der)) := by ring
      _ = -T 2*D CM := by rw [he]
  have hm := congrArg (fun P : ℚ[X] => invert P.toLaurent)
    (actual_green_CM_compact_source p hp)
  simp only [map_mul,map_add,map_pow,map_ofNat,Polynomial.toLaurent_C,
    invert_C] at hm
  change 10*invert s*invert A*der =
    15*(invert s)^(N+1)*SQ+LaurentPolynomial.C (p : ℚ)*invert A*CM at hm
  rw [greenCoordinateQ_invert,actualAbarQ_invert,hd,mul_pow] at hm
  have hpow : (T (-1) : ℚ[T;T⁻¹])^(N+1)=T (-((N+1 : ℕ) : ℤ)) := by
    rw [T_pow]
    congr 1
    omega
  rw [hpow] at hm
  have hpw : (T 1*T (-((N+1 : ℕ) : ℤ)) : ℚ[T;T⁻¹])=T (-(N : ℤ)) := by
    rw [←T_add]
    congr 1
    omega
  have hu : (T 1*T (-1)*T (-2)*T 2 : ℚ[T;T⁻¹])=1 := by
    rw [hunit,one_mul,←T_add]
    norm_num
  change 10*s*A*D CM = -15*s^(N+1)*T (-(N : ℤ))*SQ-
    LaurentPolynomial.C (p : ℚ)*A*T (-1)*CM
  linear_combination -T 1*hm-10*s*A*D CM*hu-
    15*s^(N+1)*SQ*hpw-LaurentPolynomial.C (p : ℚ)*A*CM*h12

theorem greenMetric_factor_identity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    2*(greenOriginMetricFactor p hp).val =
      (1/5 : ℚ)^(p-1)*(1/25)*(1/5)^(((p-1)/2)+1) := by
  change 2*(integralRationals p).subtype
      (WPActualRankTwoHatLift.smallIntegralInverse p 2 *
        WPActualRankTwoHatLift.smallIntegralInverse p 5 ^ 3 *
        WPActualRankTwoHatLift.smallIntegralInverse p 5 ^ (((p-1)/2)+p-1)) = _
  simp only [map_mul,map_pow,Subring.subtype_apply,Nat.cast_ofNat,
    WPActualRankTwoHatLift.smallIntegralInverse_value p 2 (by omega) (by omega),
    WPActualRankTwoHatLift.smallIntegralInverse_value p 5 (by omega) (by omega)]
  calc
    2*((1/2 : ℚ)*(1/5)^3*(1/5)^(((p-1)/2)+p-1)) =
        (1/5 : ℚ)^3*(1/5)^(((p-1)/2)+p-1) := by ring
    _ = (1/5 : ℚ)^(3+(((p-1)/2)+p-1)) := (pow_add _ _ _).symm
    _ = (1/5 : ℚ)^((p-1)+2+(((p-1)/2)+1)) := by congr 1; omega
    _ = (1/5 : ℚ)^(p-1)*(1/5)^2*(1/5)^(((p-1)/2)+1) := by
      rw [pow_add,pow_add]
    _ = _ := by norm_num

noncomputable def greenPMAtQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ℚ[T;T⁻¹] :=
  invert ((greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent

private theorem metric_inversion_factors :
    invert (T 1+1 : ℚ[T;T⁻¹])=T (-1)*(T 1+1) ∧
    invert (4-11*T 1 : ℚ[T;T⁻¹])=T (-1)*(4*T 1-11) ∧
    invert (4*T 1-11 : ℚ[T;T⁻¹])=T (-1)*(4-11*T 1) ∧
    invert (11*T 2+4*T 1+8 : ℚ[T;T⁻¹])=
      T (-2)*(8*T 2+4*T 1+11) := by
  have hu : (T (-1)*T 1 : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have h20 : (T (-2)*T 2 : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have h21 : (T (-2)*T 1 : ℚ[T;T⁻¹])=T (-1) := by rw [←T_add]; norm_num
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one,invert_T]
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -hu
  · linear_combination -4*hu
  · linear_combination 11*hu
  · linear_combination -8*h20-4*h21

theorem greenInfinityMetricQ_explicit (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    greenInfinityMetricQ p hp = LaurentPolynomial.C (greenOriginMetricFactor p hp).val*
      T (-(((p-1)/2 : ℕ) : ℤ)-3)*(T 1+1)^((p-1)/2)*
        (4*T 1-11)^(p-1)*(4-11*T 1)*(8*T 2+4*T 1+11)*greenPMAtQ p hp := by
  let N := (p-1)/2
  have hnum : ((greenOriginMetricNumerator p hp).map (integralRationals p).subtype).toLaurent =
      (T 1+1)^N*(4-11*T 1)^(p-1)*(4*T 1-11)*
        (11*T 2+4*T 1+8)*((greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent := by
    simp only [greenOriginMetricNumerator,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_add,Polynomial.map_sub,Polynomial.map_ofNat,Polynomial.map_one,
      Polynomial.map_X,Polynomial.map_comp,WPHasseIntegralTransport.integralV_map_rational,
      greenPMq,map_mul,map_pow,map_add,map_sub,map_ofNat,map_one,Polynomial.toLaurent_X,
      LaurentPolynomial.T_pow]
    rfl
  rw [greenInfinityMetricQ,greenOriginMetricQ,hnum]
  simp only [map_neg,map_mul,map_pow,invert_C,invert_T,neg_neg]
  obtain ⟨hX,hd,hc,hq⟩ := metric_inversion_factors
  rw [hX,hd,hc,hq]
  simp only [mul_pow]
  have hpN : (T (-1) : ℚ[T;T⁻¹])^N=T (-(N : ℤ)) := by
    rw [T_pow]; congr 1; omega
  have hpP : (T (-1) : ℚ[T;T⁻¹])^(p-1)=T (-((p-1 : ℕ) : ℤ)) := by
    rw [T_pow]; congr 1; omega
  rw [hpN,hpP]
  have hphase : (T (-2)*T ((p+1 : ℕ) : ℤ)*T (-(N : ℤ))*
      T (-((p-1 : ℕ) : ℤ))*T (-1)*T (-2) : ℚ[T;T⁻¹])=T (-(N : ℤ)-3) := by
    simp only [←T_add]
    congr 1
    omega
  dsimp only [greenPMAtQ]
  linear_combination LaurentPolynomial.C (greenOriginMetricFactor p hp).val*
    (T 1+1)^N*(4*T 1-11)^(p-1)*(4-11*T 1)*(8*T 2+4*T 1+11)*
    invert ((greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent*hphase

theorem greenCM_inverted_scaled (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*invert (greenCMq p hp).toLaurent =
      2*LaurentPolynomial.C (greenOriginMetricFactor p hp).val*
        T (-(((p-1)/2 : ℕ) : ℤ)-2)*(T 1+1)^(((p-1)/2)+1)*
          (4-11*T 1)*greenPMAtQ p hp := by
  let N := (p-1)/2
  have hm0 := congrArg Polynomial.toLaurent (greenCMq_PM_source p hp)
  simp only [map_mul,map_pow,map_sub,map_ofNat,Polynomial.toLaurent_C,
    Polynomial.toLaurent_X] at hm0
  have hm := congrArg invert hm0
  simp only [map_mul,map_pow,invert_C] at hm
  rw [greenCoordinateQ_invert,metric_inversion_factors.2.2.1] at hm
  simp only [greenCoordinateQ,map_mul,map_add,Polynomial.toLaurent_C,
    Polynomial.toLaurent_X,map_one,mul_pow] at hm
  have ht : (T (-1) : ℚ[T;T⁻¹])^(N+1)*T (-1)=T (-(N : ℤ)-2) := by
    rw [T_pow,←T_add]
    congr 1
    omega
  have hc := congrArg (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹])
    (greenMetric_factor_identity p hp)
  simp only [map_mul,map_ofNat] at hc
  rw [(_root_.map_pow (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹])
    (1/5 : ℚ) (N+1))] at hc
  change 2*LaurentPolynomial.C (greenOriginMetricFactor p hp).val =
    LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*LaurentPolynomial.C (1/25 : ℚ)*
      LaurentPolynomial.C (1/5 : ℚ)^(N+1) at hc
  rw [hm]
  dsimp only [greenPMAtQ]
  linear_combination
    LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*LaurentPolynomial.C (1/25 : ℚ)*
      LaurentPolynomial.C (1/5 : ℚ)^(N+1)*(T 1+1)^(N+1)*(4-11*T 1)*
        invert ((greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent*ht-
    T (-(N : ℤ)-2)*(T 1+1)^(N+1)*(4-11*T 1)*
      invert ((greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent*hc

/-- The actual metric and the same CM source agree before division by p. -/
theorem actual_metric_CM_identity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    10*(greenCoordinateQ p).toLaurent*greenInfinityMetricQ p hp =
      LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*
        (40*(greenCoordinateQ p).toLaurent*(4*T 1-11)^(p-1)-T (-1)*(4*T 1-11)^p)*
          invert (greenCMq p hp).toLaurent := by
  let N := (p-1)/2
  let s := (greenCoordinateQ p).toLaurent
  let c : ℚ[T;T⁻¹] := 4*T 1-11
  let d : ℚ[T;T⁻¹] := 4-11*T 1
  let J := greenPMAtQ p hp
  let a := LaurentPolynomial.C (greenOriginMetricFactor p hp).val
  have h5 : (5 : ℚ[T;T⁻¹])*LaurentPolynomial.C (1/5 : ℚ)=1 := by
    rw [show (5 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (5 : ℚ) from
      (_root_.map_natCast (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹]) 5).symm,
      ←map_mul]
    norm_num
  have hs10 : 10*s=2*(T 1+1) := by
    simp only [s,greenCoordinateQ,map_mul,map_add,Polynomial.toLaurent_C,
      Polynomial.toLaurent_X,map_one]
    linear_combination 2*(T 1+1)*h5
  have hs40 : 40*s=8*(T 1+1) := by linear_combination 4*hs10
  have hph : (T (-(N : ℤ)-2) : ℚ[T;T⁻¹])=T 1*T (-(N : ℤ)-3) := by
    rw [←T_add]; congr 1; omega
  have hu : (T 1*T (-1) : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have hquad : (8*T 2+4*T 1+11 : ℚ[T;T⁻¹])=8*T 1*(T 1+1)-c := by
    dsimp only [c]
    rw [show (T 2 : ℚ[T;T⁻¹])=T 1*T 1 by rw [←T_add]; norm_num]
    ring
  have hI := greenInfinityMetricQ_explicit p hp
  have hC := greenCM_inverted_scaled p hp
  change greenInfinityMetricQ p hp=a*T (-(N : ℤ)-3)*(T 1+1)^N*
    c^(p-1)*d*(8*T 2+4*T 1+11)*J at hI
  change LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*invert (greenCMq p hp).toLaurent=
    2*a*T (-(N : ℤ)-2)*(T 1+1)^(N+1)*d*J at hC
  change 10*s*greenInfinityMetricQ p hp =
    LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*
      (40*s*c^(p-1)-T (-1)*c^p)*invert (greenCMq p hp).toLaurent
  rw [show LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*
      (40*s*c^(p-1)-T (-1)*c^p)*invert (greenCMq p hp).toLaurent =
    (40*s*c^(p-1)-T (-1)*c^p)*
      (LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*invert (greenCMq p hp).toLaurent) by ring]
  rw [hI,hC,hs10,hs40,hph,hquad,
    show c^p=c^(p-1)*c by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤p)],pow_succ]
  linear_combination
    2*a*T (-(N : ℤ)-3)*(T 1+1)^N*(T 1+1)*c^(p-1)*d*J*c*hu

theorem actual_entire_green_transfer (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    D (ActualGreenPrimitive.greenMetricPrimitiveQ p hp) =
      LaurentPolynomial.C (p : ℚ) * ActualGreenPrimitive.greenInfinityMetricQ p hp +
        T (-(((p-1)/2 : ℕ) : ℤ)) *
          (greenSourceAtQ p hp * D (ActualJointGreen.finiteConicLogQ p).toLaurent +
            LaurentPolynomial.C (1/2 : ℚ) * greenLogSourceAtQ p hp) := by
  let N := (p-1)/2
  let s := (ActualGreenPrimitive.greenCoordinateQ p).toLaurent
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let c : ℚ[T;T⁻¹] := 4*T 1-11
  have hs : s≠0 := by
    intro hz
    have hzP : ActualGreenPrimitive.greenCoordinateQ p = 0 :=
      Polynomial.toLaurent_injective (by simpa only [map_zero, s] using hz)
    have he := congrArg (fun P : ℚ[X] => P.coeff 0) hzP
    norm_num [ActualGreenPrimitive.greenCoordinateQ] at he
  have hA : A≠0 := by
    intro hz
    have hzP : (WPFiniteZSource.Abar : ℚ[X]) = 0 :=
      Polynomial.toLaurent_injective (by simpa only [map_zero, A] using hz)
    have he := congrArg (fun P : ℚ[X] => P.coeff 0) hzP
    norm_num [WPFiniteZSource.Abar] at he
  have hc : D c=4 := by
    have hcl : c=(4*X-11 : ℚ[X]).toLaurent := by
      simp only [map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X]
      rfl
    rw [hcl, D_toLaurent]
    simp [map_ofNat]
  have hE : 2*A*D (ActualJointGreen.finiteConicLogQ p).toLaurent-3*c =
      -3*LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*s^N*c^p := by
    have he := congrArg Polynomial.toLaurent
      (ActualJointGreen.actual_finite_conic_log_Abar_source p hp)
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_neg,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X, ← D_toLaurent,
      N, s, A, c, neg_mul] using he
  exact entire_green_transfer p N (by omega) ((1/5 : ℚ)^(p-1))
    s A c (invert (ActualGreenPrimitive.greenCMq p hp).toLaurent)
    (greenSourceAtQ p hp) (ActualJointGreen.finiteConicLogQ p).toLaurent
    (greenLogSourceAtQ p hp) (ActualGreenPrimitive.greenInfinityMetricQ p hp)
    hs hA hc (actual_inverted_CM_source p hp) hE
    (actual_metric_CM_identity p hp) (actual_green_dlogV_source p hp)

theorem resInfinity_C_mul (a : ℚ) (L : ℚ[T;T⁻¹]) :
    ActualJointGreen.resInfinity (LaurentPolynomial.C a*L) =
      a*ActualJointGreen.resInfinity L := by
  simp only [ActualJointGreen.resInfinity, GreenLaurentOperators.C_mul_coeff]
  ring

theorem actual_entire_green_residue (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ActualJointGreen.resInfinity
      (T (-(((p-1)/2 : ℕ) : ℤ))*greenSourceAtQ p hp*
        D (ActualJointGreen.finiteConicLogQ p).toLaurent) =
      -(p : ℚ)*ActualJointGreen.resInfinity
        (ActualGreenPrimitive.greenInfinityMetricQ p hp) := by
  let N := (p-1)/2
  let u : ℚ[T;T⁻¹] := T (-(N : ℤ))
  let E := (ActualJointGreen.finiteConicLogQ p).toLaurent
  let S := greenSourceAtQ p hp
  let rho := greenLogSourceAtQ p hp
  let metric := ActualGreenPrimitive.greenInfinityMetricQ p hp
  have h := congrArg ActualJointGreen.resInfinity
    (actual_entire_green_transfer p hp)
  have he : LaurentPolynomial.C (p : ℚ)*metric +
      u*(S*D E+LaurentPolynomial.C (1/2 : ℚ)*rho) =
        LaurentPolynomial.C (p : ℚ)*metric + u*S*D E +
          LaurentPolynomial.C (1/2 : ℚ)*(u*rho) := by ring
  change ActualJointGreen.resInfinity
    (D (ActualGreenPrimitive.greenMetricPrimitiveQ p hp)) =
      ActualJointGreen.resInfinity
        (LaurentPolynomial.C (p : ℚ)*metric +
          u*(S*D E+LaurentPolynomial.C (1/2 : ℚ)*rho)) at h
  rw [he, ActualJointGreen.resInfinity_D,
    ActualJointGreen.resInfinity_add, ActualJointGreen.resInfinity_add,
    resInfinity_C_mul, resInfinity_C_mul] at h
  have hr : ActualJointGreen.resInfinity (u*rho)=0 :=
    shifted_reciprocal_density_resInfinity_zero N (by omega)
      (ActualGreenPrimitive.greenSq p hp)
  rw [hr, mul_zero, add_zero] at h
  linear_combination -h

theorem actual_entire_green_residue_origin (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ActualJointGreen.resInfinity
      (T (-(((p-1)/2 : ℕ) : ℤ))*greenSourceAtQ p hp*
        D (ActualJointGreen.finiteConicLogQ p).toLaurent) =
      -(p : ℚ)*(ActualGreenPrimitive.greenOriginMetricIntegral p hp).val := by
  rw [actual_entire_green_residue p hp,
    ActualGreenPrimitive.green_metric_origin_orientation p hp,
    ← ActualGreenPrimitive.greenOriginMetricIntegral_value p hp]

noncomputable def inverseAweight : ℤ → ℚ
  | .ofNat n => -((1/4 : ℚ)^n-4^n)/15
  | .negSucc _ => 0

noncomputable def inverseAtrace : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ inverseAweight).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem inverseAtrace_monomial (a : ℚ) (n : ℤ) :
    inverseAtrace (LaurentPolynomial.C a*T n)=a*inverseAweight n := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℚ inverseAweight (Finsupp.single n a)=_
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem inverseAweight_nonpositive (n : ℤ) (hn : n≤0) : inverseAweight n=0 := by
  cases n with
  | ofNat n =>
    have hn0 : n=0 := by
      simp only [Int.ofNat_eq_natCast] at hn
      omega
    subst n
    norm_num [inverseAweight]
  | negSucc n => rfl

theorem inverseAweight_recurrence (n : ℤ) :
    -4*inverseAweight (n+2)+17*inverseAweight (n+1)-4*inverseAweight n =
      if n = -1 then -1 else 0 := by
  cases n with
  | ofNat n =>
    have hn1 : Int.ofNat n+1=Int.ofNat (n+1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hn2 : Int.ofNat n+2=Int.ofNat (n+2) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hn0 : Int.ofNat n≠-1 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hn1, hn2, if_neg hn0]
    simp only [inverseAweight, pow_succ]
    ring
  | negSucc n =>
    cases n with
    | zero =>
      change -4*inverseAweight (Int.ofNat 1)+17*inverseAweight (Int.ofNat 0)-
        4*inverseAweight (Int.negSucc 0) = -1
      norm_num [inverseAweight]
    | succ n =>
      have h0 : Int.negSucc (Nat.succ n)≤0 := by
        simp only [Int.negSucc_eq]
        omega
      have h1 : Int.negSucc (Nat.succ n)+1≤0 := by
        simp only [Int.negSucc_eq]
        omega
      have h2 : Int.negSucc (Nat.succ n)+2≤0 := by
        simp only [Int.negSucc_eq]
        omega
      have hne : Int.negSucc (Nat.succ n)≠-1 := by
        simp only [Int.negSucc_eq]
        omega
      rw [inverseAweight_nonpositive _ h2, inverseAweight_nonpositive _ h1,
        inverseAweight_nonpositive _ h0, if_neg hne]
      norm_num

theorem resInfinity_monomial (a : ℚ) (n : ℤ) :
    ActualJointGreen.resInfinity (LaurentPolynomial.C a*T n) =
      a*(if n = -1 then -1 else 0) := by
  rw [ActualJointGreen.resInfinity, ← single_eq_C_mul_T]
  change -(Finsupp.single n a (-1))=a*(if n = -1 then -1 else 0)
  by_cases hn : n = -1 <;> simp [hn, eq_comm]

theorem inverseAtrace_Abar (L : ℚ[T;T⁻¹]) :
    inverseAtrace ((WPFiniteZSource.Abar : ℚ[X]).toLaurent*L) =
      ActualJointGreen.resInfinity L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM =>
    simp only [mul_add, map_add, ActualJointGreen.resInfinity_add, hL, hM]
  | C_mul_T n a =>
    have hA : (WPFiniteZSource.Abar : ℚ[X]).toLaurent =
        -4*T 2+17*T 1-4 := by
      simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
        Polynomial.toLaurent_X, map_one]
      have h2 : (T 2 : ℚ[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
      rw [h2]
      ring
    have h2 : (T 2 : ℚ[T;T⁻¹])*T n=T (n+2) := by
      rw [←T_add]
      congr 1
      omega
    have h1 : (T 1 : ℚ[T;T⁻¹])*T n=T (n+1) := by
      rw [←T_add]
      congr 1
      omega
    have he : (WPFiniteZSource.Abar : ℚ[X]).toLaurent*(LaurentPolynomial.C a*T n) =
        LaurentPolynomial.C (-4*a)*T (n+2)+
          LaurentPolynomial.C (17*a)*T (n+1)+LaurentPolynomial.C (-4*a)*T n := by
      rw [hA]
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination -4*LaurentPolynomial.C a*h2+17*LaurentPolynomial.C a*h1
    rw [he, map_add, map_add, inverseAtrace_monomial,
      inverseAtrace_monomial, inverseAtrace_monomial, resInfinity_monomial]
    linear_combination a*inverseAweight_recurrence n

noncomputable def dlogQtrace : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  inverseAtrace.comp
    ({
      toFun := fun L => 3*T (-1)*(4-11*T 1)*L
      map_add' := by
        intro L M
        ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem dlogQtrace_apply (L : ℚ[T;T⁻¹]) :
    dlogQtrace L = inverseAtrace (3*T (-1)*(4-11*T 1)*L) := rfl

theorem inverseAtrace_C_mul (a : ℚ) (L : ℚ[T;T⁻¹]) :
    inverseAtrace (LaurentPolynomial.C a*L)=a*inverseAtrace L := by
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using inverseAtrace.map_smul a L

theorem dlogQtrace_C_mul (a : ℚ) (L : ℚ[T;T⁻¹]) :
    dlogQtrace (LaurentPolynomial.C a*L)=a*dlogQtrace L := by
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using dlogQtrace.map_smul a L

theorem shifted_inverted_polynomial_inverseAtrace_zero (N : ℕ) (hN : 0<N)
    (P : ℚ[X]) :
    inverseAtrace (T (-(N : ℤ))*(4*T 1-11)*invert P.toLaurent)=0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, mul_add, hP, hQ, add_zero]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T]
    simp only [map_mul, invert_C, invert_T]
    have h1 : (T (-(N : ℤ)) : ℚ[T;T⁻¹])*T 1*T (-(n : ℤ)) =
        T (1-(N : ℤ)-(n : ℤ)) := by
      rw [← T_add, ← T_add]
      congr 1
      omega
    have h0 : (T (-(N : ℤ)) : ℚ[T;T⁻¹])*T (-(n : ℤ)) =
        T (-(N : ℤ)-(n : ℤ)) := by
      rw [← T_add, sub_eq_add_neg]
    have he : T (-(N : ℤ))*(4*T 1-11)*
        (LaurentPolynomial.C a*T (-(n : ℤ))) =
          LaurentPolynomial.C (4*a)*T (1-(N : ℤ)-(n : ℤ)) +
          LaurentPolynomial.C (-11*a)*T (-(N : ℤ)-(n : ℤ)) := by
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination 4*LaurentPolynomial.C a*h1-11*LaurentPolynomial.C a*h0
    rw [he, map_add, inverseAtrace_monomial, inverseAtrace_monomial,
      inverseAweight_nonpositive _ (by omega),
      inverseAweight_nonpositive _ (by omega)]
    ring

noncomputable def greenProperTraceNumeratorQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*(4*T 1-11)^p*
    invert (ActualGreenPrimitive.greenCBq p hp).toLaurent

noncomputable def greenTBAtQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ℚ[T;T⁻¹] :=
  invert ((ActualGreenPrimitive.greenTBq p hp).comp
    WPActualPullbackSource.Vpolynomial).toLaurent

/-- The numerator of Z^p B(T_vee), with no branch or proper inverse. -/
theorem actual_green_proper_trace_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    T (-1)*(4-11*T 1)*greenProperTraceNumeratorQ p hp =
      LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*T (-(((p-1)/2 : ℕ) : ℤ))*
        (ActualGreenPrimitive.greenCoordinateQ p).toLaurent^((p-1)/2)*
        (4*T 1-11)^p*greenTBAtQ p hp := by
  let N := (p-1)/2
  let s := (ActualGreenPrimitive.greenCoordinateQ p).toLaurent
  let c : ℚ[T;T⁻¹] := 4*T 1-11
  let d : ℚ[T;T⁻¹] := 4-11*T 1
  let CB := invert (ActualGreenPrimitive.greenCBq p hp).toLaurent
  let TB := greenTBAtQ p hp
  have hu : (T 1 : ℚ[T;T⁻¹])*T (-1)=1 := by rw [←T_add]; norm_num
  have hc : invert c=T (-1)*d := by
    simp only [c, d, map_sub, map_mul, map_ofNat, invert_T]
    linear_combination 11*hu
  have hs : invert s=T (-1)*s := greenCoordinateQ_invert p
  have he0 := congrArg Polynomial.toLaurent
    (ActualGreenPrimitive.greenCBq_TB_source p hp)
  simp only [map_mul, map_sub, map_pow, map_ofNat, Polynomial.toLaurent_X] at he0
  have he := congrArg invert he0
  simp only [map_mul, map_pow] at he
  change invert c*CB=(invert s)^N*TB at he
  rw [hc, hs] at he
  have hph : (T (-1) : ℚ[T;T⁻¹])^N=T (-(N : ℤ)) := by
    rw [T_pow]
    congr 1
    omega
  rw [mul_pow, hph] at he
  unfold greenProperTraceNumeratorQ
  change T (-1)*d*(LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*c^p*CB)=_
  linear_combination LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*c^p*he

theorem actual_tau_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
      (-2*T (-(((p-1)/2 : ℕ) : ℤ))*greenTBAtQ p hp*
        D (ActualJointGreen.finiteConicLogQ p).toLaurent) =
      3*T (-1)*(4-11*T 1)*greenProperTraceNumeratorQ p hp -
        3*T (-(((p-1)/2 : ℕ) : ℤ))*(4*T 1-11)*greenTBAtQ p hp := by
  let u : ℚ[T;T⁻¹] := T (-(((p-1)/2 : ℕ) : ℤ))
  let TB := greenTBAtQ p hp
  have hE := congrArg Polynomial.toLaurent
    (ActualJointGreen.actual_finite_conic_log_Abar_source p hp)
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_neg,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, ←D_toLaurent] at hE
  have hg := actual_green_proper_trace_source p hp
  simp only [map_pow] at hg
  linear_combination -u*TB*hE-3*hg

/-- Res_infinity tau_* = -2 Res_infinity x^(-N) TB_*(Q) de_N(T_t). -/
theorem actual_tau_residue (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    dlogQtrace (greenProperTraceNumeratorQ p hp) =
      -2*ActualJointGreen.resInfinity
        (T (-(((p-1)/2 : ℕ) : ℤ))*greenTBAtQ p hp*
          D (ActualJointGreen.finiteConicLogQ p).toLaurent) := by
  let u : ℚ[T;T⁻¹] := T (-(((p-1)/2 : ℕ) : ℤ))
  let c : ℚ[T;T⁻¹] := 4*T 1-11
  let TB := greenTBAtQ p hp
  let E := (ActualJointGreen.finiteConicLogQ p).toLaurent
  have hz : inverseAtrace (u*c*TB)=0 :=
    shifted_inverted_polynomial_inverseAtrace_zero ((p-1)/2) (by omega)
      ((ActualGreenPrimitive.greenTBq p hp).comp WPActualPullbackSource.Vpolynomial)
  have hz3 : inverseAtrace (3*u*c*TB)=0 := by
    have hs := inverseAtrace_C_mul 3 (u*c*TB)
    simp only [map_ofNat] at hs
    have he : 3*u*c*TB=3*(u*c*TB) := by ring
    rw [he, hs, hz, mul_zero]
  have h := congrArg inverseAtrace (actual_tau_cleared_source p hp)
  rw [inverseAtrace_Abar, map_sub, ←dlogQtrace_apply] at h
  change ActualJointGreen.resInfinity (-2*u*TB*D E)=
    dlogQtrace (greenProperTraceNumeratorQ p hp)-inverseAtrace (3*u*c*TB) at h
  rw [hz3, sub_zero] at h
  have he : -2*u*TB*D E=LaurentPolynomial.C (-2 : ℚ)*(u*TB*D E) := by
    simp only [map_neg, map_ofNat]
    ring
  rw [he, resInfinity_C_mul] at h
  exact h.symm

theorem resInfinity_neg (L : ℚ[T;T⁻¹]) :
    ActualJointGreen.resInfinity (-L) = -ActualJointGreen.resInfinity L := by
  simp only [ActualJointGreen.resInfinity, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]

theorem resInfinity_sub (L M : ℚ[T;T⁻¹]) :
    ActualJointGreen.resInfinity (L-M)=
      ActualJointGreen.resInfinity L-ActualJointGreen.resInfinity M := by
  rw [sub_eq_add_neg, ActualJointGreen.resInfinity_add, resInfinity_neg]
  ring

noncomputable def greenHAtQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ℚ[T;T⁻¹] :=
  invert ((ActualGreenPrimitive.greenHq p hp).comp
    WPActualPullbackSource.Vpolynomial).toLaurent

theorem greenSourceAtQ_actual_split (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    greenSourceAtQ p hp = 2*greenHAtQ p hp+4*greenTBAtQ p hp-
      LaurentPolynomial.C
        (4*(WPPIntegralReduction.integralRationals p).subtype
          ((ActualBalancedCarry.balancedProperIntegral p hp).eval 1)) := by
  have he := congrArg (fun P : ℚ[X] =>
    invert (P.comp WPActualPullbackSource.Vpolynomial).toLaurent)
      (ActualGreenPrimitive.greenSq_source p hp)
  simpa only [add_comp, sub_comp, mul_comp, ofNat_comp, C_comp,
    _root_.map_natCast, Nat.cast_ofNat, map_add, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_C,
    invert_C, greenSourceAtQ, greenHAtQ, greenTBAtQ] using he

/-- SB101e before division; the literal p is produced over Q. -/
theorem actual_SB101e (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ActualJointGreen.resInfinity
      (T (-(((p-1)/2 : ℕ) : ℤ))*greenHAtQ p hp*
        D (ActualJointGreen.finiteConicLogQ p).toLaurent) -
      dlogQtrace (greenProperTraceNumeratorQ p hp) =
        -(p : ℚ)/2*(ActualGreenPrimitive.greenOriginMetricIntegral p hp).val +
        2*(WPPIntegralReduction.integralRationals p).subtype
          ((ActualBalancedCarry.balancedProperIntegral p hp).eval 1)*
            (ActualJointGreen.finiteLogCIntegral p hp).val := by
  let u : ℚ[T;T⁻¹] := T (-(((p-1)/2 : ℕ) : ℤ))
  let E := (ActualJointGreen.finiteConicLogQ p).toLaurent
  let S := greenSourceAtQ p hp
  let H := greenHAtQ p hp
  let TB := greenTBAtQ p hp
  let n1 : ℚ := (WPPIntegralReduction.integralRationals p).subtype
    ((ActualBalancedCarry.balancedProperIntegral p hp).eval 1)
  have hsrc := greenSourceAtQ_actual_split p hp
  have he : u*S*D E = LaurentPolynomial.C (2 : ℚ)*(u*H*D E)+
      LaurentPolynomial.C (4 : ℚ)*(u*TB*D E)-
      LaurentPolynomial.C (4*n1)*(u*D E) := by
    change S=2*H+4*TB-LaurentPolynomial.C (4*n1) at hsrc
    rw [hsrc]
    simp only [map_ofNat, map_mul]
    ring
  have hres := congrArg ActualJointGreen.resInfinity he
  rw [resInfinity_sub, ActualJointGreen.resInfinity_add,
    resInfinity_C_mul, resInfinity_C_mul, resInfinity_C_mul] at hres
  have hC : ActualJointGreen.resInfinity (u*D E)=
      (ActualJointGreen.finiteLogCIntegral p hp).val :=
    ActualJointGreen.actual_finite_log_C_residue p hp
  rw [hC] at hres
  have hG := actual_entire_green_residue_origin p hp
  have hTau := actual_tau_residue p hp
  linear_combination (1/2 : ℚ)*hG-(1/2 : ℚ)*hres-hTau

theorem dlogQtrace_T_nonpositive (n : ℤ) (hn : n≤0) :
    dlogQtrace (T n : ℚ[T;T⁻¹])=0 := by
  have h0 : (T (-1) : ℚ[T;T⁻¹])*T n=T (n-1) := by
    rw [←T_add]
    congr 1
    omega
  have hu : (T (-1) : ℚ[T;T⁻¹])*T 1=1 := by rw [←T_add]; norm_num
  have he : (3*T (-1)*(4-11*T 1) : ℚ[T;T⁻¹])*T n =
      LaurentPolynomial.C (12 : ℚ)*T (n-1)+LaurentPolynomial.C (-33 : ℚ)*T n := by
    simp only [map_ofNat, map_neg]
    linear_combination 12*h0-33*T n*hu
  rw [dlogQtrace_apply]
  rw [he, map_add, inverseAtrace_monomial, inverseAtrace_monomial,
    inverseAweight_nonpositive _ (by omega), inverseAweight_nonpositive _ hn]
  ring

theorem actual_Qrev_eq_V : (WPFiniteNC122Residue.Qrev : ℚ[X]) =
    WPActualPullbackSource.Vpolynomial := by
  apply Polynomial.funext
  intro x
  simp only [WPFiniteNC122Residue.Qrev, WPActualPullbackSource.Vpolynomial,
    eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, eval_one]
  ring

/-- Cleared dlogQ source; the constant of P is retained until the shifted trace. -/
theorem original_polynomial_dlogQ_cleared (P : ℚ[X]) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
      (-T (-2)*(WPFiniteNC122Residue.canceledDensity P).toLaurent) =
      3*T (-1)*(4-11*T 1)*
        ((P.comp WPActualPullbackSource.Vpolynomial).toLaurent-
          LaurentPolynomial.C (P.coeff 0)) := by
  let V := WPActualPullbackSource.Vpolynomial
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let d : ℚ[T;T⁻¹] := 4-11*T 1
  let B := (P.divX.comp V).toLaurent
  have hfP : (WPFiniteZSource.Abar : ℚ[X])*(WPFiniteNC122Residue.Frev : ℚ[X]) =
      -3*X*(4-11*X)*V := by
    apply Polynomial.funext
    intro x
    simp only [WPFiniteZSource.Abar, WPFiniteNC122Residue.Frev, V,
      WPActualPullbackSource.Vpolynomial, eval_sub, eval_add, eval_mul,
      eval_pow, eval_C, eval_X, eval_ofNat, eval_one, eval_neg]
    ring
  have hf := congrArg Polynomial.toLaurent hfP
  simp only [map_mul, map_neg, map_sub, map_ofNat, Polynomial.toLaurent_X] at hf
  have hdP : X*P.divX=P-Polynomial.C (P.coeff 0) := by
    linear_combination X_mul_divX_add P
  have hd := congrArg (fun Q : ℚ[X] => (Q.comp V).toLaurent) hdP
  simp only [mul_comp, X_comp, sub_comp, C_comp, map_mul, map_sub,
    Polynomial.toLaurent_C] at hd
  have ht : (T (-2) : ℚ[T;T⁻¹])*T 1=T (-1) := by rw [←T_add]; norm_num
  rw [WPFiniteNC122Residue.canceledDensity, actual_Qrev_eq_V, map_mul]
  change A*(-T (-2)*(B*(WPFiniteNC122Residue.Frev : ℚ[X]).toLaurent))=_
  calc
    _ = -T (-2)*B*(A*(WPFiniteNC122Residue.Frev : ℚ[X]).toLaurent) := by ring
    _ = 3*(T (-2)*T 1)*d*(V.toLaurent*B) := by rw [hf]; ring
    _ = _ := by rw [ht, hd]

theorem original_polynomial_dlogQ_projection (N : ℕ) (hN : 0<N) (P : ℚ[X]) :
    dlogQtrace (T (-(N : ℤ))*(P.comp WPActualPullbackSource.Vpolynomial).toLaurent) =
      (WPFiniteNC122Residue.canceledDensity P).coeff (N+1) := by
  let u : ℚ[T;T⁻¹] := T (-(N : ℤ))
  let G := (WPFiniteNC122Residue.canceledDensity P).toLaurent
  let V := WPActualPullbackSource.Vpolynomial
  have hc := original_polynomial_dlogQ_cleared P
  have he : (WPFiniteZSource.Abar : ℚ[X]).toLaurent*(-u*T (-2)*G) =
      3*T (-1)*(4-11*T 1)*(u*((P.comp V).toLaurent-
        LaurentPolynomial.C (P.coeff 0))) := by
    linear_combination u*hc
  have h := congrArg inverseAtrace he
  rw [inverseAtrace_Abar, ←dlogQtrace_apply] at h
  change ActualJointGreen.resInfinity (-u*T (-2)*G)=
    dlogQtrace (u*((P.comp V).toLaurent-LaurentPolynomial.C (P.coeff 0))) at h
  have hs : u*((P.comp V).toLaurent-LaurentPolynomial.C (P.coeff 0)) =
      u*(P.comp V).toLaurent-LaurentPolynomial.C (P.coeff 0)*u := by ring
  rw [hs, map_sub, dlogQtrace_C_mul,
    dlogQtrace_T_nonpositive _ (by omega), mul_zero, sub_zero] at h
  have hphase : (u*T (-2) : ℚ[T;T⁻¹])=T (-((N+2 : ℕ) : ℤ)) := by
    rw [←T_add]
    congr 1
    omega
  rw [show -u*T (-2)*G=-(u*T (-2)*G) by ring,
    hphase, ActualJointGreen.resInfinity, AddMonoidAlgebra.coeff_neg,
    Finsupp.neg_apply, neg_neg] at h
  have hj := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-((N+2 : ℕ) : ℤ)) (-1) G
  simp only [map_one, one_mul] at hj
  rw [show (-1 : ℤ)- -((N+2 : ℕ) : ℤ)=((N+1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat] at hj
  rw [hj] at h
  exact h.symm

theorem actual_proper_conic_numerator (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (NativeQuadraticInverse.quadraticInverse (X^p*ActualGreenPrimitive.greenBq p hp)).comp
      WPActualPullbackSource.Vpolynomial =
        Polynomial.C ((1/5 : ℚ)^(p-1))*(4*X-11)^p*
          ActualGreenPrimitive.greenCBq p hp := by
  let B := ActualGreenPrimitive.greenBq p hp
  let P : ℚ[X] := X^p*B
  let c : ℚ[X] := 4*X-11
  let b : ℚ[X] := 4*X^2-3
  let Tc : ℚ[X] := WPFiniteCubicLog.Tc
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have heven : P.comp (-X)=P := by
    simp only [P, mul_comp, pow_comp, X_comp,
      hpodd.neg_pow]
    rw [show B.comp (-X) = -B from ActualGreenPrimitive.greenBq_odd p hp]
    ring
  have hPull := ActualGreenPrimitive.quadraticInverse_even_pullback P
    (by norm_num : (2 : ℚ)≠0) heven
  have hV : WPActualPullbackSource.Vpolynomial.comp
      (ActualGreenPrimitive.greenConicQ p)=1-Tc^2 := by
    have h125 : (125 : ℚ[X])*Polynomial.C (1/125 : ℚ)=1 := by
      change Polynomial.C (125 : ℚ)*Polynomial.C (1/125 : ℚ)=Polynomial.C 1
      rw [←Polynomial.C_mul]
      norm_num
    simp only [WPActualPullbackSource.Vpolynomial, ActualGreenPrimitive.greenConicQ,
      Tc, WPFiniteCubicLog.Tc, mul_comp, C_comp, sub_comp, ofNat_comp, pow_comp,
      one_comp, X_comp]
    linear_combination (1-(4*X^3-3*X)^2)*h125
  have hc : c.comp (ActualGreenPrimitive.greenConicQ p)=5*b := by
    simp only [c, b, ActualGreenPrimitive.greenConicQ, sub_comp, mul_comp, ofNat_comp, X_comp]
    ring
  have hTc : Tc=X*b := by simp only [Tc, b, WPFiniteCubicLog.Tc]; ring
  have hk0 : (1/5 : ℚ)^(p-1)*5^(p-1)=1 := by rw [←mul_pow]; norm_num
  have hk : (1/5 : ℚ)^(p-1)*5^p*(1/5)=1 := by
    have hpw : (5 : ℚ)^p=5^(p-1)*5 := by rw [←pow_succ, Nat.sub_add_cancel (by omega : 1≤p)]
    rw [hpw]
    linear_combination hk0
  have hkP : Polynomial.C ((1/5 : ℚ)^(p-1))*(5 : ℚ[X])^p*Polynomial.C (1/5 : ℚ)=1 := by
    rw [show (5 : ℚ[X]) = Polynomial.C (5 : ℚ) from
      (_root_.map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 5).symm,
      ←Polynomial.C_pow, ←Polynomial.C_mul, ←Polynomial.C_mul, hk, map_one]
  have hcd : (ActualGreenPrimitive.greenConicQ p).natDegree=2 := by
    unfold ActualGreenPrimitive.greenConicQ
    compute_degree; norm_num
  apply ConicKernel.comp_injective_nonconstant (ActualGreenPrimitive.greenConicQ p)
    (by rw [hcd]; norm_num)
  change ((NativeQuadraticInverse.quadraticInverse P).comp
      WPActualPullbackSource.Vpolynomial).comp (ActualGreenPrimitive.greenConicQ p) =
    (Polynomial.C ((1/5 : ℚ)^(p-1))*c^p*
      ActualGreenPrimitive.greenCBq p hp).comp (ActualGreenPrimitive.greenConicQ p)
  rw [comp_assoc, hV,
    show (1-Tc^2 : ℚ[X])=(1-X^2 : ℚ[X]).comp Tc by simp,
    ←comp_assoc, hPull]
  simp only [mul_comp, C_comp, pow_comp]
  rw [hc, (ActualGreenPrimitive.green_actual_carrier_pullbacks_Q p hp).2]
  rw [hTc]
  dsimp only [P]
  rw [mul_comp, pow_comp, X_comp,
    show (WPFiniteCubicLog.Tc : ℚ[X])=X*b from hTc]
  change (X*b)^p*B.comp (X*b)=
    Polynomial.C ((1/5 : ℚ)^(p-1))*(5*b)^p*
      (Polynomial.C (1/5 : ℚ)*X^p*B.comp (X*b))
  rw [mul_pow, mul_pow]
  linear_combination -X^p*b^p*B.comp (X*b)*hkP

theorem actual_positive_proper_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    dlogQtrace (T (-(((p-1)/2 : ℕ) : ℤ))*
      LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*(4*T 1-11)^p*
        (ActualGreenPrimitive.greenCBq p hp).toLaurent) =
      ActualDeltaUNextSource.QO p (X^p*ActualGreenPrimitive.greenBq p hp) := by
  have he := congrArg Polynomial.toLaurent (actual_proper_conic_numerator p hp)
  simp only [map_mul, Polynomial.toLaurent_C] at he
  rw [(_root_.map_pow (Polynomial.toLaurent : ℚ[X] →+* ℚ[T;T⁻¹])
    (4*X-11) p)] at he
  simp only [map_sub, map_mul, map_ofNat,
    Polynomial.toLaurent_X] at he
  have hL : T (-(((p-1)/2 : ℕ) : ℤ))*
      LaurentPolynomial.C ((1/5 : ℚ)^(p-1))*(4*T 1-11)^p*
        (ActualGreenPrimitive.greenCBq p hp).toLaurent =
      T (-(((p-1)/2 : ℕ) : ℤ))*
        ((NativeQuadraticInverse.quadraticInverse
          (X^p*ActualGreenPrimitive.greenBq p hp)).comp
          WPActualPullbackSource.Vpolynomial).toLaurent := by
    rw [he]
    ring
  rw [hL, original_polynomial_dlogQ_projection _ (by omega)]
  simp only [ActualDeltaUNextSource.QO, ResidualProjection.Ij, Nat.zero_mul, Nat.add_zero]

theorem greenBq_actual_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ActualGreenPrimitive.greenBq p hp=
      WPActualRankTwoParameter.rankJacobiNode p 1*
        ActualBalancedNodeAttachment.balancedProperQ p hp := by
  simp only [ActualGreenPrimitive.greenBq, ActualGreenPrimitive.greenBIntegral,
    Polynomial.map_mul, ActualBalancedNodeAttachment.balancedFirstIntegral_value p hp,
    ActualBalancedNodeAttachment.balancedProperQ]

noncomputable def dlogVtrace : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  inverseAtrace.comp
    ({
      toFun := fun L => (33 - 12 * T 1) * L
      map_add' := by
        intro L M
        ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem dlogVtrace_apply (L : ℚ[T;T⁻¹]) :
    dlogVtrace L = inverseAtrace ((33-12*T 1)*L) := rfl

theorem dlogVtrace_monomial (a : ℚ) (n : ℤ) :
    dlogVtrace (LaurentPolynomial.C a * T n) =
      33 * a * inverseAweight n - 12 * a * inverseAweight (n + 1) := by
  have ht : (T 1 : ℚ[T;T⁻¹]) * T n = T (n + 1) := by
    rw [← T_add]
    congr 1
    omega
  have he : (33 - 12 * T 1 : ℚ[T;T⁻¹]) *
      (LaurentPolynomial.C a * T n) =
      LaurentPolynomial.C (33 * a) * T n -
        LaurentPolynomial.C (12 * a) * T (n + 1) := by
    simp only [map_mul, map_ofNat]
    linear_combination -12 * LaurentPolynomial.C a * ht
  rw [dlogVtrace_apply]
  rw [he, map_sub, inverseAtrace_monomial, inverseAtrace_monomial]

theorem dlogVtrace_T_nonpositive (n : ℤ) (hn : n ≤ 0) :
    dlogVtrace (T n) = if n = 0 then -3 else 0 := by
  have he := dlogVtrace_monomial 1 n
  simp only [map_one, one_mul, mul_one] at he
  rw [he, inverseAweight_nonpositive n hn]
  by_cases hz : n = 0
  · subst n
    norm_num [inverseAweight]
  · rw [if_neg hz, inverseAweight_nonpositive (n + 1) (by omega)]
    ring

/-- Exact Euler endpoint at infinity; the reciprocal cubic is regular there. -/
theorem dlogVtrace_invert_polynomial (P : ℚ[X]) :
    dlogVtrace (invert P.toLaurent) = -3 * P.coeff 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, Polynomial.coeff_add]
    ring
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T]
    simp only [map_mul, invert_C, invert_T]
    have hs := dlogVtrace.map_smul a (T (-(n : ℤ)))
    simp only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] at hs
    rw [hs, dlogVtrace_T_nonpositive _ (by omega), Polynomial.coeff_monomial]
    by_cases hn : n = 0 <;> simp [hn]; ring

/-- The strictly negative extra phase removes the shifted Euler endpoint. -/
theorem shifted_inverted_polynomial_dlogVtrace_zero
    (N : ℕ) (hN : 0 < N) (P : ℚ[X]) :
    dlogVtrace (T (-(N : ℤ)) * invert P.toLaurent) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, mul_add, hP, hQ, add_zero]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T]
    simp only [map_mul, invert_C, invert_T]
    have ht : (T (-(N : ℤ)) : ℚ[T;T⁻¹]) * T (-(n : ℤ)) =
        T (-(N : ℤ) - (n : ℤ)) := by
      rw [← T_add, sub_eq_add_neg]
    rw [show T (-(N : ℤ)) * (LaurentPolynomial.C a * T (-(n : ℤ))) =
      LaurentPolynomial.C a * (T (-(N : ℤ)) * T (-(n : ℤ))) by ring, ht]
    have hs := dlogVtrace.map_smul a (T (-(N : ℤ) - (n : ℤ)))
    simp only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] at hs
    rw [hs, dlogVtrace_T_nonpositive _ (by omega), if_neg (by omega), mul_zero]

theorem actual_Euler_dlogV_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    dlogVtrace (greenHAtQ p hp) =
      -3 * (ActualGreenPrimitive.greenHq p hp).eval (4 / 125) := by
  rw [greenHAtQ, dlogVtrace_invert_polynomial, coeff_zero_eq_eval_zero,
    eval_comp]
  have hv : WPActualPullbackSource.Vpolynomial.eval 0 = (4 / 125 : ℚ) := by
    norm_num [WPActualPullbackSource.Vpolynomial]
  rw [hv]

end WPFieldAssembly.ActualBalancedGreenTransfer
