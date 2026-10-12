import WPFieldAssembly.ActualConicFiniteLog

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPPIntegralReduction

namespace WPFieldAssembly.ActualBalancedGreenTransfer

theorem D_pow_nat (L : ℚ[T;T⁻¹]) (n : ℕ) :
    D (L^(n+1)) = LaurentPolynomial.C ((n+1 : ℕ) : ℚ) * L^n * D L := by
  induction n with
  | zero =>
    simp only [pow_one, pow_zero, Nat.zero_add, Nat.cast_one, map_one, one_mul]
  | succ n ih =>
    rw [pow_succ, D_mul, ih, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem entire_green_transfer (p N : ℕ) (hp : 0<p) (k : ℚ)
    (s A c CM SQ E rho metric : ℚ[T;T⁻¹])
    (hs : s≠0) (hA : A≠0) (hc : D c=4)
    (hCM : 10*s*A*D CM =
      -15*s^(N+1)*T (-(N : ℤ))*SQ - LaurentPolynomial.C (p : ℚ)*A*T (-1)*CM)
    (hE : 2*A*D E-3*c = -3*LaurentPolynomial.C k*s^N*c^p)
    (hMetric : 10*s*metric = LaurentPolynomial.C k *
      (40*s*c^(p-1)-T (-1)*c^p)*CM)
    (hRho : A*rho = -3*c*SQ) :
    D (LaurentPolynomial.C k*c^p*CM) =
      LaurentPolynomial.C (p : ℚ)*metric + T (-(N : ℤ))*
        (SQ*D E + LaurentPolynomial.C (1/2 : ℚ)*rho) := by
  have hp' : p=(p-1)+1 := by omega
  have hcp : D (c^p) = LaurentPolynomial.C (p : ℚ)*c^(p-1)*4 := by
    conv_lhs => rw [hp']
    rw [D_pow_nat, hc, ← hp']
  have hGD : D (LaurentPolynomial.C k*c^p*CM) =
      4*LaurentPolynomial.C k*LaurentPolynomial.C (p : ℚ)*c^(p-1)*CM +
      LaurentPolynomial.C k*c^p*D CM := by
    rw [D_mul, D_C_mul, hcp]
    ring
  have hhalf : (2 : ℚ[T;T⁻¹]) * LaurentPolynomial.C (1/2 : ℚ) = 1 := by
    rw [show (2 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (2 : ℚ) from
      (_root_.map_natCast (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹]) 2).symm,
      ← map_mul]
    norm_num
  have hz : 10*s*A*(D (LaurentPolynomial.C k*c^p*CM) -
      LaurentPolynomial.C (p : ℚ)*metric - T (-(N : ℤ))*
        (SQ*D E + LaurentPolynomial.C (1/2 : ℚ)*rho)) = 0 := by
    simp only [pow_succ] at hCM
    linear_combination 10*s*A*hGD + LaurentPolynomial.C k*c^p*hCM -
      LaurentPolynomial.C (p : ℚ)*A*hMetric -
      5*s*T (-(N : ℤ))*SQ*hE - 5*s*T (-(N : ℤ))*hRho -
      5*s*A*T (-(N : ℤ))*rho*hhalf
  have h10 : (10 : ℚ[T;T⁻¹]) ≠ 0 := by
    rw [show (10 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (10 : ℚ) from
      (_root_.map_natCast (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹]) 10).symm]
    intro hz
    have hcoef := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff 0) hz
    have hzero : (0 : ℚ[T;T⁻¹]).coeff 0 = 0 := rfl
    rw [LaurentPolynomial.C_apply, if_pos rfl, hzero] at hcoef
    norm_num at hcoef
  have hzero := (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero h10 hs) hA)
  linear_combination hzero

noncomputable def greenSourceAtQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ℚ[T;T⁻¹] :=
  invert ((ActualGreenPrimitive.greenSq p hp).comp
    WPActualPullbackSource.Vpolynomial).toLaurent

noncomputable def greenLogSourceAtQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ℚ[T;T⁻¹] :=
  OriginalLaurentDensity.reciprocalDensity (ActualGreenPrimitive.greenSq p hp)

private theorem reciprocal_polynomial_at_Q (P : ℚ[X]) :
    invert (P.comp WPActualPullbackSource.Vpolynomial).toLaurent =
      WPFiniteLaurentIntegral.substitute P WPActualEtaPole.Qx := by
  calc
    _ = invert (WPActualChiSource.substituteOver P
      WPActualPullbackSource.Vpolynomial.toLaurent) := by
      rw [WPActualChiSource.substituteOver_toLaurent]
    _ = WPActualChiSource.substituteOver P
      (invert WPActualPullbackSource.Vpolynomial.toLaurent) := by
      rw [WPActualChiSource.substituteOver_invert]
    _ = _ := by
      rw [show invert WPActualPullbackSource.Vpolynomial.toLaurent =
        WPActualEtaPole.Qx by
          change invert WPActualEtaPole.Vx = WPActualEtaPole.Qx
          exact WPActualChiSource.actual_Vx_reciprocal]
      rfl

theorem actual_green_dlogV_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent * greenLogSourceAtQ p hp =
      -3*(4*T 1-11)*greenSourceAtQ p hp := by
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let c : ℚ[T;T⁻¹] := 4*T 1-11
  have hquarter : (4 : ℚ[T;T⁻¹]) * LaurentPolynomial.C (1/4 : ℚ) = 1 := by
    rw [show (4 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (4 : ℚ) from
      (_root_.map_natCast (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹]) 4).symm,
      ← map_mul]
    norm_num
  have hD : 4*OriginalLaurentDensity.D = -A := by
    simp only [OriginalLaurentDensity.D, A, WPFiniteZSource.Abar,
      map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X, map_one]
    linear_combination (4-T 1)*hquarter
  have hK : 4*OriginalLaurentDensity.K = 3*c := by
    simp only [OriginalLaurentDensity.K, c, map_ofNat]
    linear_combination -hquarter
  have hF := OriginalLaurentDensity.D_mul_Frev_inverse
  have hf : A*OriginalLaurentDensity.Frev_inverse = -3*c*WPActualEtaPole.Qx := by
    linear_combination -4*hF + OriginalLaurentDensity.Frev_inverse*hD -
      WPActualEtaPole.Qx*hK
  have hdiv : X*(ActualGreenPrimitive.greenSq p hp).divX =
      ActualGreenPrimitive.greenSq p hp := by
    simpa only [ActualGreenPrimitive.greenSq_origin p hp, map_zero, add_zero] using
      X_mul_divX_add (ActualGreenPrimitive.greenSq p hp)
  have hQ := congrArg
    (Polynomial.eval₂RingHom LaurentPolynomial.C WPActualEtaPole.Qx) hdiv
  simp only [map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at hQ
  change WPActualEtaPole.Qx *
    WPFiniteLaurentIntegral.substitute (ActualGreenPrimitive.greenSq p hp).divX
      WPActualEtaPole.Qx =
    WPFiniteLaurentIntegral.substitute (ActualGreenPrimitive.greenSq p hp)
      WPActualEtaPole.Qx at hQ
  rw [greenLogSourceAtQ, OriginalLaurentDensity.reciprocalDensity_factor,
    greenSourceAtQ, reciprocal_polynomial_at_Q]
  change A*(WPFiniteLaurentIntegral.substitute (ActualGreenPrimitive.greenSq p hp).divX
    WPActualEtaPole.Qx*OriginalLaurentDensity.Frev_inverse) =
      -3*c*WPFiniteLaurentIntegral.substitute (ActualGreenPrimitive.greenSq p hp)
        WPActualEtaPole.Qx
  linear_combination WPFiniteLaurentIntegral.substitute
    (ActualGreenPrimitive.greenSq p hp).divX WPActualEtaPole.Qx * hf - 3*c*hQ

theorem shifted_reciprocal_density_resInfinity_zero (N : ℕ) (hN : 0<N) (P : ℚ[X]) :
    ActualJointGreen.resInfinity (T (-(N : ℤ))*
      OriginalLaurentDensity.reciprocalDensity P) = 0 := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-(N : ℤ)) (-1)
    (OriginalLaurentDensity.reciprocalDensity P)
  simp only [map_one, one_mul] at hs
  rw [ActualJointGreen.resInfinity, hs,
    OriginalLaurentDensity.reciprocalDensity, LaurentPolynomial.invert_apply]
  by_cases h1 : N=1
  · subst N
    norm_num only
    have h0 : (WPFiniteNC122Residue.canceledDensity P).toLaurent.coeff 0 =
        (WPFiniteNC122Residue.canceledDensity P).coeff 0 := by
      simpa only [Nat.cast_zero] using
        WPFiniteJCarrier.toLaurent_coeff_nat (WPFiniteNC122Residue.canceledDensity P) 0
    rw [h0]
    simp [WPFiniteNC122Residue.canceledDensity, WPFiniteNC122Residue.Frev]
  · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))]
    simp

end WPFieldAssembly.ActualBalancedGreenTransfer
