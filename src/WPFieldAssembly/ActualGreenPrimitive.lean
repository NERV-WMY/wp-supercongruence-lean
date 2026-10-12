import WPFieldAssembly.ActualBalancedNodeAttachment
import WPFieldAssembly.ActualFirstGreen
import WPFieldAssembly.ActualLowEuler
import WPFieldAssembly.ActualJointGreen

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial (T invert)
open Polynomial WPPIntegralReduction
  WPFieldAssembly.ActualTC1Family WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualBalancedNodeAttachment WPFieldAssembly.ActualR0Node
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.NativeEulerPrimitive
  WPActualRankTwoParameter WPActualRankTwoProper WPActualRankTwoLegendreField
  WPActualRankTwoComparison WPActualRankTwoHatLift WPActualGaussProper WPActualGaussBottom
  WPActualRankTwoLowTaylor

namespace WPFieldAssembly.ActualGreenPrimitive
set_option maxHeartbeats 1600000

section ElementaryPolynomial
variable {K : Type*} [CommRing K]

theorem etaStep_eval (u : ℕ → K) (j : ℕ) (a : K) (U V : EtaPoly K) :
    (etaStep u j U V).eval (C a) = C (u (j + 2)) *
      (C (((2 * j + 3 : ℕ) : K) - a) * X * V.eval (C a) -
        C (((j + 1 : ℕ) : K) - a) * U.eval (C a)) := by
  simp [etaStep, cc, tx, ActualTC1Family.eta, Nat.cast_add, Nat.cast_mul, C_ofNat]

theorem scaledEta_eval_reflect (u : ℕ → K) (a : K) (m : ℕ) :
    ((scaledEta u m).eval (C a)).comp (-X) =
      C ((-1 : K) ^ m) * (scaledEta u m).eval (C a) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [scaledEta]
  | one => simp [scaledEta, ActualTC1Family.eta, tx, mul_comp, sub_comp]
  | more j ih0 ih1 =>
      simp only [scaledEta, etaStep_eval, mul_comp, sub_comp,
        C_comp, X_comp, ih0, ih1, pow_succ, map_mul, map_neg, map_one]
      ring

theorem properEta_eval_reflect (u : ℕ → K) (a : K) (m : ℕ) :
    ((properEta u m).eval (C a)).comp (-X) =
      -C ((-1 : K) ^ m) * (properEta u m).eval (C a) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [properEta]
  | one => simp [properEta]
  | more j ih0 ih1 =>
      simp only [properEta, etaStep_eval, mul_comp, sub_comp,
        C_comp, X_comp, ih0, ih1, pow_succ, map_mul, map_neg, map_one]
      ring

theorem sign_square (m : ℕ) : ((-1 : K) ^ m) ^ 2 = 1 := by
  rw [← pow_mul, show m * 2 = 2 * m by omega, pow_mul]
  simp

theorem divX_map_local {L : Type*} [CommRing L] (f : K →+* L) (P : K[X]) :
    P.divX.map f = (P.map f).divX := by
  ext n
  simp only [coeff_map, coeff_divX]
end ElementaryPolynomial

section EvenPolynomial
variable {K : Type*} [CommRing K] [IsDomain K]

theorem even_expand_contract (P : K[X]) (h2 : (2 : K) ≠ 0)
    (he : P.comp (-X) = P) : expand K 2 (contract 2 P) = P := by
  ext j
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hj]
  · rw [if_neg hj]
    have hm : j % 2 = 1 := by
      have hlt := Nat.mod_lt j (by norm_num : 0 < 2)
      have hne : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hj
      omega
    have ho : Odd j := ⟨j / 2, by have hh := Nat.mod_add_div j 2; omega⟩
    have hc := congrArg (fun Q : K[X] => Q.coeff j) he
    rw [WPFieldAssembly.ConicKernel.coeff_comp_neg, ho.neg_one_pow] at hc
    have hz : (2 : K) * P.coeff j = 0 := by linear_combination -hc
    exact ((mul_eq_zero.mp hz).resolve_left h2).symm

theorem quadraticInverse_even_pullback (P : K[X])
    (h2 : (2 : K) ≠ 0) (he : P.comp (-X) = P) :
    (quadraticInverse P).comp (1 - X ^ 2) = P := by
  have hh := even_expand_contract P h2 he
  rw [expand_eq_comp_X_pow] at hh
  rw [quadraticInverse, comp_assoc]
  simpa only [sub_comp, one_comp, X_comp, sub_sub_cancel] using hh
end EvenPolynomial

section EulerPolynomial
variable {K : Type*} [Field K]

theorem unitEuler_degree_le (p D : ℕ) (G : K[X]) (hG : G.natDegree ≤ D) :
    (unitEuler p G).natDegree ≤ D := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [unitEuler_coeff, coeff_eq_zero_of_natDegree_lt (hG.trans_lt hn)]
  split_ifs <;> simp

theorem rational_unitEuler_theta (p : ℕ) (G : ℚ[X]) (hG : G.natDegree < p) :
    X * (unitEuler p G).derivative = G - C (G.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_X_mul, coeff_derivative, unitEuler_coeff, coeff_sub, coeff_C]
      simp only [show n + 1 ≠ 0 by omega, if_false, sub_zero]
      by_cases hn : n + 1 < p
      · rw [if_pos hn]
        have hu : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hu]
        norm_num only [Nat.cast_add, Nat.cast_one]
      · rw [if_neg hn, coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
end EulerPolynomial

variable (p : ℕ) [Fact p.Prime]

noncomputable def greenHIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  unitEulerIntegral p hp (squareQIntegral p hp)
noncomputable def greenBIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  balancedFirstIntegral p hp * balancedProperIntegral p hp
noncomputable def greenUIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (2 : integralRationals p) * (greenHIntegral p hp).comp (1 - X ^ 2) +
    C (4 : integralRationals p) * (X * greenBIntegral p hp) -
    C (4 * (balancedProperIntegral p hp).eval 1)
noncomputable def greenSIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (greenUIntegral p hp)
noncomputable def greenJIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (greenSIntegral p hp).divX.comp (1 - X ^ 2)
noncomputable def greenMIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  unitEulerIntegral p hp (X * greenJIntegral p hp)

theorem greenHIntegral_value (hp : 19 ≤ p) :
    (greenHIntegral p hp).map (integralRationals p).subtype = unitEuler p (squareQ p) := by
  rw [greenHIntegral, unitEulerIntegral_value, squareQIntegral_value p hp]

theorem greenHIntegral_origin (hp : 19 ≤ p) : (greenHIntegral p hp).coeff 0 = 0 := by
  apply Subring.subtype_injective (integralRationals p)
  rw [← coeff_map, greenHIntegral_value p hp, unitEuler_coeff]
  simp

theorem greenHIntegral_degree (hp : 19 ≤ p) :
    (greenHIntegral p hp).natDegree ≤ p / 6 := by
  rw [← natDegree_map_eq_of_injective (Subring.subtype_injective (integralRationals p)) _,
    greenHIntegral_value p hp]
  exact unitEuler_degree_le p (p / 6) _ (actual_squareQ_degree p hp)

theorem greenBalancedFirst_reflect (hp : 19 ≤ p) :
    (balancedFirstIntegral p hp).comp (-X) =
      C ((-1 : integralRationals p) ^ (p / 6)) * balancedFirstIntegral p hp := by
  rw [balancedFirstIntegral, mul_comp, C_comp, scaledStar, scaledEta_eval_reflect]
  ring

theorem greenBalancedProper_reflect (hp : 19 ≤ p) :
    (balancedProperIntegral p hp).comp (-X) =
      -C ((-1 : integralRationals p) ^ (p / 6)) * balancedProperIntegral p hp := by
  rw [balancedProper_literal p hp, properEta_eval_reflect]

theorem greenBIntegral_odd (hp : 19 ≤ p) :
    (greenBIntegral p hp).comp (-X) = -greenBIntegral p hp := by
  have hs : (C ((-1 : integralRationals p) ^ (p / 6)) : (integralRationals p)[X]) ^ 2 = 1 := by
    rw [← C_pow, sign_square, C_1]
  rw [greenBIntegral, mul_comp, greenBalancedFirst_reflect p hp,
    greenBalancedProper_reflect p hp]
  linear_combination -(balancedFirstIntegral p hp * balancedProperIntegral p hp) * hs

theorem greenBIntegral_degree (hp : 19 ≤ p) :
    (greenBIntegral p hp).natDegree ≤ 2 * (p / 6) - 1 := by
  have hh := natDegree_mul_le_of_le (balancedFirstIntegral_degree p hp)
    (balancedProper_degree p hp)
  change (greenBIntegral p hp).natDegree ≤ p / 6 + (p / 6 - 1) at hh
  omega

theorem greenUIntegral_even (hp : 19 ≤ p) :
    (greenUIntegral p hp).comp (-X) = greenUIntegral p hp := by
  simp only [greenUIntegral, add_comp, sub_comp, mul_comp, C_comp, X_comp,
    comp_assoc, sub_comp, one_comp, pow_comp, greenBIntegral_odd p hp]
  ring

theorem greenUIntegral_endpoint (hp : 19 ≤ p) : (greenUIntegral p hp).eval 1 = 0 := by
  have hH : (greenHIntegral p hp).eval 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero] using greenHIntegral_origin p hp
  simp [greenUIntegral, greenBIntegral, eval_comp, hH, balancedFirstIntegral_endpoint p hp]

theorem greenUIntegral_degree (hp : 19 ≤ p) :
    (greenUIntegral p hp).natDegree ≤ 2 * (p / 6) := by
  let d := p / 6
  have hq : (1 - X ^ 2 : (integralRationals p)[X]).natDegree ≤ 2 := by compute_degree
  have hHT : ((greenHIntegral p hp).comp (1 - X ^ 2)).natDegree ≤ 2 * d :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (greenHIntegral_degree p hp) hq).trans
      (by dsimp [d]; omega))
  have hH : (C (2 : integralRationals p) *
      (greenHIntegral p hp).comp (1 - X ^ 2)).natDegree ≤ 2 * d :=
    (natDegree_C_mul_le _ _).trans hHT
  have hXB : (X * greenBIntegral p hp).natDegree ≤ 2 * d :=
    (natDegree_mul_le_of_le natDegree_X_le (greenBIntegral_degree p hp)).trans
      (by dsimp [d]; omega)
  have hB : (C (4 : integralRationals p) * (X * greenBIntegral p hp)).natDegree ≤ 2 * d :=
    (natDegree_C_mul_le _ _).trans hXB
  have hC : (C (4 * (balancedProperIntegral p hp).eval 1)).natDegree ≤ 2 * d := by
    rw [natDegree_C]
    exact Nat.zero_le _
  have hsum : (C (2 : integralRationals p) *
      (greenHIntegral p hp).comp (1 - X ^ 2) +
      C (4 : integralRationals p) * (X * greenBIntegral p hp)).natDegree ≤ 2 * d := by
    simpa only [max_self] using natDegree_add_le_of_le hH hB
  simpa only [greenUIntegral, max_self] using natDegree_sub_le_of_le hsum hC

theorem greenJIntegral_data (hp : 19 ≤ p) :
    (1 - X ^ 2) * greenJIntegral p hp = greenUIntegral p hp ∧
      (greenJIntegral p hp).natDegree ≤ 2 * (p / 6) - 2 ∧
      (greenJIntegral p hp).comp (-X) = greenJIntegral p hp := by
  let d := p / 6
  let q : (integralRationals p)[X] := 1 - X ^ 2
  let U := greenUIntegral p hp
  let S := greenSIntegral p hp
  let J := greenJIntegral p hp
  have h2 : (2 : integralRationals p) ≠ 0 := by
    exact_mod_cast (by norm_num : (2 : ℚ) ≠ 0)
  have hSc : S.comp q = U := quadraticInverse_even_pullback U h2 (greenUIntegral_even p hp)
  have hS0 : S.coeff 0 = 0 := by
    have he := congrArg (fun P : (integralRationals p)[X] => P.eval 1) hSc
    simpa only [eval_comp, q, eval_sub, eval_one, eval_pow, eval_X, one_pow,
      sub_self, ← coeff_zero_eq_eval_zero, U, greenUIntegral_endpoint p hp] using he
  have hdiv : X * S.divX = S := by
    simpa only [hS0, map_zero, add_zero] using X_mul_divX_add S
  have hJ : q * J = U := by
    have he := congrArg (fun P : (integralRationals p)[X] => P.comp q) hdiv
    simpa only [mul_comp, X_comp, J, greenJIntegral, S, hSc] using he
  have hSd : S.natDegree ≤ d :=
    quadraticInverse_degree_of_le U d (greenUIntegral_degree p hp)
  have hqd : q.natDegree ≤ 2 := by dsimp [q]; compute_degree
  have hJd : J.natDegree ≤ 2 * d - 2 :=
    natDegree_comp_le.trans ((Nat.mul_le_mul
      (show S.divX.natDegree ≤ d - 1 by rw [natDegree_divX_eq_natDegree_tsub_one]; omega)
      hqd).trans (by
        have hd : 3 ≤ d := by dsimp [d]; omega
        omega))
  have hJe : J.comp (-X) = J := by
    simp only [J, greenJIntegral, comp_assoc, sub_comp, one_comp, pow_comp, X_comp]
    congr 1
    ring
  exact ⟨hJ, hJd, hJe⟩

theorem greenMIntegral_value (hp : 19 ≤ p) :
    (greenMIntegral p hp).map (integralRationals p).subtype =
      unitEuler p (X * (greenJIntegral p hp).map (integralRationals p).subtype) := by
  rw [greenMIntegral, unitEulerIntegral_value, Polynomial.map_mul, Polynomial.map_X]

theorem greenMIntegral_derivative (hp : 19 ≤ p) :
    (greenMIntegral p hp).derivative = greenJIntegral p hp := by
  apply polynomial_subtype_injective p
  change ((greenMIntegral p hp).derivative).map (integralRationals p).subtype =
    (greenJIntegral p hp).map (integralRationals p).subtype
  rw [← Polynomial.derivative_map, greenMIntegral_value p hp]
  let J := (greenJIntegral p hp).map (integralRationals p).subtype
  have hJd : J.natDegree ≤ 2 * (p / 6) - 2 :=
    natDegree_map_le.trans (greenJIntegral_data p hp).2.1
  have hGd : (X * J).natDegree < p := by
    have hh := natDegree_mul_le_of_le natDegree_X_le hJd
    have h6 := Nat.div_mul_le_self p 6
    omega
  have ht := rational_unitEuler_theta p (X * J) hGd
  simp only [coeff_X_mul_zero, C_0, sub_zero] at ht
  exact mul_left_cancel₀ (X_ne_zero : (X : ℚ[X]) ≠ 0) ht

theorem greenMIntegral_degree (hp : 19 ≤ p) :
    (greenMIntegral p hp).natDegree ≤ 2 * (p / 6) - 1 := by
  rw [← natDegree_map_eq_of_injective (Subring.subtype_injective (integralRationals p)) _,
    greenMIntegral_value p hp]
  apply unitEuler_degree_le
  exact (natDegree_mul_le_of_le natDegree_X_le
    (natDegree_map_le.trans (greenJIntegral_data p hp).2.1)).trans (by omega)

theorem greenMIntegral_origin (hp : 19 ≤ p) : (greenMIntegral p hp).coeff 0 = 0 := by
  apply Subring.subtype_injective (integralRationals p)
  rw [← coeff_map, greenMIntegral_value p hp, unitEuler_coeff]
  simp

theorem greenMIntegral_odd (hp : 19 ≤ p) :
    (greenMIntegral p hp).comp (-X) = -greenMIntegral p hp := by
  apply polynomial_subtype_injective p
  change ((greenMIntegral p hp).comp (-X)).map (integralRationals p).subtype =
    (-greenMIntegral p hp).map (integralRationals p).subtype
  simp only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]
  rw [greenMIntegral_value p hp]
  let J := (greenJIntegral p hp).map (integralRationals p).subtype
  have hJe : J.comp (-X) = J := by
    have he := congrArg (Polynomial.map (integralRationals p).subtype)
      (greenJIntegral_data p hp).2.2
    simpa only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using he
  have hGe : (X * J).comp (-X) = -(X * J) := by
    rw [mul_comp, X_comp, hJe]
    ring
  ext n
  have hn := congrArg (fun P : ℚ[X] => P.coeff n) hGe
  rw [WPFieldAssembly.ConicKernel.coeff_comp_neg, coeff_neg] at hn
  simp only [WPFieldAssembly.ConicKernel.coeff_comp_neg, coeff_neg, unitEuler_coeff]
  split_ifs
  · linear_combination (n : ℚ)⁻¹ * hn
  · simp

/-- SB81a with its actual integral normalization and every polynomial part. -/
theorem actual_green_M_source (hp : 19 ≤ p) :
    (1 - X ^ 2) * (greenMIntegral p hp).derivative =
      C (2 : integralRationals p) * (greenHIntegral p hp).comp (1 - X ^ 2) +
        C (4 : integralRationals p) *
          (X * balancedFirstIntegral p hp * balancedProperIntegral p hp) -
        C (4 * (balancedProperIntegral p hp).eval 1) := by
  rw [greenMIntegral_derivative p hp]
  have he := (greenJIntegral_data p hp).1
  simpa only [greenUIntegral, greenBIntegral, mul_assoc] using he

theorem balancedProper_field (hp : 19 ≤ p) :
    (balancedProperIntegral p hp).map (residueHom p) = properLegendreJacobi p := by
  have he := congrArg (Polynomial.map (residueHom p)) (actual_proper_increment_source p hp)
  have hp0 : (p : (ZMod p)[X]) = 0 := by
    have he := congrArg (Polynomial.C : ZMod p →+* (ZMod p)[X]) (ZMod.natCast_self p)
    simpa only [map_natCast, map_zero] using he
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_natCast, map_natCast, hp0, zero_mul, add_zero,
    integralProperJacobi_field] using he

theorem greenHIntegral_field (hp : 19 ≤ p) :
    (greenHIntegral p hp).map (residueHom p) = ActualLowEuler.actualH p := by
  rw [greenHIntegral, unitEulerIntegral_field, squareQIntegral,
    ← balancedFirstIntegral_eq_rankIntegral p hp, quadraticInverse_map,
    Polynomial.map_pow, balancedFirstIntegral_field]
  rfl

theorem greenHIntegral_field_native (hp : 19 ≤ p) :
    (greenHIntegral p hp).map (residueHom p) = nativeHField p := by
  rw [greenHIntegral_field p hp, ActualLowEuler.actualH,
    unitEuler_field_eq p _ ((ActualLowEuler.actualF_degree p hp).trans_lt (by omega)),
    ActualLowEuler.actualF_eq_native p hp]
  rfl

theorem greenUIntegral_field (hp : 19 ≤ p) :
    (greenUIntegral p hp).map (residueHom p) = ActualFirstGreen.U p := by
  have hn : residueHom p ((balancedProperIntegral p hp).eval 1) =
      -fieldHarmonic p (p / 6) := by
    rw [← eval_map_apply, balancedProper_field p hp, map_one,
      properLegendreJacobi_endpoint_one]
  simp only [greenUIntegral, greenBIntegral, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat, map_mul, map_ofNat,
    greenHIntegral_field_native,
    balancedFirstIntegral_field, balancedProper_field, hn]
  unfold ActualFirstGreen.U ActualFirstGreen.B
  simp only [map_neg]
  ring

theorem greenJIntegral_field (hp : 19 ≤ p) :
    (greenJIntegral p hp).map (residueHom p) = ActualFirstGreen.J p := by
  rw [greenJIntegral, Polynomial.map_comp, divX_map_local, greenSIntegral,
    quadraticInverse_map, greenUIntegral_field p hp]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rfl

/-- The integral primitive reduces to the existing canonical M. -/
theorem greenMIntegral_field (hp : 19 ≤ p) :
    (greenMIntegral p hp).map (residueHom p) = ActualFirstGreen.M p := by
  have hJd : (ActualFirstGreen.J p).natDegree ≤ 2 * (p / 6) - 2 := by
    rw [← greenJIntegral_field p hp]
    exact natDegree_map_le.trans (greenJIntegral_data p hp).2.1
  have hGd : (X * ActualFirstGreen.J p).natDegree < p := by
    have hh := natDegree_mul_le_of_le natDegree_X_le hJd
    have h6 := Nat.div_mul_le_self p 6
    omega
  rw [greenMIntegral, unitEulerIntegral_field, Polynomial.map_mul, Polynomial.map_X,
    greenJIntegral_field p hp, unitEuler_field_eq p _ hGd]
  rfl

noncomputable def cubicTIntegral : (integralRationals p)[X] := 4 * X ^ 3 - 3 * X

theorem cubicTIntegral_value :
    (cubicTIntegral p).map (integralRationals p).subtype = (WPFiniteCubicLog.Tc : ℚ[X]) := by
  simp [cubicTIntegral, WPFiniteCubicLog.Tc]

theorem cubicTIntegral_field :
    (cubicTIntegral p).map (residueHom p) = (WPFiniteCubicLog.Tc : (ZMod p)[X]) := by
  simp [cubicTIntegral, WPFiniteCubicLog.Tc]

noncomputable def greenCoordinateIntegral : (integralRationals p)[X] :=
  C (smallIntegralInverse p 5) * (X + 1)
noncomputable def greenCMtIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (smallIntegralInverse p 5) * X ^ p * (greenMIntegral p hp).comp (cubicTIntegral p)
noncomputable def greenCMIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (contract 2 (greenCMtIntegral p hp)).comp (greenCoordinateIntegral p)

theorem greenCoordinateIntegral_field (hp : 19 ≤ p) :
    (greenCoordinateIntegral p).map (residueHom p) =
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]) := by
  simp only [greenCoordinateIntegral, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    smallIntegralInverse_field p 5 (by omega) (by omega), WPFiniteWSource.squaredCoordinate]
  rfl

theorem greenCMtIntegral_value (hp : 19 ≤ p) :
    (greenCMtIntegral p hp).map (integralRationals p).subtype =
      C (1 / 5 : ℚ) * X ^ p * ((greenMIntegral p hp).map
        (integralRationals p).subtype).comp (WPFiniteCubicLog.Tc : ℚ[X]) := by
  simp only [greenCMtIntegral, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_comp,
    cubicTIntegral_value]
  rw [show (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) from
    smallIntegralInverse_value p 5 (by omega) (by omega)]

theorem greenCMtIntegral_field (hp : 19 ≤ p) :
    (greenCMtIntegral p hp).map (residueHom p) = C (2 : ZMod p) * ActualFirstGreen.CMt p := by
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h10 : (10 : ZMod p) ≠ 0 := small_cast_ne_zero p 10 (by omega) (by omega)
  have hc : (5 : ZMod p)⁻¹ = 2 * (10 : ZMod p)⁻¹ := by
    field_simp [h5, h10]
    ring
  simp only [greenCMtIntegral, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_comp,
    cubicTIntegral_field, greenMIntegral_field,
    smallIntegralInverse_field p 5 (by omega) (by omega)]
  norm_num only [Nat.cast_ofNat]
  rw [hc]
  unfold ActualFirstGreen.CMt
  simp only [one_div, map_mul, C_ofNat]
  ring

/-- SB81 uses 1/5; the existing field CM uses 1/10. -/
theorem greenCMIntegral_field (hp : 19 ≤ p) :
    (greenCMIntegral p hp).map (residueHom p) = C (2 : ZMod p) * ActualFirstGreen.CM p := by
  rw [greenCMIntegral, Polynomial.map_comp, map_contract (by norm_num : (2 : ℕ) ≠ 0),
    greenCMtIntegral_field p hp, greenCoordinateIntegral_field p hp,
    WPFieldAssembly.ActualNC77Chart.contract_C_mul, mul_comp, C_comp]
  rfl

/-- Retain the characteristic-zero p term before reducing or dividing the Green source. -/
theorem actual_green_CMt_derivative (hp : 19 ≤ p) :
    ((greenCMtIntegral p hp).map (integralRationals p).subtype).derivative =
      C (1 / 5 : ℚ) * (C (p : ℚ) * X ^ (p - 1) *
        ((greenMIntegral p hp).map (integralRationals p).subtype).comp (WPFiniteCubicLog.Tc : ℚ[X]) +
        3 * X ^ p * (4 * X ^ 2 - 1) *
          (((greenMIntegral p hp).map (integralRationals p).subtype).derivative).comp
            (WPFiniteCubicLog.Tc : ℚ[X])) := by
  have hT : (WPFiniteCubicLog.Tc : ℚ[X]).derivative = 3 * (4 * X ^ 2 - 1) := by
    simp [WPFiniteCubicLog.Tc]
    norm_num only [C_ofNat]
    ring
  rw [greenCMtIntegral_value p hp]
  simp only [derivative_mul, derivative_C, derivative_X_pow,
    derivative_comp, hT, zero_mul, zero_add]
  ring

noncomputable def greenConicQ (_p : ℕ) : ℚ[X] := 5 * X ^ 2 - 1
noncomputable def greenCoordinateQ (_p : ℕ) : ℚ[X] := C (1 / 5 : ℚ) * (X + 1)
noncomputable def greenMq (hp : 19 ≤ p) : ℚ[X] :=
  (greenMIntegral p hp).map (integralRationals p).subtype
noncomputable def greenBq (hp : 19 ≤ p) : ℚ[X] :=
  (greenBIntegral p hp).map (integralRationals p).subtype
noncomputable def greenHq (hp : 19 ≤ p) : ℚ[X] :=
  (greenHIntegral p hp).map (integralRationals p).subtype
noncomputable def greenCMq (hp : 19 ≤ p) : ℚ[X] :=
  (greenCMIntegral p hp).map (integralRationals p).subtype
noncomputable def greenCBq (hp : 19 ≤ p) : ℚ[X] :=
  (contract 2 (C (1 / 5 : ℚ) * X ^ p *
    (greenBq p hp).comp (WPFiniteCubicLog.Tc : ℚ[X]))).comp (greenCoordinateQ p)
noncomputable def greenHbarq (hp : 19 ≤ p) : ℚ[X] :=
  (greenHq p hp).comp WPActualPullbackSource.Vpolynomial -
    C (2 * (integralRationals p).subtype ((balancedProperIntegral p hp).eval 1))

omit [Fact p.Prime] in
theorem greenCoordinateQ_conic :
    (greenCoordinateQ p).comp (greenConicQ p) = (X ^ 2 : ℚ[X]) := by
  have hc : (C (1 / 5 : ℚ) : ℚ[X]) * 5 = 1 := by
    change C (1 / 5 : ℚ) * C 5 = C 1
    rw [← C_mul]
    norm_num
  simp only [greenCoordinateQ, greenConicQ, mul_comp, C_comp,
    add_comp, X_comp, one_comp]
  linear_combination X ^ 2 * hc

theorem greenCMIntegral_value (hp : 19 ≤ p) :
    greenCMq p hp = (contract 2
      (C (1 / 5 : ℚ) * X ^ p * (greenMq p hp).comp
        (WPFiniteCubicLog.Tc : ℚ[X]))).comp (greenCoordinateQ p) := by
  rw [greenCMq, greenCMIntegral, Polynomial.map_comp,
    map_contract (by norm_num : (2 : ℕ) ≠ 0), greenCMtIntegral_value p hp]
  congr 1
  simp only [greenCoordinateIntegral, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
  rw [show (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) from
    smallIntegralInverse_value p 5 (by omega) (by omega)]
  rfl

private theorem green_carrier_even_Q (hp : 19 ≤ p) (P : ℚ[X])
    (hP : P.comp (-X) = -P) :
    (C (1 / 5 : ℚ) * X ^ p * P.comp (WPFiniteCubicLog.Tc : ℚ[X])).comp (-X) =
      C (1 / 5 : ℚ) * X ^ p * P.comp (WPFiniteCubicLog.Tc : ℚ[X]) := by
  have ht : (WPFiniteCubicLog.Tc : ℚ[X]).comp (-X) =
      (-X).comp (WPFiniteCubicLog.Tc : ℚ[X]) := by
    simp [WPFiniteCubicLog.Tc, mul_comp, sub_comp, pow_comp]
    ring
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [comp_assoc, ht, ← comp_assoc, hP, neg_comp,
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)).neg_pow]
  ring

theorem greenMq_odd (hp : 19 ≤ p) :
    (greenMq p hp).comp (-X) = -greenMq p hp := by
  have he := congrArg (Polynomial.map (integralRationals p).subtype)
    (greenMIntegral_odd p hp)
  simpa only [greenMq, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using he

theorem greenBq_odd (hp : 19 ≤ p) :
    (greenBq p hp).comp (-X) = -greenBq p hp := by
  have he := congrArg (Polynomial.map (integralRationals p).subtype)
    (greenBIntegral_odd p hp)
  simpa only [greenBq, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using he

private theorem even_descent_Q (P : ℚ[X]) (hP : P.comp (-X) = P) :
    (contract 2 P).comp (X ^ 2) = P := by
  have he := even_expand_contract P (by norm_num : (2 : ℚ) ≠ 0) hP
  rw [expand_eq_comp_X_pow] at he
  exact he

theorem green_actual_carrier_pullbacks_Q (hp : 19 ≤ p) :
    (greenCMq p hp).comp (greenConicQ p) =
        (greenCMtIntegral p hp).map (integralRationals p).subtype ∧
      (greenCBq p hp).comp (greenConicQ p) =
        C (1 / 5 : ℚ) * X ^ p * (greenBq p hp).comp
          (WPFiniteCubicLog.Tc : ℚ[X]) := by
  constructor
  · rw [greenCMIntegral_value p hp, comp_assoc, greenCoordinateQ_conic,
      greenCMtIntegral_value p hp]
    exact even_descent_Q _ (green_carrier_even_Q p hp _ (greenMq_odd p hp))
  · rw [greenCBq, comp_assoc, greenCoordinateQ_conic]
    exact even_descent_Q _ (green_carrier_even_Q p hp _ (greenBq_odd p hp))

/-- The p*CM term is retained over Q before division or reduction. -/
theorem actual_green_CM_cleared_Q (hp : 19 ≤ p) :
    10 * greenCoordinateQ p * (WPFiniteZSource.Abar : ℚ[X]) *
        (greenCMq p hp).derivative =
      30 * (greenCoordinateQ p) ^ (((p - 1) / 2) + 1) * greenHbarq p hp +
        C (p : ℚ) * (WPFiniteZSource.Abar : ℚ[X]) * greenCMq p hp +
        60 * greenCoordinateQ p * (4 * X - 11) * greenCBq p hp := by
  let q : ℚ[X] := 1 - X ^ 2
  let b : ℚ[X] := 4 * X ^ 2 - 1
  let c : ℚ[X] := 4 * X ^ 2 - 3
  let T : ℚ[X] := WPFiniteCubicLog.Tc
  have hT : T = X * c := by dsimp [T, WPFiniteCubicLog.Tc, c]; ring
  have hqT : 1 - T ^ 2 = q * b ^ 2 := by
    dsimp [T, WPFiniteCubicLog.Tc, q, b]
    ring
  have hV : WPActualPullbackSource.Vpolynomial.comp (greenConicQ p) = 1 - T ^ 2 := by
    have h125 : (125 : ℚ[X]) * C (1 / 125 : ℚ) = 1 := by
      change C (125 : ℚ) * C (1 / 125 : ℚ) = C 1
      rw [← C_mul]
      norm_num
    simp [WPActualPullbackSource.Vpolynomial, greenConicQ,
      T, WPFiniteCubicLog.Tc, mul_comp, sub_comp, pow_comp]
    simp only [one_div] at h125
    linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * h125
  have hA : (WPFiniteZSource.Abar : ℚ[X]).comp (greenConicQ p) = 25 * q * b := by
    simp [WPFiniteZSource.Abar, greenConicQ, q, b, mul_comp, sub_comp]
    ring
  have hl : (4 * X - 11 : ℚ[X]).comp (greenConicQ p) = 5 * c := by
    simp [greenConicQ, c, mul_comp, sub_comp]
    ring
  have hcd : (greenConicQ p).derivative = 10 * X := by
    simp [greenConicQ, derivative_pow_succ]
    ring
  have hu5 : (5 : ℚ[X]) * C (1 / 5 : ℚ) = 1 := by
    change C (5 : ℚ) * C (1 / 5 : ℚ) = C 1
    rw [← C_mul]
    norm_num
  obtain ⟨hCM, hCB⟩ := green_actual_carrier_pullbacks_Q p hp
  have hd := congrArg Polynomial.derivative hCM
  rw [derivative_comp, hcd, actual_green_CMt_derivative p hp] at hd
  have hd50 : 50 * X * (greenCMq p hp).derivative.comp (greenConicQ p) =
      C (p : ℚ) * X ^ (p - 1) * (greenMq p hp).comp T +
        3 * X ^ p * b * ((greenMq p hp).derivative).comp T := by
    dsimp [greenMq, T, b]
    linear_combination 5 * hd +
      (C (p : ℚ) * X ^ (p - 1) *
        ((greenMIntegral p hp).map (integralRationals p).subtype).comp WPFiniteCubicLog.Tc +
        3 * X ^ p * (4 * X ^ 2 - 1) *
          (((greenMIntegral p hp).map (integralRationals p).subtype).derivative).comp
            WPFiniteCubicLog.Tc) * hu5
  have hCM5 : 5 * (greenCMq p hp).comp (greenConicQ p) =
      X ^ p * (greenMq p hp).comp T := by
    rw [hCM, greenCMtIntegral_value p hp]
    dsimp [greenMq, T]
    linear_combination
      X ^ p * ((greenMIntegral p hp).map (integralRationals p).subtype).comp
        WPFiniteCubicLog.Tc * hu5
  have hCB5 : 5 * (greenCBq p hp).comp (greenConicQ p) =
      X ^ p * (greenBq p hp).comp T := by
    rw [hCB]
    dsimp [T]
    linear_combination X ^ p * (greenBq p hp).comp WPFiniteCubicLog.Tc * hu5
  have hsrc := congrArg (Polynomial.map (integralRationals p).subtype)
    (actual_green_M_source p hp)
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat, ← Polynomial.derivative_map,
    map_mul, map_ofNat] at hsrc
  have hjc : q * b ^ 2 * ((greenMq p hp).derivative).comp T =
      2 * (greenHbarq p hp).comp (greenConicQ p) +
        4 * T * (greenBq p hp).comp T := by
    have he := congrArg (fun P : ℚ[X] => P.comp T) hsrc
    simp only [mul_comp, add_comp, sub_comp, C_comp, pow_comp, one_comp,
      X_comp, ofNat_comp, comp_assoc] at he
    simp only [Subring.subtype_apply] at he
    dsimp [greenHbarq, greenMq, greenHq, greenBq, greenBIntegral]
    simp only [Polynomial.map_mul, sub_comp, mul_comp, C_comp, comp_assoc, hV,
      map_mul, C_ofNat, ofNat_comp]
    rw [← hqT]
    linear_combination he
  have hpow : ((greenCoordinateQ p) ^ (((p - 1) / 2) + 1)).comp (greenConicQ p) =
      X ^ p * X := by
    rw [pow_comp, greenCoordinateQ_conic, ← pow_mul]
    have hh := WPFiniteWSource.half_exponent p hp
    rw [show 2 * (((p - 1) / 2) + 1) = p + 1 by omega, pow_succ]
  have hx : (X : ℚ[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hx2 : (X : ℚ[X]) ^ 2 * X ^ (p - 1) = X * X ^ p := by
    linear_combination X * hx
  let E : ℚ[X] := 10 * greenCoordinateQ p * WPFiniteZSource.Abar *
      (greenCMq p hp).derivative -
    30 * (greenCoordinateQ p) ^ (((p - 1) / 2) + 1) * greenHbarq p hp -
    C (p : ℚ) * WPFiniteZSource.Abar * greenCMq p hp -
    60 * greenCoordinateQ p * (4 * X - 11) * greenCBq p hp
  have he : E.comp (greenConicQ p) * (10 * X) = 0 := by
    simp only [E, sub_comp, mul_comp, ofNat_comp, C_comp,
      greenCoordinateQ_conic, hA, hl, hpow]
    calc
      _ = 50 * X ^ 2 * q * b *
            (50 * X * (greenCMq p hp).derivative.comp (greenConicQ p)) -
          300 * X ^ 2 * X ^ p * (greenHbarq p hp).comp (greenConicQ p) -
          50 * C (p : ℚ) * X * q * b *
            (5 * (greenCMq p hp).comp (greenConicQ p)) -
          600 * X ^ 3 * c * (5 * (greenCBq p hp).comp (greenConicQ p)) := by ring
      _ = 150 * X ^ 2 * X ^ p *
            (q * b ^ 2 * ((greenMq p hp).derivative).comp T -
              2 * (greenHbarq p hp).comp (greenConicQ p) -
              4 * T * (greenBq p hp).comp T) +
          50 * C (p : ℚ) * q * b * (greenMq p hp).comp T *
            (X ^ 2 * X ^ (p - 1) - X * X ^ p) := by
        rw [hd50, hCM5, hCB5, hT]
        ring
      _ = 0 := by rw [hjc, hx2]; ring
  have hec : E.comp (greenConicQ p) = 0 :=
    (mul_eq_zero.mp he).resolve_right (by
      exact mul_ne_zero (by norm_num : (10 : ℚ[X]) ≠ 0) X_ne_zero)
  have hcdeg : (greenConicQ p).natDegree = 2 := by
    unfold greenConicQ
    compute_degree; norm_num
  have he0 : E = 0 := WPFieldAssembly.ConicKernel.comp_injective_nonconstant
    (greenConicQ p) (by rw [hcdeg]; norm_num)
      (by simpa only [zero_comp] using hec)
  dsimp [E] at he0
  linear_combination he0

section OddQuotient
variable {K : Type*} [CommRing K] [IsDomain K]

theorem odd_divX_even (P : K[X]) (h0 : P.coeff 0 = 0)
    (he : P.comp (-X) = -P) : P.divX.comp (-X) = P.divX := by
  have hd : X * P.divX = P := by
    simpa only [h0, map_zero, add_zero] using X_mul_divX_add P
  have hr := congrArg (fun Q : K[X] => Q.comp (-X)) hd
  simp only [mul_comp, X_comp, he] at hr
  apply mul_left_cancel₀ (neg_ne_zero.mpr (X_ne_zero : (X : K[X]) ≠ 0))
  linear_combination hr + hd
end OddQuotient

noncomputable def greenPMIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (greenMIntegral p hp).divX

theorem greenPMIntegral_source (hp : 19 ≤ p) :
    greenMIntegral p hp = X * (greenPMIntegral p hp).comp (1 - X ^ 2) := by
  have h2 : (2 : integralRationals p) ≠ 0 := by
    exact_mod_cast (by norm_num : (2 : ℚ) ≠ 0)
  rw [greenPMIntegral, quadraticInverse_even_pullback _ h2
    (odd_divX_even _ (greenMIntegral_origin p hp) (greenMIntegral_odd p hp))]
  symm
  simpa only [greenMIntegral_origin p hp, map_zero, add_zero] using
    X_mul_divX_add (greenMIntegral p hp)

theorem greenPMIntegral_degree (hp : 19 ≤ p) :
    (greenPMIntegral p hp).natDegree ≤ p / 6 - 1 := by
  apply quadraticInverse_degree_of_le
  rw [natDegree_divX_eq_natDegree_tsub_one]
  have hm := greenMIntegral_degree p hp
  have hd : 3 ≤ p / 6 := by omega
  omega

noncomputable def greenOriginMetricFactor (_hp : 19 ≤ p) : integralRationals p :=
  smallIntegralInverse p 2 * smallIntegralInverse p 5 ^ 3 *
    smallIntegralInverse p 5 ^ (((p - 1) / 2) + p - 1)

noncomputable def greenOriginMetricNumerator (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (X + 1) ^ ((p - 1) / 2) * (4 - 11 * X) ^ (p - 1) *
    (4 * X - 11) * (11 * X ^ 2 + 4 * X + 8) *
    (greenPMIntegral p hp).comp (WPHasseIntegralTransport.integralV p (by omega))

noncomputable def greenOriginMetricIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(greenOriginMetricFactor p hp) * (greenOriginMetricNumerator p hp).coeff p

noncomputable def greenOriginMetricQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  -LaurentPolynomial.C (greenOriginMetricFactor p hp).val *
    LaurentPolynomial.T (-((p + 1 : ℕ) : ℤ)) *
    ((greenOriginMetricNumerator p hp).map (integralRationals p).subtype).toLaurent

theorem greenOriginMetricIntegral_value (hp : 19 ≤ p) :
    (greenOriginMetricIntegral p hp).val = (greenOriginMetricQ p hp).coeff (-1) := by
  rw [greenOriginMetricQ]
  have hs := WPFiniteJCarrier.shifted_coeff
    (-(greenOriginMetricFactor p hp).val) (-((p + 1 : ℕ) : ℤ)) (-1)
    ((greenOriginMetricNumerator p hp).map (integralRationals p).subtype).toLaurent
  rw [show (-1 : ℤ) - -((p + 1 : ℕ) : ℤ) = (p : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat, coeff_map] at hs
  change -(greenOriginMetricFactor p hp).val *
    (integralRationals p).subtype ((greenOriginMetricNumerator p hp).coeff p) = _
  simpa only [map_neg, mul_comm, mul_left_comm, mul_assoc] using hs.symm

theorem greenOriginMetricIntegral_field (hp : 19 ≤ p) :
    residueHom p (greenOriginMetricIntegral p hp) =
      -residueHom p (greenOriginMetricFactor p hp) *
        ((greenOriginMetricNumerator p hp).map (residueHom p)).coeff p := by
  simp only [greenOriginMetricIntegral, map_mul, map_neg, coeff_map]

theorem greenPMIntegral_field (hp : 19 ≤ p) :
    (greenPMIntegral p hp).map (residueHom p) =
      quadraticInverse (ActualFirstGreen.M p).divX := by
  rw [greenPMIntegral, quadraticInverse_map, divX_map_local, greenMIntegral_field p hp]

section ExactMetricDensity
variable {K : Type*} [Field K] [CharZero K]

theorem Zvee_derivative_scalar (x t : K) (hx : x ≠ 0) (ht : t ≠ 0)
    (hs : 5 * t ^ 2 = x + 1) :
    (1 / (10 * t)) * (4 - 11 * x) / (5 * x) - 4 * t / (5 * x ^ 2) =
      -(11 * x ^ 2 + 4 * x + 8) / (50 * t * x ^ 2) := by
  calc
    _ = ((4 - 11 * x) * x - 40 * t ^ 2) / (50 * t * x ^ 2) := by
      field_simp [hx, ht]
      ring
    _ = _ := by
      congr 1
      linear_combination -8 * hs

theorem Z_derivative_scalar (x t w : K) (hx : x ≠ 0) (ht : t ≠ 0) (hw : w ≠ 0)
    (hs : 5 * t ^ 2 = x + 1) :
    3 * (4 * x - 1) / (50 * t * w) - t * (4 * x - 11) / (10 * x * w) =
      (8 * x ^ 2 + 4 * x + 11) / (50 * t * x * w) := by
  calc
    _ = (3 * x * (4 * x - 1) - 5 * t ^ 2 * (4 * x - 11)) /
        (50 * t * x * w) := by
      field_simp [hx, ht, hw]
      ring
    _ = _ := by
      congr 1
      linear_combination -(4 * x - 11) * hs

theorem actual_origin_metric_density_scalar (N : ℕ) (x t m : K)
    (hx : x ≠ 0) (ht : t ≠ 0) (hs : t ^ 2 = (x + 1) / 5) :
    (t * (4 * x - 11) / 5 * m) *
        (t * (4 - 11 * x) / (5 * x)) ^ (2 * N) *
        (-(11 * x ^ 2 + 4 * x + 8) / (50 * t * x ^ 2)) =
      -((x + 1) / 5) ^ N * (4 - 11 * x) ^ (2 * N) *
        (4 * x - 11) * (11 * x ^ 2 + 4 * x + 8) * m /
          (250 * 5 ^ (2 * N) * x ^ (2 * N) * x ^ 2) := by
  have hp : (t * (4 - 11 * x) / (5 * x)) ^ (2 * N) =
      ((x + 1) / 5) ^ N * (4 - 11 * x) ^ (2 * N) /
        (5 ^ (2 * N) * x ^ (2 * N)) := by
    rw [div_pow, mul_pow, mul_pow,
      show t ^ (2 * N) = (t ^ 2) ^ N by rw [pow_mul], hs]
  have hc : (t * (4 * x - 11) / 5 * m) *
      (-(11 * x ^ 2 + 4 * x + 8) / (50 * t * x ^ 2)) =
      -(4 * x - 11) * (11 * x ^ 2 + 4 * x + 8) * m / (250 * x ^ 2) := by
    field_simp [hx, ht]
    ring
  calc
    _ = ((t * (4 * x - 11) / 5 * m) *
        (-(11 * x ^ 2 + 4 * x + 8) / (50 * t * x ^ 2))) *
          (t * (4 - 11 * x) / (5 * x)) ^ (2 * N) := by ring
    _ = _ := by
      rw [hc, hp]
      field_simp [hx, pow_ne_zero (2 * N) hx]

theorem actual_infinity_metric_density_scalar (N : ℕ) (x t w m : K)
    (hx : x ≠ 0) (ht : t ≠ 0) (hw : w ≠ 0)
    (hs : t ^ 2 = (x + 1) / 5) (hwx : w ^ 2 = x) :
    (t * (4 - 11 * x) / (5 * x * w) * m) *
        (t * (4 * x - 11) / (5 * w)) ^ (2 * N) *
        ((8 * x ^ 2 + 4 * x + 11) / (50 * t * x * w)) =
      ((x + 1) / 5) ^ N * (4 * x - 11) ^ (2 * N) *
        (4 - 11 * x) * (8 * x ^ 2 + 4 * x + 11) * m /
          (250 * 5 ^ (2 * N) * x ^ N * x ^ 3) := by
  have hp : (t * (4 * x - 11) / (5 * w)) ^ (2 * N) =
      ((x + 1) / 5) ^ N * (4 * x - 11) ^ (2 * N) /
        (5 ^ (2 * N) * x ^ N) := by
    rw [div_pow, mul_pow, mul_pow,
      show t ^ (2 * N) = (t ^ 2) ^ N by rw [pow_mul],
      show w ^ (2 * N) = (w ^ 2) ^ N by rw [pow_mul], hs, hwx]
  have hc : (t * (4 - 11 * x) / (5 * x * w) * m) *
      ((8 * x ^ 2 + 4 * x + 11) / (50 * t * x * w)) =
      (4 - 11 * x) * (8 * x ^ 2 + 4 * x + 11) * m / (250 * x ^ 3) := by
    calc
      _ = (4 - 11 * x) * (8 * x ^ 2 + 4 * x + 11) * m /
          (250 * x ^ 2 * w ^ 2) := by
        field_simp [hx, ht, hw]
        ring
      _ = _ := by
        rw [hwx]
        congr 1
        ring
  calc
    _ = ((t * (4 - 11 * x) / (5 * x * w) * m) *
        ((8 * x ^ 2 + 4 * x + 11) / (50 * t * x * w))) *
          (t * (4 * x - 11) / (5 * w)) ^ (2 * N) := by ring
    _ = _ := by
      rw [hc, hp]
      field_simp [hx, pow_ne_zero N hx]
end ExactMetricDensity

noncomputable def greenPMq (hp : 19 ≤ p) : ℚ[X] :=
  (greenPMIntegral p hp).map (integralRationals p).subtype

theorem greenMq_PM_source (hp : 19 ≤ p) :
    greenMq p hp = X * (greenPMq p hp).comp (1-X^2) := by
  have he := congrArg (Polynomial.map (integralRationals p).subtype)
    (greenPMIntegral_source p hp)
  simpa only [greenMq, greenPMq, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow] using he

theorem greenCMq_PM_source (hp : 19 ≤ p) :
    greenCMq p hp = C (1/25 : ℚ) *
      (greenCoordinateQ p)^(((p-1)/2)+1) * (4*X-11) *
        (greenPMq p hp).comp WPActualPullbackSource.Vpolynomial := by
  have hcd : (greenConicQ p).natDegree = 2 := by
    unfold greenConicQ
    compute_degree; norm_num
  apply ConicKernel.comp_injective_nonconstant
    (greenConicQ p)
    (by rw [hcd]; norm_num)
  change (greenCMq p hp).comp (greenConicQ p) =
    (C (1 / 25 : ℚ) * (greenCoordinateQ p) ^ (((p - 1) / 2) + 1) *
      (4 * X - 11) * (greenPMq p hp).comp WPActualPullbackSource.Vpolynomial).comp
        (greenConicQ p)
  have hV : WPActualPullbackSource.Vpolynomial.comp (greenConicQ p) =
      1-(WPFiniteCubicLog.Tc : ℚ[X])^2 := by
    have h125 : (125 : ℚ[X]) * C (1 / 125 : ℚ) = 1 := by
      change C (125 : ℚ) * C (1 / 125 : ℚ) = C 1
      rw [← C_mul]
      norm_num
    simp only [WPActualPullbackSource.Vpolynomial, greenConicQ,
      mul_comp, C_comp, sub_comp, ofNat_comp, pow_comp,
      one_comp, X_comp, WPFiniteCubicLog.Tc]
    linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * h125
  have hl : (4*X-11 : ℚ[X]).comp (greenConicQ p) = 5*(4*X^2-3) := by
    simp only [greenConicQ, sub_comp, mul_comp, ofNat_comp, X_comp]
    ring
  have hn : 2*(((p-1)/2)+1) = p+1 := by
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  have hs : ((greenCoordinateQ p)^(((p-1)/2)+1)).comp (greenConicQ p) = X^(p+1) := by
    rw [pow_comp, greenCoordinateQ_conic, ← pow_mul, hn]
  rw [(green_actual_carrier_pullbacks_Q p hp).1, greenCMtIntegral_value p hp]
  change C (1 / 5 : ℚ) * X ^ p * (greenMq p hp).comp WPFiniteCubicLog.Tc = _
  rw [greenMq_PM_source p hp]
  simp only [mul_comp, X_comp, comp_assoc]
  rw [C_comp, hs, hl, hV]
  simp only [sub_comp, one_comp, pow_comp, X_comp]
  rw [show (WPFiniteCubicLog.Tc : ℚ[X]) = X*(4*X^2-3) by
    unfold WPFiniteCubicLog.Tc
    ring, pow_succ]
  have hc : (C (1 / 5 : ℚ) : ℚ[X]) = C (1 / 25 : ℚ) * 5 := by
    change C (1 / 5 : ℚ) = C (1 / 25 : ℚ) * C 5
    rw [← C_mul]
    norm_num
  rw [hc]
  ring

noncomputable def greenMetricPrimitiveQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1/5 : ℚ)^(p-1)) * (4*T 1-11)^p *
    invert (greenCMq p hp).toLaurent

noncomputable def greenInfinityMetricQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  -T (-2) * invert (greenOriginMetricQ p hp)

theorem green_metric_origin_orientation (hp : 19 ≤ p) :
    ActualJointGreen.resInfinity (greenInfinityMetricQ p hp) =
      (greenOriginMetricQ p hp).coeff (-1) := by
  rw [greenInfinityMetricQ, ActualJointGreen.resInfinity]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-2) (-1)
    (invert (greenOriginMetricQ p hp))
  simp only [map_one, one_mul, LaurentPolynomial.invert_apply] at hs
  norm_num at hs
  simp only [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  rw [mul_comm (T (-2)) (invert (greenOriginMetricQ p hp))]
  linear_combination hs

noncomputable def greenSq (hp : 19 ≤ p) : ℚ[X] :=
  (greenSIntegral p hp).map (integralRationals p).subtype

noncomputable def greenTBq (hp : 19 ≤ p) : ℚ[X] :=
  quadraticInverse (X * greenBq p hp)

theorem greenTBq_pullback (hp : 19 ≤ p) :
    (greenTBq p hp).comp (1-X^2) = X * greenBq p hp := by
  apply quadraticInverse_even_pullback _ (by norm_num : (2 : ℚ) ≠ 0)
  rw [mul_comp, X_comp, greenBq_odd p hp]
  ring

theorem greenSq_pullback (hp : 19 ≤ p) :
    (greenSq p hp).comp (1-X^2) =
      (greenUIntegral p hp).map (integralRationals p).subtype := by
  have he := quadraticInverse_even_pullback (greenUIntegral p hp)
    (show (2 : integralRationals p) ≠ 0 by
      exact_mod_cast (by norm_num : (2 : ℚ) ≠ 0))
    (greenUIntegral_even p hp)
  have hm := congrArg (Polynomial.map (integralRationals p).subtype) he
  simpa only [greenSq, greenSIntegral, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X] using hm

theorem greenSq_source (hp : 19 ≤ p) :
    greenSq p hp = 2 * greenHq p hp + 4 * greenTBq p hp -
      C (4 * (integralRationals p).subtype ((balancedProperIntegral p hp).eval 1)) := by
  have hqd : (1-X^2 : ℚ[X]).natDegree = 2 := by compute_degree; norm_num
  apply ConicKernel.comp_injective_nonconstant
    (1-X^2) (by rw [hqd]; norm_num)
  change (greenSq p hp).comp (1 - X ^ 2) =
    (2 * greenHq p hp + 4 * greenTBq p hp -
      C (4 * (integralRationals p).subtype ((balancedProperIntegral p hp).eval 1))).comp
        (1 - X ^ 2)
  rw [greenSq_pullback p hp]
  simp only [greenUIntegral, greenBIntegral, greenHq, greenBq,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, map_mul,
    add_comp, sub_comp, mul_comp, ofNat_comp, C_comp, greenTBq_pullback p hp]
  ring

theorem greenSq_origin (hp : 19 ≤ p) : (greenSq p hp).coeff 0 = 0 := by
  have he := congrArg (fun P : ℚ[X] => P.eval 1) (greenSq_pullback p hp)
  have hu := congrArg (integralRationals p).subtype (greenUIntegral_endpoint p hp)
  rw [← Polynomial.eval_map_apply] at hu
  simp only [map_one, map_zero] at hu
  simpa only [eval_comp, eval_sub, eval_one, eval_pow, eval_X, one_pow,
    sub_self, ← coeff_zero_eq_eval_zero, hu] using he

theorem greenCBq_TB_source (hp : 19 ≤ p) :
    (4*X-11) * greenCBq p hp =
      (greenCoordinateQ p)^((p-1)/2) *
        (greenTBq p hp).comp WPActualPullbackSource.Vpolynomial := by
  have hcd : (greenConicQ p).natDegree = 2 := by
    unfold greenConicQ
    compute_degree; norm_num
  apply ConicKernel.comp_injective_nonconstant
    (greenConicQ p) (by rw [hcd]; norm_num)
  change ((4 * X - 11) * greenCBq p hp).comp (greenConicQ p) =
    ((greenCoordinateQ p) ^ ((p - 1) / 2) *
      (greenTBq p hp).comp WPActualPullbackSource.Vpolynomial).comp (greenConicQ p)
  have hV : WPActualPullbackSource.Vpolynomial.comp (greenConicQ p) =
      1-(WPFiniteCubicLog.Tc : ℚ[X])^2 := by
    have h125 : (125 : ℚ[X]) * C (1 / 125 : ℚ) = 1 := by
      change C (125 : ℚ) * C (1 / 125 : ℚ) = C 1
      rw [← C_mul]
      norm_num
    simp only [WPActualPullbackSource.Vpolynomial, greenConicQ,
      mul_comp, C_comp, sub_comp, ofNat_comp, pow_comp, one_comp, X_comp, WPFiniteCubicLog.Tc]
    linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * h125
  have hl : (4*X-11 : ℚ[X]).comp (greenConicQ p) = 5*(4*X^2-3) := by
    simp only [greenConicQ, sub_comp, mul_comp, ofNat_comp, X_comp]
    ring
  have hpow : (X^2 : ℚ[X])^((p-1)/2) * X = X^p := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  rw [mul_comp, hl, (green_actual_carrier_pullbacks_Q p hp).2,
    mul_comp, pow_comp, greenCoordinateQ_conic, comp_assoc, hV]
  rw [show 1-(WPFiniteCubicLog.Tc : ℚ[X])^2 =
      (1-X^2 : ℚ[X]).comp (WPFiniteCubicLog.Tc : ℚ[X]) by simp]
  rw [← comp_assoc, greenTBq_pullback p hp, mul_comp, X_comp]
  rw [show (WPFiniteCubicLog.Tc : ℚ[X]) = X*(4*X^2-3) by
    unfold WPFiniteCubicLog.Tc
    ring]
  have hu5 : (5 : ℚ[X]) * C (1 / 5 : ℚ) = 1 := by
    change C (5 : ℚ) * C (1 / 5 : ℚ) = C 1
    rw [← C_mul]
    norm_num
  linear_combination
    -((greenBq p hp).comp (X * (4 * X ^ 2 - 3)) * (4 * X ^ 2 - 3)) * hpow +
      X ^ p * (greenBq p hp).comp (X * (4 * X ^ 2 - 3)) * (4 * X ^ 2 - 3) * hu5

theorem actual_green_CM_compact_source (hp : 19 ≤ p) :
    10 * greenCoordinateQ p * (WPFiniteZSource.Abar : ℚ[X]) *
      (greenCMq p hp).derivative =
        15 * (greenCoordinateQ p)^(((p-1)/2)+1) *
          (greenSq p hp).comp WPActualPullbackSource.Vpolynomial +
        C (p : ℚ) * (WPFiniteZSource.Abar : ℚ[X]) * greenCMq p hp := by
  have hc := actual_green_CM_cleared_Q p hp
  have hb := greenCBq_TB_source p hp
  rw [greenSq_source p hp]
  simp only [add_comp, sub_comp, mul_comp, ofNat_comp, C_comp]
  unfold greenHbarq at hc
  simp only [map_mul, C_ofNat] at hc ⊢
  simp only [pow_succ]
  linear_combination hc + 60 * greenCoordinateQ p * hb

end WPFieldAssembly.ActualGreenPrimitive
