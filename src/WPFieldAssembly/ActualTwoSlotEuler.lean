import WPFieldAssembly.ActualLowEuler
import WPFieldAssembly.NativeOriginalResidues
import WPFiniteKSource

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFiniteLaurentDifferential
  WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.ResidualProjection
  WPFieldAssembly.NativeQuadraticInverse

namespace WPFieldAssembly.ActualLowEuler

variable {K : Type*} [Field K]

theorem lowU_sub_origin (U : K[X]) :
    lowU (U - Polynomial.C (U.coeff 0)) = lowU U := by
  have hd : (U - Polynomial.C (U.coeff 0)).divX = U.divX := by
    ext n
    simp [coeff_divX]
  unfold lowU
  rw [hd]

theorem lowU_origin_full (U : K[X]) :
    (lowU U).coeff (-1) = -3 * (U.eval (4 / 125) - U.coeff 0) := by
  have h0 : (U - Polynomial.C (U.coeff 0)).eval 0 = 0 := by
    simp [coeff_zero_eq_eval_zero]
  have h := lowU_origin (U - Polynomial.C (U.coeff 0)) h0
  rw [lowU_sub_origin] at h
  simpa only [eval_sub, eval_C] using h

theorem nc88_shifted_ibp
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A B : K[T;T⁻¹]) (n : ℤ) (hn : (p : ℤ) ∣ n) :
    -(T n * (B * D A)).coeff (-1) =
      (T n * (A * D B)).coeff (-1) := by
  have hz : (D (T n * (A * B))).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_frobenius_shift p (A * B) n hn, D_mul,
    show D A * B = B * D A by ring,
    mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  linear_combination -hz

theorem laurent_shifted_low_contraction
    (A B : K[X]) (L n : ℕ) (hA : A.natDegree ≤ L) :
    (T (-(n : ℤ)) * invert A.toLaurent *
      B.derivative.toLaurent).coeff (-1) =
      ∑ k ∈ Finset.range (L + 1),
        ((n + k : ℕ) : K) * A.coeff k * B.coeff (n + k) := by
  classical
  conv_lhs =>
    rw [Polynomial.as_sum_range' A (L + 1) (by omega)]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T]
  have he : -(n : ℤ) + -(k : ℤ) = -((n + k : ℕ) : ℤ) := by
    push_cast
    ring
  have hm :
      T (-(n : ℤ)) *
        (LaurentPolynomial.C (A.coeff k) * T (-(k : ℤ))) =
      LaurentPolynomial.C (A.coeff k) * T (-((n + k : ℕ) : ℤ)) := by
    calc
      _ = LaurentPolynomial.C (A.coeff k) *
          (T (-(n : ℤ)) * T (-(k : ℤ))) := by ring
      _ = _ := by rw [← T_add, he]
  rw [hm, ← D_toLaurent B, WPFiniteJCarrier.shifted_coeff, D_coeff]
  have hi : (-1 : ℤ) - -((n + k : ℕ) : ℤ) + 1 =
      ((n + k : ℕ) : ℤ) := by omega
  rw [hi, WPFiniteJCarrier.toLaurent_coeff_nat]
  simp only [Int.cast_natCast]
  ring

variable (p : ℕ) [Fact p.Prime]

noncomputable def actualNC88Pair (j : ℕ) (U : (ZMod p)[X]) : ZMod p :=
  (T (-((j * p : ℕ) : ℤ)) *
    (substituteOver (actualH p) (originalQ : (ZMod p)[T;T⁻¹]) *
      D (substituteOver U
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent))).coeff (-1)

noncomputable def actualNC88Source (j : ℕ) (U : (ZMod p)[X]) : ZMod p :=
  -(T (-((j * p : ℕ) : ℤ)) * lowU U).coeff (-1)

theorem actualNC88Pair_sub_origin (j : ℕ) (U : (ZMod p)[X]) :
    actualNC88Pair p j (U - Polynomial.C (U.coeff 0)) =
      actualNC88Pair p j U := by
  let V : (ZMod p)[T;T⁻¹] :=
    (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent
  have hc : substituteOver (U - Polynomial.C (U.coeff 0)) V =
      substituteOver U V - LaurentPolynomial.C (U.coeff 0) := by
    change (Polynomial.eval₂RingHom LaurentPolynomial.C V)
          (U - Polynomial.C (U.coeff 0)) =
        (Polynomial.eval₂RingHom LaurentPolynomial.C V) U -
          LaurentPolynomial.C (U.coeff 0)
    rw [map_sub]
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  unfold actualNC88Pair
  rw [hc, map_sub, D_C, sub_zero]

theorem actualNC88Source_sub_origin (j : ℕ) (U : (ZMod p)[X]) :
    actualNC88Source p j (U - Polynomial.C (U.coeff 0)) =
      actualNC88Source p j U := by
  unfold actualNC88Source
  rw [lowU_sub_origin]

theorem actual_low_euler_NC88_zero_origin
    (hp : 19 ≤ p) (j : ℕ) (E : (ZMod p)[X]) (hE : E.eval 0 = 0) :
    Ij p j (actualF p * E) =
      actualNC88Pair p j E + actualNC88Source p j E := by
  let F := actualF p
  let H := actualH p
  let Q : (ZMod p)[T;T⁻¹] := originalQ
  let V : (ZMod p)[X] := WPFiniteNC122Residue.Qrev
  let FQ := substituteOver F Q
  let HQ := substituteOver H Q
  let EV := substituteOver E V.toLaurent
  let L := lowU E
  let N : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  let s : ℤ := ((j * p : ℕ) : ℤ)
  change Ij p j (F * E) = (T (-s) * (HQ * D EV)).coeff (-1) +
      -(T (-s) * L).coeff (-1)
  have hQL : Q * L = EV * D Q := originalQ_lowU E hE
  have heval : Q * substituteOver H.derivative Q = FQ - 1 := by
    have h := congrArg (Polynomial.eval₂RingHom LaurentPolynomial.C Q)
      (actualEuler_source p hp)
    simpa only [map_mul, map_sub, map_one,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      substituteOver, FQ, F, H] using h
  have hEulerQ : Q * D HQ = (FQ - 1) * D Q := by
    calc
      _ = Q * (substituteOver H.derivative Q * D Q) := by
        rw [D_substitute_originalQ]
      _ = (Q * substituteOver H.derivative Q) * D Q := by ring
      _ = _ := by rw [heval]
  have hFL : FQ * L = EV * D HQ + L := by
    apply mul_left_cancel₀ (actual_originalQ_ne_zero p hp)
    calc
      Q * (FQ * L) = FQ * (Q * L) := by ring
      _ = FQ * (EV * D Q) := by rw [hQL]
      _ = EV * ((FQ - 1) * D Q) + EV * D Q := by ring
      _ = EV * (Q * D HQ) + Q * L := by rw [hEulerQ, hQL]
      _ = Q * (EV * D HQ + L) := by ring
  have hshift : Ij p j (F * E) =
      (T (-N - s) *
        (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent).coeff 1 := by
    have h := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (-N - s) 1
      (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent
    simp only [map_one, one_mul] at h
    have hi : (1 : ℤ) - (-N - s) =
        (((p - 1) / 2 + j * p + 1 : ℕ) : ℤ) := by
      dsimp [N, s]
      omega
    rw [hi, WPFiniteJCarrier.toLaurent_coeff_nat] at h
    simpa only [Ij] using h.symm
  have ht : (T (-N - s) : (ZMod p)[T;T⁻¹]) * T N = T (-s) := by
    rw [← T_add]
    congr 1
    omega
  have hscaled : T (-N - s) *
        (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent =
      -(T 2 * (T (-s) * (FQ * L))) := by
    rw [density_product_kernel F E hE, actualF_whole_reciprocity p hp]
    calc
      _ = -(T 2 * ((T (-N - s) * T N) * (FQ * L))) := by ring
      _ = _ := by rw [ht]
  have hprojection : Ij p j (F * E) =
      -(T (-s) * (FQ * L)).coeff (-1) := by
    rw [hshift, hscaled]
    simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    have h := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) 2 1
      (T (-s) * (FQ * L))
    simpa only [map_one, one_mul,
      show (1 : ℤ) - 2 = -1 by norm_num] using congrArg Neg.neg h
  have hn : (p : ℤ) ∣ -s := by
    refine ⟨-(j : ℤ), ?_⟩
    dsimp [s]
    ring
  have hibp : -(T (-s) * (EV * D HQ)).coeff (-1) =
      (T (-s) * (HQ * D EV)).coeff (-1) :=
    nc88_shifted_ibp p HQ EV (-s) hn
  calc
    Ij p j (F * E) = -(T (-s) * (FQ * L)).coeff (-1) := hprojection
    _ = -(T (-s) * (EV * D HQ)).coeff (-1) +
        -(T (-s) * L).coeff (-1) := by
      rw [hFL, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      ring
    _ = _ := by rw [hibp]

theorem actual_low_euler_NC88 (hp : 19 ≤ p) (j : ℕ) (U : (ZMod p)[X]) :
    Ij p j (actualF p * U) =
      actualNC88Pair p j U + actualNC88Source p j U := by
  let E : (ZMod p)[X] := U - Polynomial.C (U.coeff 0)
  have hE : E.eval 0 = 0 := by
    dsimp [E]
    simp [coeff_zero_eq_eval_zero]
  have hF : Ij p j (actualF p) = 0 :=
    low_correction_both_projections_zero p hp
      (actualF p) (actualF_degree p hp) j
  have hFE : Ij p j (actualF p * E) = Ij p j (actualF p * U) := by
    have he : actualF p * E = actualF p * U -
        Polynomial.C (U.coeff 0) * actualF p := by
      dsimp [E]
      ring
    rw [he, WPFieldAssembly.NativeOriginalResidues.Ij_sub_local,
      Ij_C_mul, hF, mul_zero, sub_zero]
  have h := actual_low_euler_NC88_zero_origin p hp j E hE
  rw [hFE] at h
  dsimp only [E] at h
  rw [actualNC88Pair_sub_origin, actualNC88Source_sub_origin] at h
  exact h

theorem actualNC88Source_zero (U : (ZMod p)[X]) :
    actualNC88Source p 0 U = 3 * (U.eval (4 / 125) - U.coeff 0) := by
  unfold actualNC88Source
  simp only [Nat.zero_mul, Nat.cast_zero, neg_zero, T_zero, one_mul]
  rw [lowU_origin_full]
  ring

theorem actualNC88Source_one (U : (ZMod p)[X]) :
    actualNC88Source p 1 U = -(lowU U).coeff ((p : ℤ) - 1) := by
  have h := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (-(p : ℤ)) (-1) (lowU U)
  simp only [map_one, one_mul] at h
  have hi : (-1 : ℤ) - -(p : ℤ) = (p : ℤ) - 1 := by omega
  unfold actualNC88Source
  simpa only [Nat.one_mul, hi] using congrArg Neg.neg h

theorem actual_low_euler_NC88_0 (hp : 19 ≤ p) (U : (ZMod p)[X]) :
    Ij p 0 (actualF p * U) = actualNC88Pair p 0 U +
      3 * (U.eval (4 / 125) - U.eval 0) := by
  rw [actual_low_euler_NC88 p hp 0 U,
    actualNC88Source_zero, coeff_zero_eq_eval_zero]

theorem actual_low_euler_NC88_1 (hp : 19 ≤ p) (U : (ZMod p)[X]) :
    Ij p 1 (actualF p * U) = actualNC88Pair p 1 U -
      (lowU U).coeff ((p : ℤ) - 1) := by
  rw [actual_low_euler_NC88 p hp 1 U, actualNC88Source_one]
  simp only [sub_eq_add_neg]

theorem actualNC88Pair_coefficients
    (hp : 19 ≤ p) (j : ℕ) (U : (ZMod p)[X]) :
    actualNC88Pair p j U =
      ∑ k ∈ Finset.range (3 * (p / 6) + 1),
        (k : ZMod p) *
          ((actualH p).comp
            (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).coeff k *
          (U.comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).coeff (j * p + k) := by
  have hH : substituteOver (actualH p)
        (originalQ : (ZMod p)[T;T⁻¹]) =
      invert (((actualH p).comp
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).toLaurent) := by
    change substituteOver (actualH p)
      (invert (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent) = _
    rw [← substituteOver_invert, substituteOver_toLaurent]
  have hU : D (substituteOver U
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent) =
      (U.comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).derivative.toLaurent := by
    rw [substituteOver_toLaurent, D_toLaurent]
  unfold actualNC88Pair
  rw [hH, hU]
  have h := laurent_shifted_low_contraction
    ((actualH p).comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X]))
    (U.comp (WPFiniteNC122Residue.Qrev : (ZMod p)[X]))
    (3 * (p / 6)) (j * p) (actualH_pullback_degree p hp)
  have hp0 : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  simpa only [mul_assoc, Nat.cast_add, Nat.cast_mul,
    hp0, mul_zero, zero_add] using h

omit [Fact (Nat.Prime p)] in
theorem actualNC88_strict_upper_window (hp : 19 ≤ p) :
    p + 3 * (p / 6) < 2 * p := by
  omega

theorem actual_literal_Ksrc_NC88 (hp : 19 ≤ p) (j : ℕ) :
    let U : (ZMod p)[X] := quadraticInverse
      (WPFiniteKSource.KsrcP p (WPActualGaussBottom.fieldHarmonic p (p / 6)))
    Ij p j (actualF p * U) =
      actualNC88Pair p j U + actualNC88Source p j U := by
  dsimp only
  exact actual_low_euler_NC88 p hp j _

theorem actual_literal_log_square_NC88 (hp : 19 ≤ p) (j : ℕ) :
    let L : (ZMod p)[X] := quadraticInverse (WPFiniteKSource.LPsrc p)
    let h : ZMod p := WPActualGaussBottom.fieldHarmonic p (p / 6)
    let U : (ZMod p)[X] := (L - Polynomial.C h) ^ 2
    Ij p j (actualF p * U) =
      actualNC88Pair p j U + actualNC88Source p j U := by
  dsimp only
  exact actual_low_euler_NC88 p hp j _

end WPFieldAssembly.ActualLowEuler
