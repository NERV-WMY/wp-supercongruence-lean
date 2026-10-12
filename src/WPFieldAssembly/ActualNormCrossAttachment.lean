import WPFieldAssembly.ActualTwoSlotEuler
import WPFieldAssembly.ActualResidualAssembly
import WPFieldAssembly.NativeIR28
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoComparison
  WPActualRankTwoProper WPActualRankTwoLowTaylor WPActualRankTwoResidueSource
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.ResidualProjection WPFieldAssembly.ActualLowEuler
  WPActualGaussBottom WPFieldAssembly.ActualNC77Chart
  WPFieldAssembly.NativeIR28 WPFieldAssembly.ActualResidualAssembly
  WPFieldAssembly.ActualDeltaUNextSource

namespace WPFieldAssembly.ActualNormCrossAttachment

variable (p : ℕ) [Fact p.Prime]

theorem actual_rank_literal_source (hp : 19 ≤ p) :
    actualRankDividedField p (by omega) =
      actualLegendreJacobi p *
        (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) -
      X ^ p * properLegendreJacobi p := by
  rw [WPActualRankTwoComparison.actual_rankDividedField_eq_hat p hp]
  dsimp only [rankHatField, WPFiniteKSource.LPsrc,
    WPFiniteKSource.EP, WPFiniteNC122.q, evenLogPolynomial]
  simp only [map_sub]
  ring

theorem actual_rank_square_source (hp : 19 ≤ p) :
    actualRankDividedField p (by omega) ^ 2 =
      actualLegendreJacobi p ^ 2 *
        (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) ^ 2 -
      C (2 : ZMod p) *
        (X ^ p * actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6)))) +
      X ^ (2 * p) * properLegendreJacobi p ^ 2 := by
  rw [actual_rank_literal_source p hp]
  have hx : (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 := by
    rw [show 2 * p = p * 2 by omega, pow_mul]
  rw [hx]
  simp only [C_ofNat]
  ring

theorem actual_norm_cross_Ij (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (quadraticInverse (actualRankDividedField p (by omega) ^ 2)) =
      Ij p j (quadraticInverse
        (actualLegendreJacobi p ^ 2 *
          (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) ^ 2)) -
      2 * Ij p j (quadraticInverse
        (X ^ p * actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))))) +
      Ij p j (quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2)) := by
  have he := congrArg (fun P : (ZMod p)[X] => Ij p j (quadraticInverse P))
    (actual_rank_square_source p hp)
  simpa only [quadraticInverse_add_local, quadraticInverse_sub_local,
    quadraticInverse_C_mul, Ij_add, Ij_sub_local, Ij_C_mul] using he

theorem even_native_attachment (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (hev : P.comp (-X) = P) :
    (quadraticInverse P).comp (1 - X ^ 2) = P := by
  have he := NativeIR28.even_expand_contract_two p hp P hev
  rw [expand_eq_comp_X_pow] at he
  rw [quadraticInverse, comp_assoc]
  convert he using 1
  simp

theorem native_two_p_shift (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (hev : P.comp (-X) = P) :
    quadraticInverse (X ^ (2 * p) * P) =
      (1 - X ^ p) * quadraticInverse P := by
  have he := even_native_attachment p hp P hev
  have hx : (1 - X ^ p : (ZMod p)[X]).comp (1 - X ^ 2) = X ^ (2 * p) := by
    simp only [sub_comp, one_comp, pow_comp, X_comp]
    rw [sub_pow_char, one_pow, ← pow_mul]
    ring
  have hprod : X ^ (2 * p) * P =
      ((1 - X ^ p) * quadraticInverse P).comp (1 - X ^ 2) := by
    rw [mul_comp, hx, he]
  rw [hprod, quadraticInverse_quadratic]

theorem actual_Sigma_native_degree (hp : 19 ≤ p) :
    (quadraticInverse (actualLegendreJacobi p *
      actualRankDividedField p (by omega))).natDegree ≤ (p - 1) / 2 := by
  apply quadraticInverse_degree_of_le
  have hR := WPActualRankTwoComparison.rankHatField_degree p hp
  rw [← WPActualRankTwoComparison.actual_rankDividedField_eq_hat p hp] at hR
  have hY := actualLegendreJacobi_degree p
  have hhalf := WPFiniteWSource.half_exponent p hp
  exact (natDegree_mul_le_of_le hY hR).trans (by omega)

theorem actual_Sigma_I1_zero (hp : 19 ≤ p) :
    Ij p 1 (quadraticInverse (actualLegendreJacobi p *
      actualRankDividedField p (by omega))) = 0 := by
  unfold Ij
  apply coeff_eq_zero_of_natDegree_lt
  have hd := canceledDensity_degree_le
    (quadraticInverse (actualLegendreJacobi p * actualRankDividedField p (by omega)))
    ((p - 1) / 2) (by omega) (actual_Sigma_native_degree p hp)
  have hhalf := WPFiniteWSource.half_exponent p hp
  omega

theorem mul_divX_full {K : Type*} [Field K] (A B : K[X]) :
    (A * B).divX = A * B.divX + C (B.coeff 0) * A.divX := by
  apply mul_left_cancel₀ (X_ne_zero (R := K))
  have hAB := X_mul_divX_add (A * B)
  have hA := X_mul_divX_add A
  have hB := X_mul_divX_add B
  have h0 : (A * B).coeff 0 = A.coeff 0 * B.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, eval_mul,
      ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero]
  rw [h0, map_mul] at hAB
  linear_combination hAB - A * hB - C (B.coeff 0) * hA

theorem canceledDensity_mul_full {K : Type*} [Field K] (A B : K[X]) :
    WPFiniteNC122Residue.canceledDensity (A * B) =
      A.comp WPFiniteNC122Residue.Qrev * WPFiniteNC122Residue.canceledDensity B +
      C (B.coeff 0) * WPFiniteNC122Residue.canceledDensity A := by
  unfold WPFiniteNC122Residue.canceledDensity
  rw [mul_divX_full, add_comp, mul_comp, mul_comp, C_comp, add_mul]
  ring

private theorem norm_cast125_ne_zero (hp : 19 ≤ p) : (125 : ZMod p) ≠ 0 := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  rw [show (125 : ZMod p) = 5 ^ 3 by ring]
  exact pow_ne_zero 3 h5

private theorem norm_cast4_ne_zero (hp : 19 ≤ p) : (4 : ZMod p) ≠ 0 :=
  WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)

private theorem norm_fp_polynomial_pow (A : (ZMod p)[X]) :
    A ^ p = expand (ZMod p) p A := by
  have hfrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext z
    change z ^ p = z
    exact ZMod.pow_card z
  have h := Polynomial.map_frobenius_expand p A
  simpa only [hfrob, Polynomial.map_id] using h.symm

/-- X here is the density coordinate. -/
noncomputable def densityGeomMinus : (ZMod p)[X] :=
  ∑ i ∈ Finset.range p, C ((4 : ZMod p) ^ (p - 1 - i)) * X ^ i
noncomputable def densityGeomPlus : (ZMod p)[X] :=
  ∑ i ∈ Finset.range p, C ((4 : ZMod p) ^ i) * X ^ i

theorem densityGeomMinus_coeff (n : ℕ) :
    (densityGeomMinus p).coeff n =
      if n < p then (4 : ZMod p) ^ (p - 1 - n) else 0 := by
  classical
  simp only [densityGeomMinus, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  simp only [Finset.sum_ite_eq, Finset.mem_range]

theorem densityGeomPlus_coeff (n : ℕ) :
    (densityGeomPlus p).coeff n = if n < p then (4 : ZMod p) ^ n else 0 := by
  classical
  simp only [densityGeomPlus, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  simp only [Finset.sum_ite_eq, Finset.mem_range]

theorem densityGeomMinus_source :
    (4 - X : (ZMod p)[X]) * densityGeomMinus p = 4 - X ^ p := by
  classical
  have he : densityGeomMinus p = ∑ i ∈ Finset.range p,
      (X : (ZMod p)[X]) ^ i * (C (4 : ZMod p)) ^ (p - 1 - i) := by
    unfold densityGeomMinus
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_pow]
    ring
  have hg := (Commute.all (X : (ZMod p)[X]) (C (4 : ZMod p))).mul_neg_geom_sum₂ p
  have hc : (4 : (ZMod p)[X]) ^ p = 4 := by
    change (C (4 : ZMod p)) ^ p = C (4 : ZMod p)
    rw [← map_pow, ZMod.pow_card]
  rw [he]
  simpa only [C_ofNat, hc] using hg

theorem densityGeomPlus_source :
    (4 * X - 1 : (ZMod p)[X]) * densityGeomPlus p = 4 * X ^ p - 1 := by
  classical
  have he : densityGeomPlus p = ∑ i ∈ Finset.range p, (4 * X : (ZMod p)[X]) ^ i := by
    unfold densityGeomPlus
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_pow, map_pow, C_ofNat]
  have hc : (4 : (ZMod p)[X]) ^ p = 4 := by
    change (C (4 : ZMod p)) ^ p = C (4 : ZMod p)
    rw [← map_pow, ZMod.pow_card]
  rw [he, mul_geom_sum, mul_pow, hc]

private theorem density_Qrev_scaled (hp : 19 ≤ p) :
    C (125 : ZMod p) * (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) =
      (4 * X - 1) ^ 2 * (4 - X) := by
  have h125 := norm_cast125_ne_zero p hp
  rw [WPFiniteNC122Residue.Qrev_factored]
  calc
    _ = (C (125 : ZMod p) * C (125 : ZMod p)⁻¹) *
        (4 * X - 1) ^ 2 * (4 - X) := by ring
    _ = _ := by rw [← map_mul, mul_inv_cancel₀ h125, C_1, one_mul]

private theorem density_Frev_scaled (hp : 19 ≤ p) :
    C (125 : ZMod p) * (WPFiniteNC122Residue.Frev : (ZMod p)[X]) =
      132 * X ^ 3 - 81 * X ^ 2 + 12 * X := by
  have h125 := norm_cast125_ne_zero p hp
  have hs (a : ZMod p) : 125 * (a / 125) = a := by field_simp [h125]
  simp only [WPFiniteNC122Residue.Frev, mul_add, mul_sub,
    ← mul_assoc, ← map_mul, hs]
  simp only [C_ofNat]

private theorem density_Qrev_pow_scaled (hp : 19 ≤ p) :
    C (125 : ZMod p) * (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) ^ p =
      (4 * X ^ p - 1) ^ 2 * (4 - X ^ p) := by
  have h125 := norm_cast125_ne_zero p hp
  have hpow : (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) ^ p =
      C (125 : ZMod p)⁻¹ * (4 * X ^ p - 1) ^ 2 * (4 - X ^ p) := by
    rw [norm_fp_polynomial_pow, WPFiniteNC122Residue.Qrev_factored]
    simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, expand_C, expand_X]
  rw [hpow]
  calc
    _ = (C (125 : ZMod p) * C (125 : ZMod p)⁻¹) *
        (4 * X ^ p - 1) ^ 2 * (4 - X ^ p) := by ring
    _ = _ := by rw [← map_mul, mul_inv_cancel₀ h125, C_1, one_mul]

/-- Input X^p is native q^p; output X is the density coordinate. All bands remain. -/
theorem universal_density_qp_certificate (hp : 19 ≤ p) :
    C (125 : ZMod p) * WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X]) =
      2 * X ^ 2 * (4 * X ^ p - 1) ^ 2 * densityGeomMinus p -
        4 * X ^ 2 * (4 * X ^ p - 1) * (4 - X ^ p) * densityGeomPlus p +
        3 * X * (4 * X ^ p - 1) ^ 2 * (4 - X ^ p) := by
  let V : (ZMod p)[X] := WPFiniteNC122Residue.Qrev
  let F : (ZMod p)[X] := WPFiniteNC122Residue.Frev
  let b : (ZMod p)[X] := 4 * X - 1
  let a : (ZMod p)[X] := 4 - X
  let P : (ZMod p)[X] := 4 * X ^ p - 1
  let A : (ZMod p)[X] := 4 - X ^ p
  let f : (ZMod p)[X] := 132 * X ^ 3 - 81 * X ^ 2 + 12 * X
  let E : (ZMod p)[X] := 2 * X ^ 2 * P ^ 2 * densityGeomMinus p -
      4 * X ^ 2 * P * A * densityGeomPlus p + 3 * X * P ^ 2 * A
  change C (125 : ZMod p) * WPFiniteNC122Residue.canceledDensity (X ^ p) = E
  have h125 := norm_cast125_ne_zero p hp
  have h4 := norm_cast4_ne_zero p hp
  have hV : C (125 : ZMod p) * V = b ^ 2 * a := density_Qrev_scaled p hp
  have hVp : C (125 : ZMod p) * V ^ p = P ^ 2 * A := density_Qrev_pow_scaled p hp
  have hF : C (125 : ZMod p) * F = f := density_Frev_scaled p hp
  have hm : a * densityGeomMinus p = A := densityGeomMinus_source p
  have hg : b * densityGeomPlus p = P := densityGeomPlus_source p
  have hbase : V * WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X]) =
      V ^ p * F := by
    unfold WPFiniteNC122Residue.canceledDensity
    rw [divX_X_pow, if_neg (by omega : p ≠ 0), pow_comp, X_comp]
    change V * (V ^ (p - 1) * F) = V ^ p * F
    calc
      _ = (V * V ^ (p - 1)) * F := by ring
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hleft : (C (125 : ZMod p) * V) *
      (C (125 : ZMod p) * WPFiniteNC122Residue.canceledDensity (X ^ p)) = P ^ 2 * A * f := by
    calc
      _ = C (125 : ZMod p) ^ 2 * (V * WPFiniteNC122Residue.canceledDensity (X ^ p)) := by ring
      _ = C (125 : ZMod p) ^ 2 * (V ^ p * F) := by rw [hbase]
      _ = (C (125 : ZMod p) * V ^ p) * (C (125 : ZMod p) * F) := by ring
      _ = _ := by rw [hVp, hF]
  have hright : (C (125 : ZMod p) * V) * E = P ^ 2 * A * f := by
    rw [hV]
    dsimp only [E]
    calc
      _ = 2 * X ^ 2 * b ^ 2 * P ^ 2 * (a * densityGeomMinus p) -
          4 * X ^ 2 * b * a * P * A * (b * densityGeomPlus p) +
          3 * X * b ^ 2 * a * P ^ 2 * A := by ring
      _ = 2 * X ^ 2 * b ^ 2 * P ^ 2 * A - 4 * X ^ 2 * b * a * P * A * P +
          3 * X * b ^ 2 * a * P ^ 2 * A := by rw [hm, hg]
      _ = P ^ 2 * A * f := by dsimp only [a, b, P, A, f]; ring
  have hVne : V ≠ 0 := by
    intro hz
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) hz
    have hv : V.eval 0 = 4 / 125 := by simp [V, WPFiniteNC122Residue.Qrev]
    rw [hv] at he
    exact (div_ne_zero h4 h125) (by simpa using he)
  apply mul_left_cancel₀ (mul_ne_zero (C_ne_zero.mpr h125) hVne)
  exact hleft.trans hright.symm

theorem universal_density_qp_bands (hp : 19 ≤ p) :
    C (125 : ZMod p) * WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X]) =
      C 32 * X ^ (2 * p + 2) * densityGeomMinus p -
        C 16 * X ^ (p + 2) * densityGeomMinus p + C 2 * X ^ 2 * densityGeomMinus p +
        C 16 * X ^ (2 * p + 2) * densityGeomPlus p -
        C 68 * X ^ (p + 2) * densityGeomPlus p + C 16 * X ^ 2 * densityGeomPlus p -
        C 48 * X ^ (3 * p + 1) + C 216 * X ^ (2 * p + 1) - C 99 * X ^ (p + 1) + C 12 * X := by
  have h2p2 : (X : (ZMod p)[X]) ^ (2 * p + 2) = X ^ 2 * (X ^ p) ^ 2 := by
    rw [show 2 * p + 2 = p + p + 2 by omega, pow_add, pow_add]; ring
  have hp2 : (X : (ZMod p)[X]) ^ (p + 2) = X ^ 2 * X ^ p := by rw [pow_add]; ring
  have h3p1 : (X : (ZMod p)[X]) ^ (3 * p + 1) = X * (X ^ p) ^ 3 := by
    rw [show 3 * p + 1 = p + p + p + 1 by omega, pow_add, pow_add, pow_add]; ring
  have h2p1 : (X : (ZMod p)[X]) ^ (2 * p + 1) = X * (X ^ p) ^ 2 := by
    rw [show 2 * p + 1 = p + p + 1 by omega, pow_add, pow_add]; ring
  have hp1 : (X : (ZMod p)[X]) ^ (p + 1) = X * X ^ p := by rw [pow_add]; ring
  rw [universal_density_qp_certificate p hp, h2p2, hp2, h3p1, h2p1, hp1]
  simp only [C_ofNat]
  ring

theorem densityGeom_midpoint (hp : 19 ≤ p) :
    (densityGeomMinus p).coeff (((p - 1) / 2) - 1) = 4 ∧
      (densityGeomPlus p).coeff (((p - 1) / 2) - 1) = (1 / 4 : ZMod p) := by
  let N := (p - 1) / 2
  have hhalf : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have hfour : (4 : ZMod p) ^ N = 1 := WPFiniteWSource.four_half_power p hp
  have h4 := norm_cast4_ne_zero p hp
  have hN : 1 ≤ N := by omega
  constructor
  · change (densityGeomMinus p).coeff (N - 1) = 4
    rw [densityGeomMinus_coeff, if_pos (by omega : N - 1 < p),
      show p - 1 - (N - 1) = N + 1 by omega, pow_succ, hfour, one_mul]
  · change (densityGeomPlus p).coeff (N - 1) = 1 / 4
    rw [densityGeomPlus_coeff, if_pos (by omega : N - 1 < p)]
    apply (eq_div_iff h4).2
    rw [← pow_succ, show N - 1 + 1 = N by omega, hfour]

theorem universal_I0_qp (hp : 19 ≤ p) : Ij p 0 (X ^ p : (ZMod p)[X]) = 12 / 125 := by
  let N := (p - 1) / 2
  unfold Ij
  simp only [Nat.zero_mul, Nat.add_zero]
  change (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + 1) = 12 / 125
  have hhalf : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have hm := (densityGeom_midpoint p hp).1
  have hg := (densityGeom_midpoint p hp).2
  change (densityGeomMinus p).coeff (N - 1) = 4 at hm
  change (densityGeomPlus p).coeff (N - 1) = 1 / 4 at hg
  have h125 := norm_cast125_ne_zero p hp
  have h4 := norm_cast4_ne_zero p hp
  have hi : N + 1 - 2 = N - 1 := by omega
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (N + 1))
    (universal_density_qp_bands p hp)
  simp only [coeff_add, coeff_sub, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_X] at hc
  split_ifs at hc <;> try omega
  all_goals
    simp only [hi, hm, hg, mul_zero, add_zero, zero_add,
      sub_zero] at hc
    have hnum : (2 : ZMod p) * 4 + 16 * (1 / 4) = 12 := by field_simp [h4]; ring
    have hcalc : (125 : ZMod p) *
        (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + 1) = 12 := by
      exact hc.trans hnum
    apply (eq_div_iff h125).2
    simpa only [mul_comm] using hcalc

theorem universal_I1_qp (hp : 19 ≤ p) : Ij p 1 (X ^ p : (ZMod p)[X]) = -81 / 125 := by
  let N := (p - 1) / 2
  unfold Ij
  simp only [Nat.one_mul]
  change (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + p + 1) = -81 / 125
  have hhalf : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have hm := (densityGeom_midpoint p hp).1
  have hg := (densityGeom_midpoint p hp).2
  change (densityGeomMinus p).coeff (N - 1) = 4 at hm
  change (densityGeomPlus p).coeff (N - 1) = 1 / 4 at hg
  have h125 := norm_cast125_ne_zero p hp
  have h4 := norm_cast4_ne_zero p hp
  have hi : N + p + 1 - (p + 2) = N - 1 := by omega
  have hfar : N + p + 1 - 2 = N + p - 1 := by omega
  have hmf : (densityGeomMinus p).coeff (N + p - 1) = 0 := by
    rw [densityGeomMinus_coeff, if_neg (by omega)]
  have hgf : (densityGeomPlus p).coeff (N + p - 1) = 0 := by
    rw [densityGeomPlus_coeff, if_neg (by omega)]
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (N + p + 1))
    (universal_density_qp_bands p hp)
  simp only [coeff_add, coeff_sub, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_X] at hc
  split_ifs at hc <;> try omega
  all_goals
    simp only [hi, hfar, hm, hg, hmf, hgf, mul_zero,
      add_zero, sub_zero, zero_sub] at hc
    have hnum : -((16 : ZMod p) * 4) - 68 * (1 / 4) = -81 := by field_simp [h4]; ring
    have hcalc : (125 : ZMod p) *
        (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + p + 1) = -81 := by
      exact hc.trans hnum
    apply (eq_div_iff h125).2
    simpa only [mul_comm] using hcalc

theorem frobenius_band_hole (N j : ℕ) (hN : N + 1 < p)
    (A B : (ZMod p)[X]) (hB : B.natDegree ≤ N) :
    (A ^ p * B).coeff (N + j * p + 1) = 0 := by
  classical
  have hs : A ^ p = ∑ k ∈ Finset.range (A.natDegree + 1),
      C (A.coeff k) * X ^ (p * k) := by
    rw [norm_fp_polynomial_pow]
    conv_lhs => rw [Polynomial.as_sum_range' A (A.natDegree + 1) (by omega)]
    simp only [map_sum, expand_monomial]
    simp only [← C_mul_X_pow_eq_monomial, Nat.mul_comm]
  rw [hs, Finset.sum_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hpk
  · have hkj : k ≤ j := by
      by_contra hn
      have hjk : j + 1 ≤ k := by omega
      have hm := Nat.mul_le_mul_left p hjk
      have hm' : j * p + p ≤ p * k := by
        simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_comm] using hm
      omega
    have hm := Nat.mul_le_mul_left p hkj
    have hm' : p * k ≤ j * p := by simpa only [Nat.mul_comm] using hm
    have hz : B.coeff (N + j * p + 1 - p * k) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    rw [hz, mul_zero]
  · exact mul_zero _

theorem low_B_frobenius_projection (hp : 19 ≤ p) (B : (ZMod p)[X])
    (hB : B.natDegree ≤ p / 6) (j : ℕ) :
    Ij p j (X ^ p * B) = B.coeff 0 * Ij p j (X ^ p) := by
  let N := (p - 1) / 2
  have hhalf : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have h6 := Nat.div_mul_le_self p 6
  have hD : (WPFiniteNC122Residue.canceledDensity B).natDegree ≤ N := by
    have hd := canceledDensity_degree_le B (p / 6) (by omega) hB
    omega
  have hhole := frobenius_band_hole p N j (by omega)
    (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) (WPFiniteNC122Residue.canceledDensity B) hD
  unfold Ij
  rw [canceledDensity_mul_full, pow_comp, X_comp, coeff_add, coeff_C_mul]
  change ((WPFiniteNC122Residue.Qrev : (ZMod p)[X]) ^ p *
      WPFiniteNC122Residue.canceledDensity B).coeff (N + j * p + 1) +
    B.coeff 0 * (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + j * p + 1) =
    B.coeff 0 * (WPFiniteNC122Residue.canceledDensity (X ^ p : (ZMod p)[X])).coeff (N + j * p + 1)
  rw [hhole, zero_add]

theorem low_B_proper_projection (hp : 19 ≤ p) (B : (ZMod p)[X])
    (hB : B.natDegree ≤ p / 6) (j : ℕ) :
    Ij p j ((1 - X ^ p) * B) = -B.coeff 0 * Ij p j (X ^ p) := by
  rw [sub_mul, one_mul, Ij_sub_local,
    low_correction_both_projections_zero p hp B hB j, low_B_frobenius_projection p hp B hB j]
  ring

noncomputable def actualProperSquareNative : (ZMod p)[X] :=
  quadraticInverse (properLegendreJacobi p ^ 2)

theorem actual_proper_square_even (hp : 19 ≤ p) :
    (properLegendreJacobi p ^ 2).comp (-X) = properLegendreJacobi p ^ 2 := by
  let s : ZMod p := (-1) ^ (p / 6)
  have hs : s ^ 2 = 1 := by
    dsimp only [s]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    _ = (-C s * properLegendreJacobi p) ^ 2 := by
      rw [pow_comp, actual_proper_legendre_reflect p hp]
    _ = C (s ^ 2) * properLegendreJacobi p ^ 2 := by simp only [map_pow]; ring
    _ = _ := by rw [hs, C_1, one_mul]

theorem actual_proper_square_native_degree (hp : 19 ≤ p) :
    (actualProperSquareNative p).natDegree ≤ p / 6 - 1 := by
  have hn : (properLegendreJacobi p).natDegree ≤ p / 6 - 1 := by
    have hd := properLegendreJacobi_degree p (by omega)
    omega
  unfold actualProperSquareNative
  apply quadraticInverse_degree_of_le
  exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hn)

theorem actual_proper_square_native_origin (hp : 19 ≤ p) :
    (actualProperSquareNative p).coeff 0 = fieldHarmonic p (p / 6) ^ 2 := by
  have he := even_native_attachment p hp (properLegendreJacobi p ^ 2)
    (actual_proper_square_even p hp)
  have hv := congrArg (fun P : (ZMod p)[X] => P.eval 1) he
  change ((actualProperSquareNative p).comp (1 - X ^ 2)).eval 1 =
    (properLegendreJacobi p ^ 2).eval 1 at hv
  simp only [eval_comp, eval_sub, eval_one, eval_pow, eval_X, one_pow,
    sub_self, properLegendreJacobi_endpoint_one] at hv
  simpa only [coeff_zero_eq_eval_zero, neg_sq] using hv

theorem actual_proper_band_native (hp : 19 ≤ p) :
    quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2) =
      (1 - X ^ p) * actualProperSquareNative p := by
  simpa only [actualProperSquareNative] using native_two_p_shift p hp
    (properLegendreJacobi p ^ 2) (actual_proper_square_even p hp)

theorem actual_proper_band_all_slots (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2)) =
      -(fieldHarmonic p (p / 6) ^ 2) * Ij p j (X ^ p : (ZMod p)[X]) := by
  rw [actual_proper_band_native p hp, low_B_proper_projection p hp
    (actualProperSquareNative p) ((actual_proper_square_native_degree p hp).trans
      (Nat.sub_le _ _)) j, actual_proper_square_native_origin p hp]

theorem actual_proper_band_I0 (hp : 19 ≤ p) :
    Ij p 0 (quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2)) =
      -(12 * fieldHarmonic p (p / 6) ^ 2) / 125 := by
  rw [actual_proper_band_all_slots p hp 0, universal_I0_qp p hp]
  simp only [div_eq_mul_inv]
  ring

theorem actual_proper_band_I1 (hp : 19 ≤ p) :
    Ij p 1 (quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2)) =
      (81 * fieldHarmonic p (p / 6) ^ 2) / 125 := by
  rw [actual_proper_band_all_slots p hp 1, universal_I1_qp p hp]
  simp only [div_eq_mul_inv]
  ring

theorem actual_proper_band_QO (hp : 19 ≤ p) :
    QO p (X ^ (2 * p) * properLegendreJacobi p ^ 2) =
      -(12 * fieldHarmonic p (p / 6) ^ 2) / 125 := by
  exact actual_proper_band_I0 p hp

noncomputable def actualNormXi (hp : 19 ≤ p) : (ZMod p)[X] :=
  quadraticInverse (actualRankDividedField p (by omega) ^ 2 -
    X ^ (2 * p) * properLegendreJacobi p ^ 2)

theorem actual_original_norm_Xi (hp : 19 ≤ p) :
    (originalNorm p : ZMod p) = Ij p 0 (actualNormXi p hp) / 3 +
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) +
      (103 * fieldHarmonic p (p / 6) ^ 2) / 1000 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  have h125 := norm_cast125_ne_zero p hp
  have h1000 : (1000 : ZMod p) ≠ 0 := by
    rw [show (1000 : ZMod p) = 2 ^ 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 3 h5)
  rw [actual_original_norm_full p hp]
  unfold actualNormXi
  rw [quadraticInverse_sub_local, Ij_sub_local, Ij_sub_local,
    actual_proper_band_I0 p hp, actual_proper_band_I1 p hp]
  unfold QO
  field_simp [h3, h24, h125, h1000]
  ring

theorem quadraticInverse_mul_even (hp : 19 ≤ p) (P Q : (ZMod p)[X])
    (hP : P.comp (-X) = P) (hQ : Q.comp (-X) = Q) :
    quadraticInverse (P * Q) = quadraticInverse P * quadraticInverse Q := by
  have he : (quadraticInverse P * quadraticInverse Q).comp (1 - X ^ 2) = P * Q := by
    rw [mul_comp, even_native_attachment p hp P hP, even_native_attachment p hp Q hQ]
  have h := congrArg quadraticInverse he
  rw [quadraticInverse_quadratic] at h
  exact h.symm

noncomputable def actualLogNative : (ZMod p)[X] := quadraticInverse (WPFiniteKSource.LPsrc p)
noncomputable def actualSigmaNative (hp : 19 ≤ p) : (ZMod p)[X] :=
  quadraticInverse (actualLegendreJacobi p * actualRankDividedField p (by omega))
noncomputable def actualLogMinusH : (ZMod p)[X] := actualLogNative p - C (fieldHarmonic p (p / 6))

theorem actual_Y_square_even (hp : 19 ≤ p) :
    (actualLegendreJacobi p ^ 2).comp (-X) = actualLegendreJacobi p ^ 2 := by
  let s : ZMod p := (-1) ^ (p / 6)
  have hs : s ^ 2 = 1 := by
    dsimp only [s]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hY : (actualLegendreJacobi p).comp (-X) = C s * actualLegendreJacobi p :=
    legendreField_reflect p (p / 6) (by omega)
  calc
    _ = (C s * actualLegendreJacobi p) ^ 2 := by rw [pow_comp, hY]
    _ = C (s ^ 2) * actualLegendreJacobi p ^ 2 := by simp only [map_pow]; ring
    _ = _ := by rw [hs, C_1, one_mul]

theorem actual_YR_even (hp : 19 ≤ p) :
    (actualLegendreJacobi p * actualRankDividedField p (by omega)).comp (-X) =
      actualLegendreJacobi p * actualRankDividedField p (by omega) := by
  let s : ZMod p := (-1) ^ (p / 6)
  have hs : s ^ 2 = 1 := by
    dsimp only [s]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hY : (actualLegendreJacobi p).comp (-X) = C s * actualLegendreJacobi p :=
    legendreField_reflect p (p / 6) (by omega)
  rw [mul_comp, hY, actual_rank_divided_reflect p hp]
  change (C s * actualLegendreJacobi p) * (C s * actualRankDividedField p (by omega)) =
    actualLegendreJacobi p * actualRankDividedField p (by omega)
  calc
    _ = C (s ^ 2) * (actualLegendreJacobi p * actualRankDividedField p (by omega)) := by
      simp only [map_pow]
      ring
    _ = _ := by rw [hs, C_1, one_mul]

theorem actual_log_minus_h_native :
    quadraticInverse (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) =
      actualLogMinusH p := by
  rw [quadraticInverse_sub_local]
  simp only [actualLogMinusH, actualLogNative, quadraticInverse, contract_C, C_comp]

theorem actual_Xi_whole_source (hp : 19 ≤ p) :
    actualRankDividedField p (by omega) ^ 2 - X ^ (2 * p) * properLegendreJacobi p ^ 2 =
      2 * (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) *
        (actualLegendreJacobi p * actualRankDividedField p (by omega)) -
      actualLegendreJacobi p ^ 2 *
        (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) ^ 2 := by
  rw [actual_rank_literal_source p hp]
  have hx : (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  rw [hx]
  ring

theorem actual_Xi_native_source (hp : 19 ≤ p) :
    actualNormXi p hp = 2 * actualLogMinusH p * actualSigmaNative p hp -
      actualF p * actualLogMinusH p ^ 2 := by
  let A : (ZMod p)[X] := WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))
  have hA : A.comp (-X) = A := by
    dsimp only [A]
    rw [sub_comp, WPFiniteNC122Residue.LPsrc_even, C_comp]
  have hA2 : (A ^ 2).comp (-X) = A ^ 2 := by rw [pow_comp, hA]
  have hqiA : quadraticInverse A = actualLogMinusH p := actual_log_minus_h_native p
  have hqiA2 : quadraticInverse (A ^ 2) = actualLogMinusH p ^ 2 := by
    rw [pow_two, quadraticInverse_mul_even p hp A A hA hA, hqiA, ← pow_two]
  have hcross : quadraticInverse
      (A * (actualLegendreJacobi p * actualRankDividedField p (by omega))) =
      actualLogMinusH p * actualSigmaNative p hp := by
    rw [quadraticInverse_mul_even p hp A
      (actualLegendreJacobi p * actualRankDividedField p (by omega)) hA (actual_YR_even p hp), hqiA]
    rfl
  have hsquare : quadraticInverse (actualLegendreJacobi p ^ 2 * A ^ 2) =
      actualF p * actualLogMinusH p ^ 2 := by
    rw [quadraticInverse_mul_even p hp (actualLegendreJacobi p ^ 2) (A ^ 2)
      (actual_Y_square_even p hp) hA2, hqiA2]
    rfl
  have htwo := quadraticInverse_nat_mul_local 2
    (A * (actualLegendreJacobi p * actualRankDividedField p (by omega)))
  norm_num only [Nat.cast_ofNat] at htwo
  unfold actualNormXi
  rw [actual_Xi_whole_source p hp, quadraticInverse_sub_local,
    show (2 : (ZMod p)[X]) * (WPFiniteKSource.LPsrc p - C (fieldHarmonic p (p / 6))) *
      (actualLegendreJacobi p * actualRankDividedField p (by omega)) =
      2 * (A * (actualLegendreJacobi p * actualRankDividedField p (by omega))) by
      dsimp only [A]; ring,
    htwo, hcross, hsquare]
  ring

theorem actual_Sigma_native_I1_zero (hp : 19 ≤ p) : Ij p 1 (actualSigmaNative p hp) = 0 := by
  simpa only [actualSigmaNative] using actual_Sigma_I1_zero p hp

theorem actual_Xi_all_slots_NC88 (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (actualNormXi p hp) =
      2 * Ij p j (actualLogNative p * actualSigmaNative p hp) -
      2 * fieldHarmonic p (p / 6) * Ij p j (actualSigmaNative p hp) -
      actualNC88Pair p j (actualLogMinusH p ^ 2) -
      actualNC88Source p j (actualLogMinusH p ^ 2) := by
  have hcross : Ij p j (actualLogMinusH p * actualSigmaNative p hp) =
      Ij p j (actualLogNative p * actualSigmaNative p hp) -
        fieldHarmonic p (p / 6) * Ij p j (actualSigmaNative p hp) := by
    unfold actualLogMinusH
    rw [sub_mul, Ij_sub_local, Ij_C_mul]
  have htwo := Ij_nat_mul_local p j 2
    (actualLogMinusH p * actualSigmaNative p hp)
  norm_num only [Nat.cast_ofNat] at htwo
  rw [actual_Xi_native_source p hp, Ij_sub_local,
    show (2 : (ZMod p)[X]) * actualLogMinusH p * actualSigmaNative p hp =
      2 * (actualLogMinusH p * actualSigmaNative p hp) by ring,
    htwo, hcross, actual_low_euler_NC88 p hp j (actualLogMinusH p ^ 2)]
  ring

theorem actual_Xi_upper_NC88 (hp : 19 ≤ p) :
    Ij p 1 (actualNormXi p hp) = 2 * Ij p 1 (actualLogNative p * actualSigmaNative p hp) -
      actualNC88Pair p 1 (actualLogMinusH p ^ 2) - actualNC88Source p 1 (actualLogMinusH p ^ 2) := by
  rw [actual_Xi_all_slots_NC88 p hp 1, actual_Sigma_native_I1_zero p hp,
    mul_zero, sub_zero]

theorem actual_full_norm_upper_NC88 (hp : 19 ≤ p) :
    Ij p 1 (quadraticInverse (actualRankDividedField p (by omega) ^ 2)) =
      2 * Ij p 1 (actualLogNative p * actualSigmaNative p hp) -
      actualNC88Pair p 1 (actualLogMinusH p ^ 2) - actualNC88Source p 1 (actualLogMinusH p ^ 2) +
      (81 * fieldHarmonic p (p / 6) ^ 2) / 125 := by
  have hz : quadraticInverse (actualRankDividedField p (by omega) ^ 2) =
      actualNormXi p hp + quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2) := by
    unfold actualNormXi
    rw [quadraticInverse_sub_local]
    ring
  rw [hz, Ij_add, actual_Xi_upper_NC88 p hp, actual_proper_band_I1 p hp]

/-- Both original norm slots retain their actual origins and whole upper source. -/
theorem actual_original_norm_NC88 (hp : 19 ≤ p) :
    (originalNorm p : ZMod p) =
      (2 / 3 : ZMod p) * Ij p 0 (actualLogNative p * actualSigmaNative p hp) -
      (2 / 3 : ZMod p) * fieldHarmonic p (p / 6) * Ij p 0 (actualSigmaNative p hp) -
      actualNC88Pair p 0 (actualLogMinusH p ^ 2) / 3 -
      ((actualLogMinusH p).eval (4 / 125) ^ 2 - (actualLogMinusH p).eval 0 ^ 2) +
      (5 / 12 : ZMod p) * Ij p 1 (actualLogNative p * actualSigmaNative p hp) -
      (5 / 24 : ZMod p) * actualNC88Pair p 1 (actualLogMinusH p ^ 2) +
      (5 / 24 : ZMod p) * (lowU (actualLogMinusH p ^ 2)).coeff ((p : ℤ) - 1) +
      (103 * fieldHarmonic p (p / 6) ^ 2) / 1000 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h12 : (12 : ZMod p) ≠ 0 := by
    rw [show (12 : ZMod p) = 2 ^ 2 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) h3
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  have h1000 : (1000 : ZMod p) ≠ 0 := by
    rw [show (1000 : ZMod p) = 2 ^ 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 3 h5)
  rw [actual_original_norm_Xi p hp, actual_Xi_all_slots_NC88 p hp 0,
    actual_Xi_upper_NC88 p hp]
  simp only [actualNC88Source_zero, actualNC88Source_one,
    coeff_zero_eq_eval_zero, eval_pow]
  field_simp [h3, h12, h24, h1000]
  ring

end WPFieldAssembly.ActualNormCrossAttachment
