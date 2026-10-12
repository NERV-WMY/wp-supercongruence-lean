import WPFieldAssembly.ConicKernel
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.FirstGreen

set_option maxHeartbeats 1000000

/-- All derivative-invisible slots in the actual bounded homogeneous remainder. -/
theorem even_flat_three_slots
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (b : (ZMod p)[X])
    (hD : b.derivative = 0)
    (hdeg : b.natDegree ≤ 5 * p - 3)
    (hev : b.comp (-X) = b) :
    ∃ a0 a2 a4 : ZMod p,
      b = Polynomial.C a0 + Polynomial.C a2 * X ^ (2 * p) +
        Polynomial.C a4 * X ^ (4 * p) := by
  let U : (ZMod p)[X] := contract p b
  have hpP : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have he : expand (ZMod p) p U = b :=
    Polynomial.expand_contract p hD hpP.ne_zero
  have hUd : U.natDegree ≤ 4 := by
    have hm : U.natDegree * p ≤ 5 * p - 3 := by
      rw [← natDegree_expand p U, he]
      exact hdeg
    by_contra hn
    have h5 : 5 ≤ U.natDegree := by omega
    have hh := Nat.mul_le_mul_right p h5
    omega
  have ho : Odd p := hpP.odd_of_ne_two (by omega)
  have hOddCoeff (n : ℕ)
      (hs : (-1 : ZMod p) ^ (n * p) = -1) :
      U.coeff n = 0 := by
    have hc := congrArg
      (fun Q : (ZMod p)[X] => Q.coeff (n * p)) hev
    rw [WPFieldAssembly.ConicKernel.coeff_comp_neg, hs] at hc
    have hz : (2 : ZMod p) * b.coeff (n * p) = 0 := by
      linear_combination -hc
    change (contract p b).coeff n = 0
    rw [coeff_contract hpP.ne_zero]
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hU1 : U.coeff 1 = 0 :=
    hOddCoeff 1 (by simp only [one_mul, ho.neg_one_pow])
  have hU3 : U.coeff 3 = 0 := hOddCoeff 3 (by
    rw [Nat.mul_comm, pow_mul, ho.neg_one_pow]
    norm_num)
  have hs :
      U = Polynomial.C (U.coeff 0) +
        Polynomial.C (U.coeff 2) * X ^ 2 +
        Polynomial.C (U.coeff 4) * X ^ 4 := by
    ext n
    by_cases hn : n ≤ 4
    · interval_cases n <;> simp [hU1, hU3]
    · have hz : U.coeff n = 0 :=
        coeff_eq_zero_of_natDegree_lt (hUd.trans_lt (by omega))
      have hn0 : n ≠ 0 := by omega
      have hn2 : n ≠ 2 := by omega
      have hn4 : n ≠ 4 := by omega
      simp [hz, hn0, hn2, hn4, coeff_C, coeff_C_mul, coeff_X_pow]
  refine ⟨U.coeff 0, U.coeff 2, U.coeff 4, ?_⟩
  calc
    b = expand (ZMod p) p U := he.symm
    _ = expand (ZMod p) p
        (Polynomial.C (U.coeff 0) + Polynomial.C (U.coeff 2) * X ^ 2 +
          Polynomial.C (U.coeff 4) * X ^ 4) := congrArg (expand (ZMod p) p) hs
    _ = _ := by
      simp only [map_add, map_mul, map_pow, expand_C, expand_X]
      rw [← pow_mul, ← pow_mul]
      simp only [Nat.mul_comm]

/-- Cleared proper Green algebra; every actual source is attached separately. -/
theorem first_green_cleared
    {K : Type*} [Field K]
    (a l r R f χ P H Kpol z CB CM : K[T;T⁻¹]) (h : K)
    (hχ : χ = f * P + z * CB)
    (hP : D P = R - r)
    (hH : a * D H = (f - 1) * l)
    (hK : a * D Kpol = H * l)
    (hz : D z = 0)
    (hM : a * z * D CM =
      a * R * (H + 2 * LaurentPolynomial.C h) - z * CB * l) :
    a * D (P * (H + 2 * LaurentPolynomial.C h) + Kpol - z * CM) =
      (χ + H - P) * l - a * (H + 2 * LaurentPolynomial.C h) * r := by
  have hD2 : D (2 : K[T;T⁻¹]) = 0 := by
    change D (LaurentPolynomial.C (2 : K)) = 0
    exact D_C 2
  simp only [map_sub, map_add, D_mul, D_C, hD2, hz,
    mul_zero, add_zero]
  linear_combination
    a * (H + 2 * LaurentPolynomial.C h) * hP +
    P * hH + hK - hM - l * hχ

theorem three_phase_zero
    {K : Type*} [Field K]
    (h3 : (3 : K) ≠ 0) (h4 : (4 : K) ≠ 0)
    (h15 : (15 : K) ≠ 0)
    (α β γ : K)
    (ha : α / 4 + β + 4 * γ = 0)
    (hb : 4 * α + β + γ / 4 = 0)
    (hpos : 3 * α = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have hα : α = 0 := (mul_eq_zero.mp hpos).resolve_left h3
  rw [hα, zero_div, zero_add] at ha
  rw [hα, mul_zero, zero_add] at hb
  have hb' : 4 * β + γ = 0 := by
    field_simp [h4] at hb
    linear_combination hb
  have hγ' : 15 * γ = 0 := by
    linear_combination 4 * ha - hb'
  have hγ : γ = 0 := (mul_eq_zero.mp hγ').resolve_left h15
  have hβ : β = 0 := by simpa [hγ] using ha
  exact ⟨hα, hβ, hγ⟩

end WPFieldAssembly.FirstGreen
