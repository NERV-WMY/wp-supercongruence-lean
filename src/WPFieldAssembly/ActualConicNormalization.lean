import WPFieldAssembly.ActualConicKernelData

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteJCarrier WPFiniteCubicLog
  WPActualRankTwoLegendreField WPActualRankTwoProper WPActualRankTwoComparison
  WPFieldAssembly.ConicChart WPFieldAssembly.ConicCoefficients
  WPFieldAssembly.NativeChiFieldSource WPFieldAssembly.NativeShiftedChi
  WPFieldAssembly.ActualConicSource WPFieldAssembly.ActualConicProper
  WPFieldAssembly.ConicDivision WPFieldAssembly.ConicKernel
  WPFieldAssembly.ActualConicKernelData

namespace WPFieldAssembly.ActualConicNormalization

set_option maxHeartbeats 1000000

theorem actual_conic_self_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let y := (actualLegendreJacobi p).comp Tc
    conicC conicA ((c0Field p hp).comp B) (y ^ 2) (y ^ 2) = 0 := by
  let f := halfPullbackField p hp
  have hs := actual_half_self_field_zero p hp
  have hz : polynomialConcomitant (c2Field p hp) (c1Field p hp) (c0Field p hp) f f = 0 := by
    ext n
    have hh := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (n : ℤ)) hs
    rw [← concomitant_toLaurent] at hh
    rw [toLaurent_coeff_nat] at hh
    change _ = 0 at hh
    exact hh
  have hc := congrArg (fun P : (ZMod p)[X] => P.comp B) hz
  have hchain := actual_conic_coefficient_chain p hp
  rw [polynomial_conic_transport _ _ _ _ _ _ _ hchain.1 hchain.2, zero_comp] at hc
  have hF : f.comp B = ((actualLegendreJacobi p).comp Tc) ^ 2 := by
    dsimp only [f]
    rw [halfPullbackField_eq]
    exact actual_full_native_conic_square p hp
  rw [hF] at hc
  exact hc

theorem actual_conic_quotient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ b : (ZMod p)[X],
      firstNumerator conicA ((actualLegendreJacobi p).comp Tc)
        ((shiftedChiField p hp).comp B) (forcingE p) =
          (actualLegendreJacobi p).comp Tc * b ∧
        b.derivative = 0 ∧ (conicA : (ZMod p)[X]) ∣ b := by
  let y := (actualLegendreJacobi p).comp Tc
  let m := C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc
  let H := (shiftedChiField p hp).comp B
  let A := (conicA : (ZMod p)[X])
  let E := forcingE p
  have hA : A ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
    simp [A, conicA] at he
  have hy : y ≠ 0 := by
    have he : y.eval 1 = 1 := by
      simp only [y, eval_comp]
      have ht : (Tc : (ZMod p)[X]).eval 1 = 1 := by norm_num [Tc]
      rw [ht]
      exact actualLegendreJacobi_endpoint_one p
    intro hz
    rw [hz, eval_zero] at he
    exact zero_ne_one he
  have hW : A * (y * m.derivative - y.derivative * m) = 1 - y ^ 2 :=
    actual_conic_proper_wronskian p hp
  have hself : conicC A ((c0Field p hp).comp B) (y ^ 2) (y ^ 2) = 0 :=
    actual_conic_self_zero p hp
  have hs : conicC A ((c0Field p hp).comp B) (y ^ 2) H +
      A * (E.derivative * (y ^ 2) ^ 2 + E * y ^ 2 * (y ^ 2).derivative) = 0 := by
    have hsquare : (y ^ 2) ^ 2 = y ^ 4 := by ring
    rw [hsquare]
    exact actual_half_chi_conic_source p hp
  obtain ⟨b, hb, hD⟩ := source_divided_kernel A ((c0Field p hp).comp B) y m H E hA hy hW hself hs
  let L := y * H.derivative - 2 * y.derivative * H + 5 * X * B ^ (p - 1) * y ^ 3
  have hML : firstNumerator A y H E = A * L := by
    dsimp only [firstNumerator, L, E, forcingE, A]
    ring
  have hdiv : A ∣ b := ⟨y * L + (y * m.derivative - y.derivative * m) * b,
    source_kernel_divisor A y m (firstNumerator A y H E) b L hW hb hML⟩
  exact ⟨b, hb, hD, hdiv⟩

/-- The actual source supplies every hypothesis of the bounded Frobenius kernel. -/
theorem actual_conic_firstNumerator_normalized (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    firstNumerator conicA ((actualLegendreJacobi p).comp Tc)
      ((shiftedChiField p hp).comp B) (forcingE p) =
      (actualLegendreJacobi p).comp Tc *
        (C (5 : ZMod p) * X ^ p * conicA ^ p) := by
  obtain ⟨b, hb, hD, hA⟩ := actual_conic_quotient p hp
  obtain ⟨hdeg, hodd, h1, hhalf, htop⟩ := actual_kernel_data p hp b hb hA
  have hnorm := bounded_conic_kernel_normalized p hp b hD hdeg hodd h1 hhalf htop
  rw [hnorm] at hb
  exact hb

end WPFieldAssembly.ActualConicNormalization
