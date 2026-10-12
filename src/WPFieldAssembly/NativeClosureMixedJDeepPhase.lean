import WPFieldAssembly.NativeClosureEndProduct

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualSimplePoleResidue
open WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.NativeClosureMixedJDeepPhase

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- The two full negative blocks and the polynomial positive block are retained. -/
noncomputable def deepPhaseNumerator (n2 n1 : ℕ) (P2 P1 Ppos : K[X]) : K[T;T⁻¹] :=
  T (-(n2 : ℤ))*P2.toLaurent+T (-(n1 : ℤ))*P1.toLaurent+Ppos.toLaurent

/-- The actual quadratic-pole detector, expressed through full Laurent evaluation. -/
theorem originPole_full_evaluation (F : K[T;T⁻¹]) (h4 : (4 : K)≠0) :
    originPole F =
      ((trunc F).eval (1/4)-ev (1/4) (div_ne_zero one_ne_zero h4) F-
        ((trunc F).eval 4-ev 4 h4 F))/15 := by
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  have hia : (1/4 : K)⁻¹=4 := by simp only [one_div,inv_inv]
  have hib : (4 : K)⁻¹=1/4 := by simp only [one_div]
  have hDa := endProduct_pole_evaluation F (1/4 : K) ha
  have hDb := endProduct_pole_evaluation F (4 : K) h4
  rw [hia] at hDa
  rw [hib] at hDb
  rw [originPole,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,hDa,hDb]

/-- A strict degree bound removes only the regular part, retaining every negative coefficient. -/
theorem originPole_strict_negative_phase (n : ℕ) (P : K[X])
    (hP : P.natDegree<n) (h4 : (4 : K)≠0) :
    originPole (T (-(n : ℤ))*P.toLaurent) =
      ((4 : K)^(-(n : ℤ))*P.eval 4-
        (1/4 : K)^(-(n : ℤ))*P.eval (1/4))/15 := by
  have htr : trunc (T (-(n : ℤ))*P.toLaurent)=0 := by
    simpa only [one_mul] using endProduct_trunc_negative_phase n 1 P
      (by simpa only [one_mul] using hP)
  rw [originPole_full_evaluation _ h4,htr]
  rw [endProduct_shifted_evaluation P (-(n : ℤ)) (1/4)
    (div_ne_zero one_ne_zero h4),endProduct_shifted_evaluation P (-(n : ℤ)) 4 h4]
  simp only [eval_zero]
  ring

/-- The whole discarded product is evaluated before its positive block is removed. -/
theorem originPole_three_blocks (n2 n1 : ℕ) (P2 P1 Ppos : K[X])
    (hP2 : P2.natDegree<n2) (hP1 : P1.natDegree<n1) (h4 : (4 : K)≠0) :
    originPole (deepPhaseNumerator n2 n1 P2 P1 Ppos) =
      ((4 : K)^(-(n2 : ℤ))*P2.eval 4+(4 : K)^(-(n1 : ℤ))*P1.eval 4-
        ((1/4 : K)^(-(n2 : ℤ))*P2.eval (1/4)+
          (1/4 : K)^(-(n1 : ℤ))*P1.eval (1/4)))/15 := by
  rw [deepPhaseNumerator,originPole_add,originPole_add,
    originPole_strict_negative_phase n2 P2 hP2 h4,
    originPole_strict_negative_phase n1 P1 hP1 h4,originPole_polynomial]
  ring

/-- The original prefactor and two-band endpoint table gives the full deep correction.
The degree and endpoint hypotheses concern the cleared polynomial blocks themselves. -/
theorem deep_phase_correction_from_two_band (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (n2 n1 : ℕ) (P2 P1 Ppos : K[X])
    (hP2 : P2.natDegree<n2) (hP1 : P1.natDegree<n1)
    (Ua Ub Va Vb c h q : K)
    (hAa : Ua/4+Va+c= -h) (hAb : 4*Ub+Vb+c= -h)
    (hphase_a :
      (1/4 : K)^(-(n2 : ℤ))*P2.eval (1/4)+
        (1/4 : K)^(-(n1 : ℤ))*P1.eval (1/4) =
          -256*h*Ub-16*h*(4*Vb+4*(4*c/3-q+h)-11*Ub))
    (hphase_b :
      (4 : K)^(-(n2 : ℤ))*P2.eval 4+(4 : K)^(-(n1 : ℤ))*P1.eval 4 =
        -h*Ua/4-h*(4*Va+4*(4*c/3-q+h)-11*Ua)/4) :
    originPole (deepPhaseNumerator n2 n1 P2 P1 Ppos) =
      h*(-176*Ub+11*Ua/4+21*c-63*q)/15 := by
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hva : Va= -h-c-Ua/4 := by linear_combination hAa
  have hvb : Vb= -h-c-4*Ub := by linear_combination hAb
  rw [originPole_three_blocks n2 n1 P2 P1 Ppos hP2 hP1 h4,hphase_a,hphase_b,hva,hvb]
  field_simp [h3,h4,h15]
  ring

/-- The same finite endpoint dictionary preserves all Fermat letters and constants. -/
theorem deep_phase_quotient_alphabet (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (q r k : K) :
    let h : K := -2*q-3*r/2
    let Ua : K := -4*((-2*q+3*r/4)+q)/5
    let Ub : K := -4*((q-3*r/2)+q)/5
    let c : K := 3*k/2-11*q/5-h
    h*(-176*Ub+11*Ua/4+21*c-63*q)/15 =
      h*(1083*q/5-3627*r/20+63*k/2)/15 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : K)≠0 := by
    rw [show (20 : K)=4*5 by ring]
    exact mul_ne_zero h4 h5
  dsimp only
  field_simp [h2,h4,h5,h15,h20]
  ring

end WPFieldAssembly.NativeClosureMixedJDeepPhase
