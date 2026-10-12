import WPFiniteZSource
import WPKFifthEndpoint

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureUniversalLog

/- STATEMENT_FIDELITY: UW17b--d's original full-cutoff Jlog and J2log,
   with a=1/4 and b=4. The derivative is the literal Laurent derivative;
   the branch evaluation is x=-1, not coefficient zero. No finite input
   manifest is used. This unit does not yet identify Ucan, VS or their
   whole rational carry, and assigns no common-trace or NC77 value. -/

variable {K : Type*} [Field K]

noncomputable def scaledLog (p : ℕ) (c : K) : K[T;T⁻¹] :=
  ((WPFiniteAffineLog.LP p).comp (Polynomial.C c * X)).toLaurent

noncomputable def scaledDilog (p : ℕ) (c : K) : K[T;T⁻¹] :=
  ((WPFiniteKSource.RP p).comp (Polynomial.C c * X)).toLaurent

theorem scaledLog_full (p : ℕ) (c : K) :
    scaledLog p c = ∑ j ∈ Finset.Ico 1 p,
      LaurentPolynomial.C (c^j / (j : K)) * T (j : ℤ) := by
  unfold scaledLog WPFiniteAffineLog.LP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, mul_pow, map_sum,
    map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    LaurentPolynomial.T_pow, mul_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [←map_pow,←mul_assoc,←map_mul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

theorem scaledDilog_full (p : ℕ) (c : K) :
    scaledDilog p c = ∑ j ∈ Finset.Ico 1 p,
      LaurentPolynomial.C (c^j / (j : K)^2) * T (j : ℤ) := by
  unfold scaledDilog WPFiniteKSource.RP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, mul_pow, map_sum,
    map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    LaurentPolynomial.T_pow, mul_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [←map_pow,←mul_assoc,←map_mul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

theorem scaledDilog_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (c : K) :
    D (scaledDilog p c) = T (-1) * scaledLog p c := by
  rw [scaledDilog_full, scaledLog_full, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (j : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j hj
  rw [D_monomial]
  have hc : c^j/(j : K)^2 * ((j : ℤ) : K) = c^j/(j : K) := by
    simp only [Int.cast_natCast]
    field_simp [hj0]
  rw [hc]
  rw [mul_comm (T (-1)), mul_assoc, ←T_add]
  congr 2

noncomputable def originalJlog (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2/15 : K) *
    ((T (-(p : ℤ))-LaurentPolynomial.C (1/4 : K))*scaledLog p 4 -
      (T (-(p : ℤ))-LaurentPolynomial.C (4 : K))*scaledLog p (1/4))

noncomputable def originalJ2log (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2/15 : K) *
    ((T (-(p : ℤ))-LaurentPolynomial.C (1/4 : K))*scaledDilog p 4 -
      (T (-(p : ℤ))-LaurentPolynomial.C (4 : K))*scaledDilog p (1/4))

/-- The same full Laurent logarithm supplies every derivative coefficient. -/
theorem originalJ2log_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (originalJ2log p : K[T;T⁻¹]) = T (-1)*originalJlog p := by
  have hshift (c : K) (P : K[T;T⁻¹]) :
      D ((T (-(p : ℤ))-LaurentPolynomial.C c)*P) =
        (T (-(p : ℤ))-LaurentPolynomial.C c)*D P := by
    rw [sub_mul,map_sub,D_frobenius_shift p P _ (dvd_neg.mpr (dvd_refl _)),
      D_C_mul]
    ring
  rw [originalJ2log,D_C_mul,map_sub,hshift,hshift,
    scaledDilog_derivative,scaledDilog_derivative,originalJlog]
  ring

theorem scaledDilog_eval (p : ℕ) [Fact p.Prime] [CharP K p] (c : K) (x : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) x (scaledDilog p c) =
      WPFiniteField.R p (c*(x : K)) := by
  simp only [scaledDilog,LaurentPolynomial.eval₂_toLaurent,eval₂_id,
    eval_comp,eval_mul,eval_C,eval_X,WPFiniteKSource.RP_eval]

/-- The full dilogarithm term contributes R(-4)/6 to the original u0. -/
theorem originalJ2log_branch (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (originalJ2log p) =
      -(WPFiniteField.R p (-4 : K))/3 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpow : (-1 : K)^p = -1 := by simpa using hodd.neg_pow (1 : K)
  have h4pow : (-4 : K)^p = -4 := by
    rw [hodd.neg_pow (4 : K)]
    exact congrArg (fun x : K => -x) (WPFiniteField.natCast_pow_char (K := K) p 4)
  have hinv := WPFiniteField.R_inversion p (-4 : K) (neg_ne_zero.mpr h4)
  have hi : (-4 : K)⁻¹ = -(1/4 : K) := by simp only [inv_neg,one_div]
  rw [h4pow,hi] at hinv
  simp only [originalJ2log,map_mul,map_sub,LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T_neg_n,RingHom.id_apply,Units.val_neg,
    Units.val_one,inv_neg,inv_one,hpow,scaledDilog_eval]
  simp only [mul_neg,mul_one,one_div] at hinv ⊢
  rw [hinv]
  field_simp [h3,h4,h15]
  ring

end WPFieldAssembly.SourceClosureUniversalLog
