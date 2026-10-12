import WPFieldAssembly.SourceClosureUVWeightedK0
import WPFieldAssembly.SourceClosureUniversalLog

open scoped LaurentPolynomial Polynomial
open LaurentPolynomial WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedBands
  WPFieldAssembly.SourceClosureUniversalLog

namespace WPFieldAssembly.SourceClosureUVWeightedLog

/- The full ell/R cutoff is traced before finite inversion is used.
   Every derivative-invisible negative Frobenius shift is retained. -/

theorem weighted_nonpositive (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n≤0) (c : ZMod p) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c*T n)=0 := by
  rw [original_weight_monomial p hp n (by omega) c,
    endpointTrace_monomial, endpointTrace_monomial,
    endpointWeight_nonpositive _ _ _ hn,
    endpointWeight_nonpositive _ _ _ (by omega)]
  ring

theorem weighted_low_monomial (p n : ℕ) [Fact p.Prime] (hp : 19≤p)
    (hn : 0<n) (hnp : n<p) (c : ZMod p) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c*T (n : ℤ))=
      3*(2*c*(4 : ZMod p)^n+c*(1/4 : ZMod p)^n) := by
  rw [original_weight_monomial p hp n (by omega) c,
    endpointTrace_monomial, endpointTrace_monomial,
    endpointWeight_nonpositive _ _ ((n : ℤ)-(p : ℤ)) (by omega),
    endpointWeight_nat, if_neg (by omega)]
  ring

theorem weighted_low_sum (p : ℕ) [Fact p.Prime] (hp : 19≤p) (d : ℕ → ZMod p) :
    originalWeightedFieldTrace p (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (d j)*T (j : ℤ))=
      3*(2*(∑ j∈Finset.Ico 1 p, d j*(4 : ZMod p)^j)+
        ∑ j∈Finset.Ico 1 p, d j*(1/4 : ZMod p)^j) := by
  have hsum : originalWeightedFieldTrace p
      (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (d j)*T (j : ℤ)) =
      ∑ j∈Finset.Ico 1 p, originalWeightedFieldTrace p
        (LaurentPolynomial.C (d j)*T (j : ℤ)) := by
    simp only [originalWeightedFieldTrace, Finset.mul_sum, map_sum]
  rw [hsum]
  calc
    _ = ∑ j∈Finset.Ico 1 p, 3*(2*d j*(4 : ZMod p)^j+d j*(1/4 : ZMod p)^j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact weighted_low_monomial p j hp (by have := Finset.mem_Ico.mp hj; omega)
        (Finset.mem_Ico.mp hj).2 (d j)
    _ = ∑ j∈Finset.Ico 1 p,
        3*(2*(d j*(4 : ZMod p)^j)+d j*(1/4 : ZMod p)^j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [←Finset.mul_sum, Finset.sum_add_distrib, ←Finset.mul_sum]

theorem weighted_shift_low_sum (p : ℕ) [Fact p.Prime] (hp : 19≤p) (d : ℕ → ZMod p) :
    originalWeightedFieldTrace p
      (T (-(p : ℤ))*(∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (d j)*T (j : ℤ)))=0 := by
  simp only [originalWeightedFieldTrace, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*
      (LaurentPolynomial.C (d j)*T (j : ℤ))=
        LaurentPolynomial.C (d j)*T ((j : ℤ)-(p : ℤ)) := by
    rw [mul_comm (T (-(p : ℤ))), mul_assoc, ←T_add]
    congr 1
  rw [ht]
  exact weighted_nonpositive p hp _ (by have := (Finset.mem_Ico.mp hj).2; omega) _

theorem weighted_scaledLog (p : ℕ) [Fact p.Prime] (hp : 19≤p) (c : ZMod p) :
    originalWeightedFieldTrace p (scaledLog p c)=
      3*(2*WPFiniteField.ell p (4*c)+WPFiniteField.ell p (c/4)) := by
  rw [scaledLog_full, weighted_low_sum p hp]
  have h (z : ZMod p) : (∑ j∈Finset.Ico 1 p, c^j/(j : ZMod p)*z^j)=
      WPFiniteField.ell p (c*z) := by
    unfold WPFiniteField.ell
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  rw [h 4, h (1/4), show c*4=4*c by ring, show c*(1/4)=c/4 by ring]

theorem weighted_scaledDilog (p : ℕ) [Fact p.Prime] (hp : 19≤p) (c : ZMod p) :
    originalWeightedFieldTrace p (scaledDilog p c)=
      3*(2*WPFiniteField.R p (4*c)+WPFiniteField.R p (c/4)) := by
  rw [scaledDilog_full, weighted_low_sum p hp]
  have h (z : ZMod p) : (∑ j∈Finset.Ico 1 p, c^j/(j : ZMod p)^2*z^j)=
      WPFiniteField.R p (c*z) := by
    unfold WPFiniteField.R
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  rw [h 4, h (1/4), show c*4=4*c by ring, show c*(1/4)=c/4 by ring]

theorem weighted_shift_scaledLog (p : ℕ) [Fact p.Prime] (hp : 19≤p) (c : ZMod p) :
    originalWeightedFieldTrace p (T (-(p : ℤ))*scaledLog p c)=0 := by
  rw [scaledLog_full, weighted_shift_low_sum p hp]

theorem weighted_shift_scaledDilog (p : ℕ) [Fact p.Prime] (hp : 19≤p) (c : ZMod p) :
    originalWeightedFieldTrace p (T (-(p : ℤ))*scaledDilog p c)=0 := by
  rw [scaledDilog_full, weighted_shift_low_sum p hp]

end WPFieldAssembly.SourceClosureUVWeightedLog
