import WPFiniteABSourceTail

open Polynomial

namespace WPFinitePrimitiveTransport

open WPFiniteProductTail

variable {K : Type*} [Field K]

theorem zero_of_derivative_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree < p) (hder : Q.derivative = 0)
    (hz : Q.eval 0 = 0) : Q = 0 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_eval_zero, eval_zero] using hz
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
  have hsmall : n ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have he : Q.coeff n * (n : K) = 0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (n - 1)) hder
    simpa only [coeff_derivative, ← Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p n hsmall)

/-- Transport a genuine sub-p, zero-origin source primitive to the literal finite one. -/
theorem unitPrimitiveP_unique (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) (z : K)
    (Q : K[X]) (hQ : Q.natDegree < p) (hQ0 : Q.eval 0 = 0)
    (hsource : (X - C z) * Q.derivative = W - C (W.eval z)) :
    Q = unitPrimitiveP p W z := by
  have hp := (Fact.out : p.Prime).pos
  have hX : (X - C z : K[X]) ≠ 0 := sub_ne_zero.mpr (X_ne_C z)
  have hder : (Q - unitPrimitiveP p W z).derivative = 0 := by
    apply (mul_eq_zero.mp (show (X - C z) * (Q - unitPrimitiveP p W z).derivative = 0 by
      rw [derivative_sub, mul_sub, hsource, unitPrimitiveP_source p W hW h0, sub_self])).resolve_left hX
  have hd : (Q - unitPrimitiveP p W z).natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hQ ((unitPrimitiveP_degree p W z).trans_lt (by omega)))
  have hz : (Q - unitPrimitiveP p W z).eval 0 = 0 := by
    rw [eval_sub, hQ0, unitPrimitiveP_zero, sub_self]
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hd hder hz)

theorem unitPrimitiveP_actual_eval (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) (z : K)
    (Q : K[X]) (hQ : Q.natDegree < p) (hQ0 : Q.eval 0 = 0)
    (hsource : (X - C z) * Q.derivative = W - C (W.eval z)) (y : K) :
    Q.eval y = unitPrimitive p W z y := by
  rw [unitPrimitiveP_unique p W hW h0 z Q hQ hQ0 hsource, unitPrimitiveP_eval]

theorem originPrimitiveP_unique (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0)
    (Q : K[X]) (hQ : Q.natDegree < p) (hQ0 : Q.eval 0 = 0)
    (hsource : X * Q.derivative = W) (y : K) : Q.eval y = originPrimitive p W y := by
  have he : (X - C (0 : K)) * Q.derivative = W - C (W.eval 0) := by
    rw [map_zero, sub_zero, ← coeff_zero_eq_eval_zero, h0, map_zero, sub_zero, hsource]
  rw [unitPrimitiveP_actual_eval p W hW h0 0 Q hQ hQ0 he y, unitPrimitive_origin]

end WPFinitePrimitiveTransport
