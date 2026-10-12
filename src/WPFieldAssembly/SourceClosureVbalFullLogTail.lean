import WPFiniteABSourceTail
import WPFiniteLogProduct

open scoped BigOperators Polynomial
open Polynomial WPFiniteAffineLog WPFiniteProductTail WPFiniteABSourceTail
  WPFiniteDReciprocity

namespace WPFieldAssembly.SourceClosureVbalFullLogTail

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- Both logarithms retain their original unit ranges through p-1. -/
theorem scaled_log_unit_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (c d z : K) :
    unitPrimitive p ((LP p).comp (Polynomial.C c*X)) z d⁻¹=
      WPFiniteLoop.D (p-1) (c/d) (c*z) ∧
    originPrimitive p ((LP p).comp (Polynomial.C c*X)) d⁻¹=
      WPFiniteField.R p (c/d) := by
  have hp : 1≤p := (Fact.out : p.Prime).one_le
  constructor
  · unfold unitPrimitive WPFiniteLoop.D
    rw [Nat.sub_add_cancel hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [LP_scaled_coeff,if_pos (Finset.mem_Ico.mp hi),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≤ i := by have := Finset.mem_Ico.mp hk; omega
    have hpow : c^k*c^(i-k)=c^i := by
      rw [←pow_add,Nat.add_sub_of_le hki]
    simp only [mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
    linear_combination -(d⁻¹^k*z^(i-k)*(i : K)⁻¹*(k : K)⁻¹)*hpow
  · unfold originPrimitive WPFiniteField.R
    apply Finset.sum_congr rfl
    intro i hi
    rw [LP_scaled_coeff,if_pos (Finset.mem_Ico.mp hi)]
    simp only [div_eq_mul_inv,inv_pow]
    ring

/-- The full strict upper product tail excludes its separate coefficient-p row. -/
theorem full_log_product_strict_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (c d z : K) (hd : d≠0) :
    (strictTail p (((LP p).comp (Polynomial.C c*X))*
      ((LP p).comp (Polynomial.C d*X)))).eval z=
      -d^p*(WPFiniteLoop.D (p-1) (c/d) (c*z)-WPFiniteField.R p (c/d)) := by
  have hdeg : ((LP p : K[X]).comp (Polynomial.C c*X)).natDegree<p := by
    apply lt_of_le_of_lt _ (Nat.sub_lt (Fact.out : p.Prime).pos (by omega : 0<1))
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [LP_scaled_coeff,if_neg (by omega)]
  have hzero : ((LP p : K[X]).comp (Polynomial.C c*X)).coeff 0=0 := by
    rw [LP_scaled_coeff,if_neg (by omega)]
  rw [full_product_tail_value p _ hdeg hzero d hd,
    (scaled_log_unit_primitive (K:=K) p c d z).1,
    (scaled_log_unit_primitive (K:=K) p c d z).2]

/-- In particular the full self-square has its original strict endpoint projection. -/
theorem full_log_square_strict_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (c z : K) (hc : c≠0) :
    (strictTail p (((LP p).comp (Polynomial.C c*X))^2)).eval z=
      -c^p*(WPFiniteLoop.D (p-1) 1 (c*z)-WPFiniteField.R p 1) := by
  rw [pow_two,full_log_product_strict_tail p c c z hc,div_self hc]

private theorem full_unit_values (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    WPFiniteField.ell p (1 : K)=0 ∧ WPFiniteField.R p (1 : K)=0 := by
  constructor
  · have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.ell_castHom,map_one,map_zero] using he
  · have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.R_castHom,map_one,map_zero] using he

private theorem H2_diagonal (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    H2 p t t=t^p*WPFiniteField.R p 1 := by
  unfold H2 WPFiniteField.R
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : k≤p := (Finset.mem_Ico.mp hk).2.le
  rw [←pow_add,Nat.add_sub_of_le hkp,one_pow]
  ring

/-- The diagonal correction is retained in the same full-range mixed shuffle. -/
theorem full_D_one_left (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (t : K) :
    WPFiniteLoop.D (p-1) 1 t+2*WPFiniteLoop.D (p-1) t 1=
      2*WPFiniteField.R p t := by
  have he := D_second_reciprocity (K:=K) p t (1 : K) one_ne_zero
  simp only [one_pow,div_one,H2,mul_one,one_mul] at he
  change WPFiniteLoop.D (p-1) t 1=-T2 p t 1+WPFiniteField.R p t at he
  rw [T2,(full_unit_values (K:=K) p hp).2] at he
  linear_combination he

/-- The full self-product fixes the two reciprocal proper D rows together. -/
theorem full_log_diagonal_shuffle (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (t : K) (ht : t≠0) (htp : t^p=t) :
    WPFiniteField.ell p t^2=
      2*t*(WPFiniteLoop.D (p-1) t 1+WPFiniteLoop.D (p-1) t⁻¹ 1)-
        2*(1+t)*WPFiniteField.R p t := by
  have hR1 := (full_unit_values (K:=K) p hp).2
  have he := WPFiniteLogProduct.full_logarithm_product p t t ht ht
  have hD := D_reciprocity (K:=K) p t t ht
  have hDi := D_reciprocity (K:=K) p t⁻¹ t⁻¹ (inv_ne_zero ht)
  rw [div_self ht,htp] at hD
  rw [div_self (inv_ne_zero ht),inv_inv,inv_pow,htp] at hDi
  simp only [H2_diagonal,hR1,mul_zero,sub_zero,T2,hD,hDi,htp,
    WPFiniteField.R_inversion p t ht] at he
  have hti : t*t⁻¹=1 := mul_inv_cancel₀ ht
  rw [←pow_two] at he
  linear_combination he+2*t*(WPFiniteLoop.D (p-1) t 1)*hti-
    2*t*(WPFiniteField.R p t)*hti

private theorem full_D_unit_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : WPFiniteLoop.D (p-1) (1 : K) 1=0 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hu := full_unit_values (K:=K) p hp
  have he := WPFiniteLogProduct.full_logarithm_product p (1 : K) 1 one_ne_zero one_ne_zero
  rw [hu.1,mul_zero,one_pow,inv_one,H2_diagonal,hu.2,mul_zero,sub_zero,T2] at he
  rw [hu.2] at he
  apply mul_left_cancel₀ h2
  apply mul_left_cancel₀ h2
  simp only [mul_zero]
  linear_combination -he

/-- Corrected NC118f uses the original a+2b orientation of the two strict tails. -/
theorem actual_full_log_difference_square_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p ((((LP p : K[X]).comp (Polynomial.C 4*X))-
      (LP p).comp (Polynomial.C (1/4)*X))^2)).eval (1/4)+
    2*(strictTail p ((((LP p : K[X]).comp (Polynomial.C 4*X))-
      (LP p).comp (Polynomial.C (1/4)*X))^2)).eval 4=
      33*WPFiniteField.ell p (16 : K)^2/64 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h16 : (16 : K)≠0 := by rw [show (16 : K)=2^4 by ring]; exact pow_ne_zero _ h2
  have h64 : (64 : K)≠0 := by rw [show (64 : K)=2^6 by ring]; exact pow_ne_zero _ h2
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have h16p : (16 : K)^p=16 := WPFiniteField.natCast_pow_char p 16
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have hpoly (B A : K[X]) : (B-A)^2=B^2+A^2-Polynomial.C (2 : K)*(B*A) := by
    simp only [map_ofNat]
    ring
  rw [hpoly,strictTail_sub p (by omega),strictTail_add p (by omega),
    strictTail_C_mul p (by omega)]
  simp only [eval_sub,eval_add,eval_mul,eval_C]
  rw [full_log_square_strict_tail p 4 (1/4) h4,
    full_log_square_strict_tail p (1/4) (1/4) (one_div_ne_zero h4),
    full_log_product_strict_tail p 4 (1/4) (1/4) (one_div_ne_zero h4),
    full_log_square_strict_tail p 4 4 h4,
    full_log_square_strict_tail p (1/4) 4 (one_div_ne_zero h4),
    full_log_product_strict_tail p 4 (1/4) 4 (one_div_ne_zero h4),h4p,hap]
  have ha4 : (1/4 : K)*4=1 := by field_simp [h4]
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  have haa : (1/4 : K)*(1/4)=(16 : K)⁻¹ := by field_simp [h4,h16]; ring
  have h44 : (4 : K)*4=16 := by ring
  have hda : (4 : K)/(1/4)=16 := by field_simp [h4]; ring
  rw [ha4,h4a,haa,h44,hda,(full_unit_values (K:=K) p hp).2,
    full_D_unit_diagonal p hp,
    D_reciprocity p (16 : K) 16 h16,div_self h16,h16p]
  have hmix := full_D_one_left (K:=K) p hp (16 : K)
  have hmixi := full_D_one_left (K:=K) p hp (16 : K)⁻¹
  have hdiag := full_log_diagonal_shuffle (K:=K) p hp (16 : K) h16 h16p
  rw [WPFiniteField.R_inversion p (16 : K) h16,h16p] at hmixi
  linear_combination (norm := (field_simp [h4,h16,h64]; ring))
    -8*hmix-hmixi/4-33*hdiag/64

end WPFieldAssembly.SourceClosureVbalFullLogTail
