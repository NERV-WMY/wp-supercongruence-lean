import WPFieldAssembly.ActualFullA2
import WPFieldAssembly.ActualCubicUnitRoot
import WPKFifthEndpoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators Polynomial
open Polynomial WPFiniteJSource WPFiniteField
  WPFieldAssembly.ActualFullA2 WPFieldAssembly.ActualCubicUnitRoot

namespace WPFieldAssembly.ActualCubicWeightTwoTrace

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

noncomputable def cubicA2 (p : ℕ) : K :=
  ∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), (H (j-1) : K)/(j : K)

noncomputable def thirdHarmonicTwo (p : ℕ) : K :=
  ∑ j ∈ Finset.Ico 1 (p/3+1), 1/(j : K)^2

private theorem root_cube (u : K) (hu : u^2+u+1=0) : u^3=1 := by
  linear_combination (u-1)*hu

private theorem root_fourth (u : K) (hu : u^2+u+1=0) : u^4=u := by
  rw [show (4 : ℕ)=3+1 by omega, pow_add, root_cube u hu, pow_one, one_mul]

private theorem square_root (u : K) (hu : u^2+u+1=0) : (u^2)^2+u^2+1=0 := by
  rw [←pow_mul, show (2*2 : ℕ)=4 by omega, root_fourth u hu]
  linear_combination hu

theorem cubic_root_power_trace (u : K) (hu : u^2+u+1=0) (j : ℕ) :
    1+u^j+(u^2)^j=if 3 ∣ j then 3 else 0 := by
  have hmod : u^j=u^(j%3) := by
    conv_lhs => rw [←Nat.mod_add_div j 3]
    rw [pow_add, pow_mul, root_cube u hu, one_pow, mul_one]
  have hmod₂ : (u^2)^j=(u^2)^(j%3) := by
    conv_lhs => rw [←Nat.mod_add_div j 3]
    rw [pow_add, pow_mul, root_cube (u^2) (square_root u hu), one_pow, mul_one]
  rw [hmod, hmod₂]
  have hj := Nat.mod_lt j (by omega : 0 < 3)
  simp only [Nat.dvd_iff_mod_eq_zero]
  generalize hm : j%3=m at *
  interval_cases m
  · norm_num
  · norm_num
    linear_combination hu
  · norm_num
    linear_combination square_root u hu

theorem cubic_full_filter_trace (p : ℕ) (f : ℕ → K) (u : K)
    (hu : u^2+u+1=0) :
    (∑ j ∈ Finset.Ico 1 p, f j)+
      (∑ j ∈ Finset.Ico 1 p, f j*u^j)+
      (∑ j ∈ Finset.Ico 1 p, f j*(u^2)^j)=
      3*∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), f j := by
  rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrArg (fun a : K => f j*a) (cubic_root_power_trace u hu j)
  split_ifs at h ⊢ <;> linear_combination h

private theorem R_zero (p : ℕ) [Fact p.Prime] [CharP K p] : R p (0 : K)=0 := by
  unfold R
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos := (Finset.mem_Ico.mp hj).1
  simp only [zero_pow (by omega : j ≠ 0), zero_div]

private theorem R_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    R p (1 : K)=0 := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_one_eq_zero p (by omega))
  simpa only [←R_castHom, map_one, map_zero] using h

theorem cubic_harmonic_trace (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2+u+1=0) :
    (fullHarmonicPrimitive p : K[X]).eval u+
      (fullHarmonicPrimitive p : K[X]).eval (u^2)=3*cubicA2 p := by
  have h := cubic_full_filter_trace p
    (fun j => (H (j-1) : K)/(j : K)) u hu
  have hz : (fullHarmonicPrimitive p : K[X]).eval 1=0 := by
    rw [actual_full_dilog_value p hp, sub_self, R_zero, neg_zero]
  have he : (fullHarmonicPrimitive p : K[X]).eval 1=
      ∑ j ∈ Finset.Ico 1 p, (H (j-1) : K)/(j : K) := by
    simp only [fullHarmonicPrimitive, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_X, one_pow, mul_one]
  rw [←he, hz, zero_add] at h
  simpa only [fullHarmonicPrimitive, cubicA2, eval_finsetSum, eval_mul,
    eval_C, eval_pow, eval_X] using h

theorem cubic_dilog_trace (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2+u+1=0) :
    R p u+R p (u^2)=thirdHarmonicTwo (K := K) p/3 := by
  have h := cubic_full_filter_trace p (fun j => 1/(j : K)^2) u hu
  have h0 : (∑ j ∈ Finset.Ico 1 p, 1/(j : K)^2)=R p (1 : K) := by
    simp only [R, one_pow]
  rw [h0, R_one p hp, zero_add] at h
  have hf : (∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j),
      1/(j : K)^2)=thirdHarmonicTwo p/9 := by
    rw [WPActualHarmonicCubeFilter.cubic_filter_sum p (by omega)]
    unfold thirdHarmonicTwo
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have h3 : (3 : K) ≠ 0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
    have h9 : (9 : K) ≠ 0 := denominator_ne_zero p 9 (Finset.mem_Ico.mpr (by omega))
    have hu : (j : K) ≠ 0 := denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
    push_cast
    field_simp [h3, h9, hu]
    ring
  rw [hf] at h
  have he : R p u+R p (u^2)=3*(thirdHarmonicTwo (K := K) p/9) := by
    simpa only [R, one_div, div_eq_mul_inv, one_mul, mul_comm] using h
  rw [he]
  have h3 : (3 : K) ≠ 0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h9 : (9 : K) ≠ 0 := denominator_ne_zero p 9 (Finset.mem_Ico.mpr (by omega))
  field_simp [h3, h9]
  ring

/-- Algebraic cancellation of both cubic norm projections. -/
theorem cubic_norm_trace_algebra (w q R₁ R₂ A₁ A₂ : K)
    (h3 : (3 : K) ≠ 0)
    (hw : w^2+w+1=0) (hR : R₂=w^2*R₁)
    (h₁ : (1-w)*A₁=w*R₁+(1-w)^2*q^2/8)
    (h₂ : (1-w^2)*A₂=w^2*R₂+(1-w^2)^2*q^2/8) :
    A₁+A₂+R₁+R₂=3*q^2/8 := by
  have hprod : (1-w)*(1-w^2)=(3 : K) := by
    have hc := root_cube w hw
    linear_combination hc-hw
  have hsum : (1-w)+(1-w^2)=(3 : K) := by linear_combination -hw
  have hcoef : (1-w^2)*w+(1-w)*w^4=3*w := by
    rw [root_fourth w hw]
    linear_combination -w*hw
  have htrace : R₁+R₂=-w*R₁ := by
    rw [hR]
    linear_combination R₁*hw
  have ha : 3*(A₁+A₂)=3*w*R₁+9*q^2/8 := by
    rw [hR] at h₂
    have h := congrArg₂ (fun a b : K => a+b)
      (congrArg (fun a : K => (1-w^2)*a) h₁)
      (congrArg (fun a : K => (1-w)*a) h₂)
    have hl : (1-w^2)*((1-w)*A₁)+(1-w)*((1-w^2)*A₂)=3*(A₁+A₂) := by
      linear_combination (A₁+A₂)*hprod
    have hr : (1-w^2)*(w*R₁+(1-w)^2*q^2/8)+
        (1-w)*(w^2*(w^2*R₁)+(1-w^2)^2*q^2/8)=3*w*R₁+9*q^2/8 := by
      linear_combination R₁*hcoef+(q^2/8)*((1-w)+(1-w^2))*hprod+
        (3*q^2/8)*hsum
    rw [hl, hr] at h
    exact h
  rw [show A₁+A₂+R₁+R₂=A₁+A₂+(R₁+R₂) by ring, htrace]
  apply mul_left_cancel₀ h3
  linear_combination ha

private theorem root_ne_zero (u : K) (hu : u^2+u+1=0) : u ≠ 0 := by
  intro hz
  rw [hz] at hu
  norm_num at hu

private theorem root_inverse (u : K) (hu : u^2+u+1=0) : u⁻¹=u^2 := by
  have hz := root_ne_zero u hu
  field_simp [hz]
  linear_combination -(root_cube u hu)

/-- Both norm projections are attached to the actual integer cubic unit. -/
theorem actual_cubic_weight_two_root_trace (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2+u+1=0) :
    cubicA2 (K := K) p=
      (WPFiniteInversion.integerFermatQuotient p 3 : K)^2/8-
        thirdHarmonicTwo (K := K) p/9 := by
  let w := u^p
  let q : K := WPFiniteInversion.integerFermatQuotient p 3
  have hw : w^2+w+1=0 := by
    have h := congrArg (fun a : K => a^p) hu
    rw [add_pow_char, add_pow_char, one_pow,
      zero_pow (Fact.out : p.Prime).ne_zero] at h
    rw [←pow_mul, Nat.mul_comm 2 p, pow_mul] at h
    exact h
  have hR : R p (u^2)=w^2*R p u := by
    rw [←root_inverse u hu, R_inversion p u (root_ne_zero u hu), root_inverse w hw]
  have hn₁ := R_weight_two_reflection p (by omega) u
  have hn₂ := R_weight_two_reflection p (by omega) (u^2)
  rw [sub_pow_char, one_pow, actual_cubic_root_log p hp u hu] at hn₁
  rw [sub_pow_char, one_pow, actual_cubic_root_log p hp (u^2) (square_root u hu),
    ←pow_mul, Nat.mul_comm 2 p, pow_mul] at hn₂
  let A₁ := (fullHarmonicPrimitive p : K[X]).eval u
  let A₂ := (fullHarmonicPrimitive p : K[X]).eval (u^2)
  have h₁ : (1-w)*A₁=w*R p u+(1-w)^2*q^2/8 := by
    dsimp only [A₁]
    rw [actual_full_dilog_value p hp]
    change w*R p u+(1-w)*R p (1-u)=-(-(1-w)*q/2)^2/2 at hn₁
    have h2 : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
    have h8 : (8 : K) ≠ 0 := denominator_ne_zero p 8 (Finset.mem_Ico.mpr (by omega))
    field_simp [h2, h8] at hn₁ ⊢
    linear_combination -hn₁
  have h₂ : (1-w^2)*A₂=w^2*R p (u^2)+(1-w^2)^2*q^2/8 := by
    dsimp only [A₂]
    rw [actual_full_dilog_value p hp]
    change w^2*R p (u^2)+(1-w^2)*R p (1-u^2)=-(-(1-w^2)*q/2)^2/2 at hn₂
    have h2 : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
    have h8 : (8 : K) ≠ 0 := denominator_ne_zero p 8 (Finset.mem_Ico.mpr (by omega))
    field_simp [h2, h8] at hn₂ ⊢
    linear_combination -hn₂
  have h3 : (3 : K) ≠ 0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have he := cubic_norm_trace_algebra w q (R p u) (R p (u^2)) A₁ A₂ h3 hw hR h₁ h₂
  have hA := cubic_harmonic_trace p hp u hu
  have hD := cubic_dilog_trace p hp u hu
  change A₁+A₂=3*cubicA2 p at hA
  rw [show A₁+A₂+R p u+R p (u^2)=A₁+A₂+(R p u+R p (u^2)) by ring,
    hA, hD] at he
  have h8 : (8 : K) ≠ 0 := denominator_ne_zero p 8 (Finset.mem_Ico.mpr (by omega))
  have h9 : (9 : K) ≠ 0 := denominator_ne_zero p 9 (Finset.mem_Ico.mpr (by omega))
  dsimp only [q] at he
  field_simp [h3, h8, h9] at he ⊢
  linear_combination he

theorem cubicA2_map {F : Type*} [Field F] (φ : K →+* F) (p : ℕ) :
    φ (cubicA2 (K := K) p)=cubicA2 (K := F) p := by
  simp only [cubicA2, H, map_sum, map_div₀, map_inv₀, map_natCast]

theorem thirdHarmonicTwo_map {F : Type*} [Field F] (φ : K →+* F) (p : ℕ) :
    φ (thirdHarmonicTwo (K := K) p)=thirdHarmonicTwo (K := F) p := by
  simp only [thirdHarmonicTwo, map_sum, map_div₀, map_one, map_pow, map_natCast]

/-- No cube root in the prime field is assumed; both prime classes use the same source. -/
theorem actual_cubic_weight_two_trace (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    cubicA2 (K := K) p=
      (WPFiniteInversion.integerFermatQuotient p 3 : K)^2/8-
        thirdHarmonicTwo (K := K) p/9 := by
  let F := AlgebraicClosure K
  let φ : K →+* F := algebraMap K F
  have hd : (X^2+X+1 : F[X]).degree=2 := by
    compute_degree <;> norm_num
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (X^2+X+1 : F[X]) (by rw [hd]; norm_num)
  have hu' : u^2+u+1=0 := by
    simpa only [Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_one] using hu
  apply φ.injective
  rw [cubicA2_map, map_sub, map_div₀, map_div₀, map_pow, map_intCast,
    map_ofNat, map_ofNat, thirdHarmonicTwo_map]
  exact actual_cubic_weight_two_root_trace p hp u hu'

end WPFieldAssembly.ActualCubicWeightTwoTrace
