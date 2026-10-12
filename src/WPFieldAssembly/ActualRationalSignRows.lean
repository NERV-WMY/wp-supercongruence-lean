import WPFiniteHomogeneousD
import WPKFifthEndpoint

open scoped BigOperators
open WPFiniteField WPFiniteSignTrace WPFiniteDReciprocity

namespace WPFieldAssembly.ActualRationalSignRows

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

noncomputable def q2 (p : ℕ) : K := WPFiniteInversion.integerFermatQuotient p 2
noncomputable def q3 (p : ℕ) : K := WPFiniteInversion.integerFermatQuotient p 3

private theorem small_ne (p a : ℕ) [Fact p.Prime] [CharP K p]
    (ha : 0<a) (hap : a<p) : (a : K)≠0 :=
  denominator_ne_zero p a (Finset.mem_Ico.mpr ⟨ha,hap⟩)

private theorem H2_joint_neg (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x y : K) : H2 p (-x) (-y)=-H2 p x y := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  unfold H2
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [neg_pow,neg_pow]
  have hs : (-1 : K)^j*(-1)^(p-j)=-1 := by
    rw [←pow_add,show j+(p-j)=p by omega,hodd.neg_one_pow]
  linear_combination (x^j*y^(p-j)/(j : K)^2)*hs

private theorem H2_zero_right (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    H2 p x 0=0 := by
  unfold H2
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [zero_pow (by omega : p-j≠0),mul_zero,zero_div]

/-- The full four-sign trace is the original six homogeneous terms, even at Y=1. -/
theorem fullTraceS_six_H2 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x y : K) :
    fullTraceS p x y=H2 p (x-y) (1-y)+H2 p (-x-y) (1-y)-2*H2 p (-y) (1-y)+
      H2 p (x+y) (1+y)+H2 p (-x+y) (1+y)-2*H2 p y (1+y) := by
  unfold fullTraceS
  rw [WPFiniteHomogeneousD.full_D_three_H2 p hp,
    WPFiniteHomogeneousD.full_D_three_H2 p hp,
    WPFiniteHomogeneousD.full_D_three_H2 p hp,
    WPFiniteHomogeneousD.full_D_three_H2 p hp]
  have h₁ := H2_joint_neg p hp (y-x) y
  have h₂ := H2_joint_neg p hp (y+x) y
  rw [show -(y-x)= -y+x by ring] at h₁
  rw [show -(y+x)= -y-x by ring] at h₂
  simp only [sub_neg_eq_add,neg_neg]
  linear_combination h₁+h₂

private theorem R_zero (p : ℕ) [Fact p.Prime] [CharP K p] : R p (0 : K)=0 := by
  unfold R
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).1
  rw [zero_pow (by omega : j≠0),zero_div]

private theorem R_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (1 : K)=0 := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_one_eq_zero p (by omega))
  simpa only [←R_castHom,map_one,map_zero] using h

private theorem R_neg_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (-1 : K)=0 := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_neg_one_eq_zero p hp)
  simpa only [←R_castHom,map_neg,map_one,map_zero] using h

private theorem R_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (2 : K)=-(q2 (K := K) p)^2 := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_two_eq_fermat p hp)
  simpa only [q2,←R_castHom,map_ofNat,map_neg,map_pow,map_intCast] using h

private theorem R_four (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (4 : K)= -6*(q2 (K := K) p)^2-2*R p (-2 : K) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_four_eq_fermat p hp)
  simpa only [q2,←R_castHom,map_ofNat,map_neg,map_sub,map_mul,map_pow,map_intCast]
    using h

private theorem R_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (1/2 : K)=-(q2 (K := K) p)^2/2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have hpow : (2 : K)^p=2 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 2
  rw [one_div,R_inversion p (2 : K) h2,hpow,R_two p hp]
  ring

private theorem R_neg_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (-1/2 : K)= -R p (-2 : K)/2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have hpow : (-2 : K)^p= -2 := by
    rw [(Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow]
    simpa only [Nat.cast_ofNat] using congrArg Neg.neg (natCast_pow_char (K := K) p 2)
  rw [show (-1/2 : K)=(-2)⁻¹ by simp only [inv_neg,one_div,neg_div],
    R_inversion p (-2 : K) (neg_ne_zero.mpr h2),hpow]
  simp only [inv_neg,div_eq_mul_inv]
  ring

private theorem R_three (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (3 : K)=(2/3 : K)*R p (-2 : K)-(2*q2 (K := K) p-3*q3 p)^2/6 := by
  have h := R_weight_two_reflection p (by omega) (-2 : K)
  rw [show (1-(-2) : K)=3 by ring,
    (Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow,
    WPFiniteLoop.ell_neg_two p hp] at h
  have h2p : (2 : K)^p=2 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 2
  have h3p : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  rw [h2p,h3p] at h
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  dsimp only [q2,q3]
  linear_combination (norm := (field_simp [h2,h3,h6]; ring)) (1/3 : K)*h

private theorem R_third (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (1/3 : K)=(2/9 : K)*R p (-2 : K)-(2*q2 (K := K) p-3*q3 p)^2/18 := by
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have hpow : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  rw [one_div,R_inversion p (3 : K) h3,hpow,R_three p hp]
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  field_simp [h3,h6,h9,h18]
  ring

private theorem R_quarter (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (1/4 : K)= -(3/2 : K)*(q2 (K := K) p)^2-R p (-2 : K)/2 := by
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have hpow : (4 : K)^p=4 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 4
  rw [one_div,R_inversion p (4 : K) h4,hpow,R_four p hp]
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  field_simp [h2,h4]
  ring

private theorem ell_third (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    ell p (1/3 : K)=q3 (K := K) p-(2/3 : K)*q2 p := by
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h := ell_reflection p (by omega) (3 : K)
  rw [show (1-3 : K)= -2 by ring,WPFiniteLoop.ell_neg_two p hp] at h
  have hpow : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  rw [one_div,ell_inversion p (3 : K) h3,hpow,←h]
  dsimp only [q2,q3]
  field_simp [h3]
  ring

private theorem ell_quarter (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    ell p (1/4 : K)=2*q2 (K := K) p-(3/4 : K)*q3 p := by
  have h3z : ((1-4 : ℤ) : ZMod p)≠0 := by
    simpa using small_ne (K := ZMod p) p 3 (by omega) (by omega)
  have h4z : ((4 : ℤ) : ZMod p)≠0 := by
    simpa using small_ne (K := ZMod p) p 4 (by omega) (by omega)
  have hpred : Even (p-1) := by
    obtain ⟨n,hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n,by omega⟩
  have hnegative : WPFiniteInversion.integerFermatQuotient p (1-4)=
      WPFiniteInversion.integerFermatQuotient p 3 := by
    rw [show (1-4 : ℤ)= -3 by norm_num]
    simp only [WPFiniteInversion.integerFermatQuotient,hpred.neg_pow]
  have hq := WPFiniteInversion.entropyQuotient_eq_fermat p 4 h4z h3z
  rw [hnegative] at hq
  have hz := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) 4
  rw [hq] at hz
  push_cast at hz
  rw [WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)] at hz
  have h := congrArg (ZMod.castHom (dvd_refl p) K) hz
  simp only [←ell_castHom,map_ofNat,map_sub,map_neg,map_mul,map_intCast] at h
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have hpow : (4 : K)^p=4 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 4
  rw [one_div,ell_inversion p (4 : K) h4,hpow,h]
  dsimp only [q2,q3]
  field_simp [h4]
  ring

private theorem R_two_thirds (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (2/3 : K)= -R p (-2 : K)/9-(2*q2 (K := K) p-3*q3 p)^2/18 := by
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have harg : (1-1/3 : K)=2/3 := by field_simp [h3]; ring
  have hpow : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  have h := R_weight_two_reflection p (by omega) (1/3 : K)
  rw [sub_pow_char,one_pow,div_pow,one_pow,hpow,harg,
    ell_third p hp,R_third p hp] at h
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  linear_combination (norm := (field_simp [h2,h3,h9,h18]; ring)) (3/2 : K)*h

private theorem R_three_halves (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (3/2 : K)= -R p (-2 : K)/6-(2*q2 (K := K) p-3*q3 p)^2/12 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have hpow : (2/3 : K)^p=2/3 := by
    rw [div_pow]
    have h2p : (2 : K)^p=2 := by
      simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 2
    have h3p : (3 : K)^p=3 := by
      simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
    rw [h2p,h3p]
  rw [show (3/2 : K)=(2/3)⁻¹ by rw [inv_div],
    R_inversion p (2/3 : K) (div_ne_zero h2 h3),hpow,R_two_thirds p hp]
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h12 : (12 : K)≠0 := small_ne (K := K) p 12 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  field_simp [h2,h3,h6,h9,h12,h18]
  ring

private theorem R_three_quarters (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (3/4 : K)=R p (-2 : K)/6-(13/6 : K)*(q2 (K := K) p)^2+
      2*q2 p*q3 p-(3/8 : K)*(q3 p)^2 := by
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have harg : (1-1/4 : K)=3/4 := by field_simp [h4]; ring
  have hpow : (4 : K)^p=4 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 4
  have h := R_weight_two_reflection p (by omega) (1/4 : K)
  rw [sub_pow_char,one_pow,div_pow,one_pow,hpow,harg,
    ell_quarter p hp,R_quarter p hp] at h
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h8 : (8 : K)≠0 := small_ne (K := K) p 8 (by omega) (by omega)
  linear_combination (norm := (field_simp [h2,h3,h4,h6,h8]; ring)) (4/3 : K)*h

private theorem R_neg_third (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (-1/3 : K)= -R p (-3 : K)/3 := by
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have hpow : (-3 : K)^p= -3 := by
    rw [(Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow]
    simpa only [Nat.cast_ofNat] using congrArg Neg.neg (natCast_pow_char (K := K) p 3)
  rw [show (-1/3 : K)=(-3)⁻¹ by simp only [inv_neg,one_div,neg_div],
    R_inversion p (-3 : K) (neg_ne_zero.mpr h3),hpow]
  simp only [inv_neg,div_eq_mul_inv]
  ring

private theorem R_four_thirds (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    R p (4/3 : K)=(4/3 : K)*R p (3/4 : K) := by
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have hpow : (3/4 : K)^p=3/4 := by
    rw [div_pow]
    have h3p : (3 : K)^p=3 := by
      simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
    have h4p : (4 : K)^p=4 := by
      simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 4
    rw [h3p,h4p]
  rw [show (4/3 : K)=(3/4)⁻¹ by rw [inv_div],
    R_inversion p (3/4 : K) (div_ne_zero h3 h4),hpow,inv_div]

theorem fullTraceS_right_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x : K) :
    fullTraceS p x 1=2*(R p ((1+x)/2)+R p ((1-x)/2)-2*R p (1/2 : K)) := by
  rw [fullTraceS_six_H2 p hp]
  simp only [sub_self,H2_zero_right,zero_add,zero_sub,
    show (1+1 : K)=2 by ring]
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  rw [WPFiniteHomogeneousD.H2_scaled_R p _ 2 h2,
    WPFiniteHomogeneousD.H2_scaled_R p _ 2 h2,
    WPFiniteHomogeneousD.H2_scaled_R p _ 2 h2]
  have hpow : (2 : K)^p=2 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 2
  rw [hpow,show (x+1 : K)=1+x by ring,show (-x+1 : K)=1-x by ring]
  ring

theorem fullTraceS_right_two (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x : K) :
    fullTraceS p x 2= -R p (2-x)-R p (2+x)+2*R p (2 : K)+
      3*(R p ((2+x)/3)+R p ((2-x)/3)-2*R p (2/3 : K)) := by
  rw [fullTraceS_six_H2 p hp,
    show (1-2 : K)= -1 by ring,show (1+2 : K)=3 by ring]
  have hm : (-1 : K)≠0 := neg_ne_zero.mpr one_ne_zero
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  rw [WPFiniteHomogeneousD.H2_scaled_R p _ (-1) hm,
    WPFiniteHomogeneousD.H2_scaled_R p _ (-1) hm,
    WPFiniteHomogeneousD.H2_scaled_R p _ (-1) hm,
    WPFiniteHomogeneousD.H2_scaled_R p _ 3 h3,
    WPFiniteHomogeneousD.H2_scaled_R p _ 3 h3,
    WPFiniteHomogeneousD.H2_scaled_R p _ 3 h3,
    (Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_one_pow]
  have hpow : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  rw [hpow]
  simp only [div_neg,div_one,neg_sub,sub_neg_eq_add,neg_neg]
  rw [show (x+2 : K)=2+x by ring,show (-x+2 : K)=2-x by ring]
  ring

theorem fullTraceS_right_half (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x : K) :
    fullTraceS p x (1/2)=
      (R p (2*x-1)+R p (-2*x-1))/2+
      (3/2 : K)*(R p ((1+2*x)/3)+R p ((1-2*x)/3)-2*R p (1/3 : K)) := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have ha : (1-1/2 : K)=1/2 := by field_simp [h2]; ring
  have hb : (1+1/2 : K)=3/2 := by field_simp [h2]; ring
  have hhalf : (1/2 : K)≠0 := div_ne_zero one_ne_zero h2
  have hthreehalf : (3/2 : K)≠0 := div_ne_zero h3 h2
  rw [fullTraceS_six_H2 p hp,ha,hb]
  rw [WPFiniteHomogeneousD.H2_scaled_R p _ (1/2) hhalf,
    WPFiniteHomogeneousD.H2_scaled_R p _ (1/2) hhalf,
    WPFiniteHomogeneousD.H2_scaled_R p _ (1/2) hhalf,
    WPFiniteHomogeneousD.H2_scaled_R p _ (3/2) hthreehalf,
    WPFiniteHomogeneousD.H2_scaled_R p _ (3/2) hthreehalf,
    WPFiniteHomogeneousD.H2_scaled_R p _ (3/2) hthreehalf]
  have h2p : (2 : K)^p=2 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 2
  have h3p : (3 : K)^p=3 := by
    simpa only [Nat.cast_ofNat] using natCast_pow_char (K := K) p 3
  rw [div_pow,one_pow,h2p,div_pow,h3p,h2p]
  have ha₁ : (x-1/2 : K)/(1/2)=2*x-1 := by field_simp [h2]
  have ha₂ : (-x-1/2 : K)/(1/2)= -2*x-1 := by field_simp [h2]
  have ha₃ : (-(1/2) : K)/(1/2)= -1 := by field_simp [h2]
  have hb₁ : (x+1/2 : K)/(3/2)=(1+2*x)/3 := by field_simp [h2,h3]; ring
  have hb₂ : (-x+1/2 : K)/(3/2)=(1-2*x)/3 := by field_simp [h2,h3]; ring
  have hb₃ : (1/2 : K)/(3/2)=1/3 := by field_simp [h2,h3]
  rw [ha₁,ha₂,ha₃,hb₁,hb₂,hb₃,R_neg_one p hp]
  ring

theorem S_one_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (1 : K) 1=2*(q2 (K := K) p)^2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  rw [fullTraceS_right_one p hp,
    show (1+1 : K)=2 by ring,div_self h2,
    sub_self,zero_div,R_one p hp,R_zero,R_half p hp]
  field_simp [h2]
  ring

theorem S_half_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (1/2 : K) 1= -(2/3 : K)*R p (-2 : K)-
      (16/3 : K)*(q2 (K := K) p)^2+4*q2 p*q3 p-(3/4 : K)*(q3 p)^2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h8 : (8 : K)≠0 := small_ne (K := K) p 8 (by omega) (by omega)
  have ha : (1+1/2 : K)/2=3/4 := by field_simp [h2,h4]; ring
  have hb : (1-1/2 : K)/2=1/4 := by field_simp [h2,h4]; ring
  rw [fullTraceS_right_one p hp,ha,hb,R_three_quarters p hp,R_quarter p hp,R_half p hp]
  field_simp [h2,h3,h4,h6,h8]
  ring

theorem S_one_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (1 : K) 2=(2/3 : K)*R p (-2 : K)-
      (2/3 : K)*(q2 (K := K) p)^2-4*q2 p*q3 p+3*(q3 p)^2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  rw [fullTraceS_right_two p hp,
    show (2-1 : K)=1 by ring,show (2+1 : K)=3 by ring,div_self h3,
    R_one p hp,R_three p hp,R_two p hp,R_third p hp,R_two_thirds p hp]
  field_simp [h2,h3,h6,h9,h18]
  ring

theorem S_half_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (1/2 : K) (1/2)= -R p (-2 : K)/3+
      (2*q2 (K := K) p-3*q3 p)^2/12 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h12 : (12 : K)≠0 := small_ne (K := K) p 12 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  have ha : (2*(1/2)-1 : K)=0 := by field_simp [h2]; ring
  have hb : (-2*(1/2)-1 : K)= -2 := by field_simp [h2]; ring
  have hc : (1+2*(1/2) : K)/3=2/3 := by field_simp [h2,h3]; ring
  have hd : (1-2*(1/2) : K)/3=0 := by field_simp [h2,h3]; ring
  rw [fullTraceS_right_half p hp,ha,hb,hc,hd,R_zero,R_two_thirds p hp,R_third p hp]
  field_simp [h2,h3,h9,h12,h18]
  ring

theorem S_two_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (2 : K) 2=(10/3 : K)*R p (-2 : K)-
      (10/3 : K)*(q2 (K := K) p)^2+4*q2 p*q3 p+(3/2 : K)*(q3 p)^2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h8 : (8 : K)≠0 := small_ne (K := K) p 8 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  rw [fullTraceS_right_two p hp,sub_self,zero_div,
    show (2+2 : K)=4 by ring,R_zero,R_four p hp,R_two p hp,
    R_four_thirds p hp,R_three_quarters p hp,R_two_thirds p hp]
  field_simp [h2,h3,h6,h8,h9,h18]
  ring

theorem S_two_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (2 : K) 1= -(4/3 : K)*R p (-2 : K)+
      (4/3 : K)*(q2 (K := K) p)^2+2*q2 p*q3 p-(3/2 : K)*(q3 p)^2 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h12 : (12 : K)≠0 := small_ne (K := K) p 12 (by omega) (by omega)
  rw [fullTraceS_right_one p hp,
    show (1+2 : K)=3 by ring,show (1-2 : K)= -1 by ring,
    R_three_halves p hp,R_neg_half p hp,R_half p hp]
  field_simp [h2,h3,h6,h12]
  ring

theorem S_one_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullTraceS p (1 : K) (1/2)= -(2/3 : K)*R p (-2 : K)+
      (2*q2 (K := K) p-3*q3 p)^2/6 := by
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h9 : (9 : K)≠0 := small_ne (K := K) p 9 (by omega) (by omega)
  have h18 : (18 : K)≠0 := small_ne (K := K) p 18 (by omega) (by omega)
  rw [fullTraceS_right_half p hp,
    show (2*1-1 : K)=1 by ring,show (-2*1-1 : K)= -3 by ring,
    show (1+2*1 : K)=3 by ring,show (1-2*1 : K)= -1 by ring,
    div_self h3,R_one p hp,R_neg_third p hp,R_third p hp]
  field_simp [h2,h3,h6,h9,h18]
  ring

/-- SB103's complete ordered rational combination, with every original diagonal. -/
theorem SB103_ordered_rational_combination (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (-4*(fullTraceS p (1 : K) 2-fullTraceS p (1/2 : K) 1)+
      22*(fullTraceS p (1 : K) 1-fullTraceS p (1/2 : K) (1/2))+
      11*(fullTraceS p (2 : K) 2-fullTraceS p (1 : K) 1)+
      7*(fullTraceS p (2 : K) 1-fullTraceS p (1 : K) (1/2)))/10=
      (17/5 : K)*R p (-2 : K)-(18/5 : K)*(q2 (K := K) p)^2+
      (63/5 : K)*q2 p*q3 p-(18/5 : K)*(q3 p)^2 := by
  rw [S_one_two p hp,S_half_one p hp,S_one_one p hp,S_half_half p hp,
    S_two_two p hp,S_two_one p hp,S_one_half p hp]
  have h2 : (2 : K)≠0 := small_ne (K := K) p 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := small_ne (K := K) p 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := small_ne (K := K) p 4 (by omega) (by omega)
  have h5 : (5 : K)≠0 := small_ne (K := K) p 5 (by omega) (by omega)
  have h6 : (6 : K)≠0 := small_ne (K := K) p 6 (by omega) (by omega)
  have h10 : (10 : K)≠0 := small_ne (K := K) p 10 (by omega) (by omega)
  have h12 : (12 : K)≠0 := small_ne (K := K) p 12 (by omega) (by omega)
  field_simp [h2,h3,h4,h5,h6,h10,h12]
  ring

end WPFieldAssembly.ActualRationalSignRows
