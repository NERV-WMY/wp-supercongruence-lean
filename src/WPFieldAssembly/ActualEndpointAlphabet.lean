import WPFieldAssembly.ActualEntropyEndpoints

open WPPIntegralReduction WPFiniteInversion

namespace WPFieldAssembly.ActualEndpointAlphabet

set_option maxHeartbeats 1000000

theorem R_negative_half (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    R p (-1/2)= -R p (-2)/2 := by
  have h2 : (2 : ZMod p)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he := R_inversion p (-2) (neg_ne_zero.mpr h2)
  rw [ZMod.pow_card] at he
  have hi : (-2 : ZMod p)⁻¹=(-1/2 : ZMod p) := by
    field_simp [h2]
  rw [hi] at he
  calc
    _ = (-1/2 : ZMod p)*R p (-2) := he
    _ = _ := by ring

theorem R_positive_half (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    R p (1/2)= -(integerFermatQuotient p 2 : ZMod p)^2/2 := by
  have h2 : (2 : ZMod p)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he := R_inversion p 2 h2
  rw [ZMod.pow_card,R_two_eq_fermat p hp] at he
  rw [show (2 : ZMod p)⁻¹=1/2 by simp only [one_div]] at he
  calc
    _ = (1/2 : ZMod p)*(-(integerFermatQuotient p 2 : ZMod p)^2) := he
    _ = _ := by ring

theorem R_three_half_relation (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    R p 3/2-R p (3/2)=R p (-2)/2 := by
  have h2 : (2 : ZMod p)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : ZMod p)≠0 := denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  have hi := ell_inversion p (-2) (neg_ne_zero.mpr h2)
  rw [ZMod.pow_card] at hi
  rw [show (-2 : ZMod p)⁻¹=(-1/2 : ZMod p) by field_simp [h2]] at hi
  have hL : ell p (-1/2)=ell p (-2)/2 := by
    calc
      _ = -(-1/2 : ZMod p)*ell p (-2) := hi
      _ = _ := by ring
  have hm := R_weight_two_reflection p (by omega) (-2)
  have hh := R_weight_two_reflection p (by omega) (-1/2)
  rw [ZMod.pow_card,ZMod.pow_card] at hm hh
  rw [show (1-(-2) : ZMod p)=3 by ring] at hm
  rw [show (1-(-1/2) : ZMod p)=3/2 by field_simp [h2]; ring,
    R_negative_half p hp,hL] at hh
  field_simp [h2] at hm hh
  have hm' : -4*R p (-2)+6*R p 3+(ell p (-2))^2=0 := by
    linear_combination hm
  have hh' : 2*R p (-2)+12*R p (3/2)+(ell p (-2))^2=0 := by
    linear_combination hh
  field_simp [h2]
  apply mul_left_cancel₀ h6
  linear_combination hm'-hh'

/-- The alphabet change acts on the same canonical rational R1 carry. -/
theorem literalR1Integral_alphabet (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (ActualEntropyEndpoints.literalR1Integral p hp)=
      R p (-2)/2-2*(integerFermatQuotient p 2 : ZMod p)^2+
      (3/2 : ZMod p)*(integerFermatQuotient p 2 : ZMod p)*
        (integerFermatQuotient p 3 : ZMod p) := by
  rw [ActualEntropyEndpoints.literalR1Integral_field p hp]
  unfold WPFiniteNC122.Aeven
  change -(-(R p (1-2)+R p (1+2))/2)+
      2*(-(R p (1-1/2)+R p (1+1/2))/2)-
      (5/2 : ZMod p)*(integerFermatQuotient p 2 : ZMod p)^2+
      (3/2 : ZMod p)*(integerFermatQuotient p 2 : ZMod p)*
        (integerFermatQuotient p 3 : ZMod p)=_
  have h2 : (2 : ZMod p)≠0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  rw [show (1-2 : ZMod p)=-1 by ring,show (1+2 : ZMod p)=3 by ring,
    show (1-1/2 : ZMod p)=1/2 by field_simp [h2]; ring,
    show (1+1/2 : ZMod p)=3/2 by field_simp [h2]; ring,
    R_neg_one_eq_zero p hp,R_positive_half p hp]
  have h := R_three_half_relation p hp
  rw [←h]
  field_simp [h2]
  ring

end WPFieldAssembly.ActualEndpointAlphabet
