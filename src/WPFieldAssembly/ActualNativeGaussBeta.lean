import WPFieldAssembly.ActualGaussHarmonic
import WPFieldAssembly.ActualGaussBeta
import WPActualRankTwoLegendreField

open WPActualNativeHasse WPActualRankTwoLegendreField

namespace WPFieldAssembly.ActualGaussHarmonic

set_option maxHeartbeats 1800000

/-- The original native coefficient recurrence at the actual integer Legendre degree. -/
theorem actual_native_legendre_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hn : n+1<p) :
    2*((n : ZMod p)+1)^3*(WPReview.nativeCoefficient (n+1) : ZMod p)=
      (2*(n : ZMod p)+1)*((n : ZMod p)-(p/6 : ℕ))*
        ((n : ZMod p)+(p/6 : ℕ)+1)*(WPReview.nativeCoefficient n : ZMod p) := by
  have h6 : (6 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h36 : (36 : ZMod p)≠0 := by
    convert pow_ne_zero 2 h6 using 1
    norm_num
  have he := actual_native_field_recurrence p n (by omega) hn
  rw [mul_assoc (2*(n : ZMod p)+1) (6*(n : ZMod p)+1) (6*(n : ZMod p)+5),
    rankField_legendre_factor p n (by omega)] at he
  apply mul_left_cancel₀ h36
  linear_combination he

/-- The exact unit beta factor converts the actual native coefficient to its integer row. -/
theorem actual_native_beta_product (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hn : 1≤n) (hd : n≤p/6) :
    2*(n : ZMod p)*(WPReview.nativeCoefficient n : ZMod p)*
      betaEndpoint (K:=ZMod p) p (n-1)=gaussA (K:=ZMod p) (p/6) n := by
  have hall : ∀ n : ℕ, 1≤n → n≤p/6 →
      2*(n : ZMod p)*(WPReview.nativeCoefficient n : ZMod p)*
        betaEndpoint (K:=ZMod p) p (n-1)=gaussA (K:=ZMod p) (p/6) n := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro _hlow htop
      by_cases hz : n=0
      · subst n
        have hc := actual_native_legendre_recurrence p 0 hp (by omega)
        have ha := gaussA_recurrence (K:=ZMod p) (p/6) 0
        simp only [Nat.cast_zero,zero_add,one_pow,one_mul,
          WPReview.nativeCoefficient_zero,Rat.cast_one,mul_one,gaussA_zero] at hc ha
        rw [show 0+1-1=0 by omega,betaEndpoint_zero_index p (by omega)]
        simp only [mul_one]
        linear_combination hc-ha
      · have hi := ih (by omega) (by omega)
        have hb := betaEndpoint_recurrence (K:=ZMod p) p (n-1) (by omega)
        have he := actual_native_legendre_recurrence p n hp (by omega)
        have ha := gaussA_recurrence (K:=ZMod p) (p/6) n
        have hu : ((n+1 : ℕ) : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p (n+1)
          (Finset.mem_Ico.mpr (by omega))
        have hhb : 2*(n-1)+3=2*n+1 := by omega
        have hhn : 2*(n-1)+2=2*n := by omega
        rw [Nat.sub_add_cancel (by omega : 1≤n),hhb,hhn] at hb
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hb
        rw [show n+1-1=n by omega]
        apply mul_left_cancel₀ (pow_ne_zero 2 hu)
        simp only [Nat.cast_add,Nat.cast_one]
        linear_combination
          betaEndpoint (K:=ZMod p) p n*he+
          ((n : ZMod p)-(p/6 : ℕ))*((n : ZMod p)+(p/6 : ℕ)+1)*
            (WPReview.nativeCoefficient n : ZMod p)*hb+
          ((n : ZMod p)-(p/6 : ℕ))*((n : ZMod p)+(p/6 : ℕ)+1)*hi-ha
  exact hall n hn hd

end WPFieldAssembly.ActualGaussHarmonic
