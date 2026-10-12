import WPReview.Literal
import WPReview.FiniteStokes
import WPGammaArithmetic

namespace WPReview

theorem gamma_helper_eq (k : ℕ) : gamma k = WPGammaArithmetic.gamma k := rfl

theorem Gamma_helper_eq (L : ℕ) (f : ℕ → ℚ) :
    Gamma L f = WPGammaArithmetic.gammaMoment L f := rfl

theorem congruence_helper_iff (p m : ℕ) (a b : ℚ) :
    RationalCongruent p m a b ↔ WPGammaArithmetic.RationalCongruent p m a b := Iff.rfl

theorem gamma_valuation_formula (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) :
    padicValRat p (gamma k) =
      2 * (k / p : ℕ) - (((2 * k + 1) / p : ℕ) : ℤ) :=
  WPGammaArithmetic.gamma_valuation_formula p k hp hp7 hk

theorem gamma_valuation_values (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) :
    padicValRat p (gamma k) = 0 ∨ padicValRat p (gamma k) = -1 :=
  WPGammaArithmetic.gamma_valuation_values p k hp hp7 hk

theorem Gamma_precision_loss (p L m : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f g : ℕ → ℚ)
    (hfg : ∀ k ≤ L, RationalCongruent p (m + 1) (f k) (g k)) :
    RationalCongruent p m (Gamma L f) (Gamma L g) :=
  WPGammaArithmetic.gammaMoment_precision_loss p L m hp hp7 hL f g hfg

theorem Gamma_p6_to_p5 (p L : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f g : ℕ → ℚ)
    (hfg : ∀ k ≤ L, RationalCongruent p 6 (f k) (g k)) :
    RationalCongruent p 5 (Gamma L f) (Gamma L g) :=
  WPGammaArithmetic.gammaMoment_p6_to_p5 p L hp hp7 hL f g hfg

theorem p_mul_Gamma_integral (p L : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f : ℕ → ℚ)
    (hf : ∀ k ≤ L, RationalCongruent p 0 (f k) 0) :
    RationalCongruent p 0 ((p : ℚ) * Gamma L f) 0 :=
  WPGammaArithmetic.p_mul_gammaMoment_integral p L hp hp7 hL f hf

end WPReview
