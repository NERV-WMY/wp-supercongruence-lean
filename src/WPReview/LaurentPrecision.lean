import WPReview.Literal
import WPLaurent

namespace WPReview

def fermatQuotientFour (p : ℕ) : ℚ := ((4 : ℚ)^(p-1)-1)/(p : ℚ)

theorem fermat_quotient_four_eq_helper (p : ℕ) :
    fermatQuotientFour p = WPLaurent.fermatQuotient4 p := rfl

theorem laurent_congruence_helper_iff (p m : ℕ) (a b : ℚ) :
    RationalCongruent p m a b ↔ WPLaurent.RationalCongruent p m a b := Iff.rfl

theorem fermat_quotient_four_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    0 ≤ padicValRat p (fermatQuotientFour p) :=
  WPLaurent.fermatQuotient4_integral p hp hp7

theorem resonant_laurent_kernel (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : ℤ) (hb : b = -5 ∨ b = -3 ∨ b = -1 ∨ b = 1 ∨ b = 3 ∨ b = 5) :
    RationalCongruent p 3
      ((p : ℚ)*(1-(4 : ℚ)^(-(b*(p : ℤ))))/((b*(p : ℤ) : ℤ) : ℚ))
      ((1-(4 : ℚ)^(-b))/(b : ℚ)+(p : ℚ)*(4 : ℚ)^(-b)*fermatQuotientFour p -
        ((p : ℚ)^2/2)*((b : ℚ)+1)*(4 : ℚ)^(-b)*fermatQuotientFour p^2) :=
  WPLaurent.literal_resonant_kernel_expanded p hp hp7 b hb

theorem nonresonant_laurent_kernel (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ell b r : ℤ) (hsplit : ell=b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ))
    (hodd : Odd ell) (hlo : -6*((5*p/6 : ℕ) : ℤ)-1 ≤ ell)
    (hhi : ell ≤ 6*(p : ℤ)-1) :
    RationalCongruent p 3
      ((p : ℚ)*(1-(4 : ℚ)^(-ell))/(ell : ℚ))
      ((p : ℚ)*(1-(4 : ℚ)^(-b-r))/(ell : ℚ)+
        (p : ℚ)^2*(b : ℚ)*(4 : ℚ)^(-b-r)*fermatQuotientFour p/(ell : ℚ)) :=
  WPLaurent.literal_nonresonant_kernel_expanded p hp hp7 ell b r
    hsplit hr1 hrp hodd hlo hhi

theorem nonresonant_laurent_denominator_unit (p : ℕ) (ell b r : ℤ)
    (hsplit : ell=b*(p : ℤ)+r) (hr1 : 1 ≤ r) (hrp : r < (p : ℤ)) :
    padicValRat p (ell : ℚ) = 0 :=
  WPLaurent.nonresonant_denominator_unit p ell b r hsplit hr1 hrp

end WPReview
