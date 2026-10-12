import Verification.Challenge
import WPReview.AllPrime

namespace WPSupercongruenceStatement

theorem W_eq_literalSum (p : Nat) : W p = WPReview.literalSum p := by
  unfold W WPReview.literalSum
  apply Finset.sum_congr rfl
  intro n _
  unfold WPReview.literalTerm WPReview.weightNat
  push_cast
  rfl

theorem congruent_eq (p : Nat) (a b : Rat) :
    Congruent p a b = WPReview.RationalCongruent p 5 a b := rfl

theorem checkedChallenge : Challenge := by
  intro p hprime hp
  rw [congruent_eq, W_eq_literalSum]
  exact WPReview.literal_all_primes p hprime hp

end WPSupercongruenceStatement
