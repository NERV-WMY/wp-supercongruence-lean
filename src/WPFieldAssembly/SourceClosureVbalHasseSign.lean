import WPFieldAssembly.SourceClosureVbalIR61FourEnds
import WPFiniteJWeightedResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteWSource
  WPFieldAssembly.SourceClosureVbalIR61FourEnds

namespace WPFieldAssembly.SourceClosureVbalHasseSign

set_option maxHeartbeats 1600000

/-- The original Hasse sign is a unit in both retained prime classes. -/
theorem actual_cross_hasse_sign_square (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    actualCrossHasseSign p^2=1 := by
  have hsg : ((-1 : ZMod p)^(p/6))^2=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have htwo : ((2 : ZMod p)^((p-1)/2))^2=1 := by
    calc
      _ = (4 : ZMod p)^((p-1)/2) := by
        rw [←pow_mul,Nat.mul_comm,pow_mul]
        norm_num
      _ = _ := four_half_power p hp
  rw [actualCrossHasseSign,mul_pow,hsg,htwo,one_mul]

/-- The actual unit endpoint selects this sign after cancellation of the common conic coordinate. -/
theorem actual_cross_hasse_unit_scale (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (M : ℕ) (hM : 2*M+(p/6)%2=(p-1)/2) :
    actualCrossHasseSign p*(4 : ZMod p)^M*(-2)^((p/6)%2)=1 := by
  let r := (p/6)%2
  have heven : Even (p/6+r) := by
    refine ⟨(p/6)/2+r,?_⟩
    have hdiv := Nat.mod_add_div (p/6) 2
    dsimp only [r]
    omega
  have h4 : (4 : ZMod p)^M=(2 : ZMod p)^(2*M) := by
    rw [show (4 : ZMod p)=2^2 by ring,←pow_mul]
  have hhalf : (2 : ZMod p)^(2*((p-1)/2))=1 := by
    calc
      _ = (4 : ZMod p)^((p-1)/2) := by
        rw [pow_mul]
        norm_num
      _ = _ := four_half_power p hp
  change actualCrossHasseSign p*(4 : ZMod p)^M*(-2)^r=1
  calc
    _ = (-1 : ZMod p)^(p/6+r)*(2 : ZMod p)^((p-1)/2+2*M+r) := by
      rw [actualCrossHasseSign,h4,show (-2 : ZMod p)=(-1)*2 by ring,
        mul_pow,pow_add,pow_add,pow_add]
      ring
    _ = (-1 : ZMod p)^(p/6+r)*(2 : ZMod p)^(2*((p-1)/2)) := by
      congr 2
      dsimp only [r]
      omega
    _ = _ := by rw [heven.neg_one_pow,hhalf,one_mul]

/-- A full square equality and the same unit endpoint select the whole polynomial sign. -/
theorem whole_square_sign_selected {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] (h2 : (2 : K)≠0) (ψ : R→+*K) (P Q : R)
    (hsquare : P^2=Q^2) (hP : ψ P=1) (hQ : ψ Q=1) : P=Q := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hopposite
  · exact hsame
  · have he := congrArg ψ hopposite
    rw [map_neg,hP,hQ] at he
    have hz : (2 : K)=0 := by linear_combination he
    exact (h2 hz).elim

end WPFieldAssembly.SourceClosureVbalHasseSign
