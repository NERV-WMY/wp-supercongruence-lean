import WPFiniteLoop

namespace WPActualFinalConsumer

open WPFiniteField

variable {K : Type*} [Field K]

theorem actual_corrected_consumer (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    77 * (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u) / 75 +
      22 * (Ke p (2 * u) - Ke p u) / 5 -
      2233 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 / 125 +
      1386 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
        (WPFiniteInversion.integerFermatQuotient p 3 : K) / 125 +
      154 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 25 -
      231 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 50 +
      4334 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * WPFifthEntropy.C p u / 375 -
      616 * (WPFiniteInversion.integerFermatQuotient p 3 : K) * WPFifthEntropy.C p u / 125 -
      88 * (WPFifthEntropy.C p u) ^ 2 / 25 - 22 * R p (-2 : K) / 15 -
      11 * R p (16 : K) / 150 = 0 := by
  let q : ZMod p := WPFiniteInversion.integerFermatQuotient p 2
  let r : ZMod p := WPFiniteInversion.integerFermatQuotient p 3
  let k : ZMod p := WPFiniteInversion.integerFermatQuotient p 5
  let c : ZMod p := ((WPFifthEntropy.B p 2 - WPFifthEntropy.B p 1 : ℤ) : ZMod p) / 5
  have he := WPFinalEndpointAlgebra.corrected_final_consumer p hp q r k c
    (WPFiniteInversion.R p (-2)) (WPFiniteInversion.R p 16)
    (-6 * q * k + 9 * r * k / 2 + 72 * q ^ 2 / 5 -
      54 * q * r / 5 - 52 * q * c / 5 + 24 * r * c / 5)
    (7 * q ^ 2 / 10 - q * c / 5 + 4 * c ^ 2 / 5 +
      WPFiniteInversion.R p (-2) / 3 + WPFiniteInversion.R p 16 / 60) rfl rfl
  have hm := congrArg (ZMod.castHom (dvd_refl p) K) he
  dsimp only [q, r, k, c] at hm
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_intCast,
    map_ofNat, map_zero, ← R_castHom, ← WPKFifthEndpoint.C_castHom p hp u hu] at hm
  rw [WPFiniteLoop.loop_at_fifth p hp u hu, WPKFifthEndpoint.Ke_difference p hp u hu]
  exact hm

end WPActualFinalConsumer
