import WPMarkedBridge.Literal

namespace WPMarkedBridge

noncomputable section

open WPCompletedCartier.ActualNormalization
open WPResidueQuotient.Adic

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

/-- The hypothesis is membership in the actual scalar-image submodule p^8 Zp^5. -/
theorem actual_marked_literal_of_powerSubmodule
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp ∈
        powerSubmodule (M := Fin 5 → ℤ_[p]) (p : ℤ_[p]) 8) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  obtain ⟨e, he⟩ := (mem_powerSubmodule (p : ℤ_[p]) 8 _).mp hres
  exact actual_marked_literal_congruence p hp hp7 hp19 e he.symm

theorem actual_marked_cleared_of_powerSubmodule
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp ∈
        powerSubmodule (M := Fin 5 → ℤ_[p]) (p : ℤ_[p]) 8) :
    (p : ℤ)^5 ∣ WPReview.clearedDifference p :=
  (WPReview.literal_congruence_iff p (Fact.out : p.Prime) hp).mp
    (actual_marked_literal_of_powerSubmodule p hp hp7 hp19 hres)

end
end WPMarkedBridge
