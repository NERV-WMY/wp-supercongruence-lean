import Mathlib.Tactic

open scoped BigOperators

namespace WPFiniteConductorReflection

def reciprocalCoordinate (r : ℚ) : ℚ := 1 / (4 * r)

def q1 (r : ℚ) : ℚ :=
  (16 * r ^ 2 - 1) * (1 - r ^ 2) ^ 2 / (500 * r ^ 6)

def q2 (r : ℚ) : ℚ :=
  (4 / 125) * (16 * r ^ 2 - 1) ^ 2 * (1 - r ^ 2)

def firstWeight (r : ℚ) : ℚ :=
  -(16 * r ^ 2 - 11) / (3 * (1 - r ^ 2) * (16 * r ^ 2 - 1))

def secondWeight (r : ℚ) : ℚ :=
  4 * (11 * r ^ 2 - 1) / (3 * (1 - r ^ 2) * (16 * r ^ 2 - 1))

def firstFlux (p n : ℕ) (r : ℚ) : ℚ :=
  firstWeight r * q2 r ^ p * q1 r ^ n

def secondFlux (p n : ℕ) (r : ℚ) : ℚ :=
  secondWeight r * q1 r ^ p * q2 r ^ n

theorem q1_reciprocal (r : ℚ) (hr : r ≠ 0) :
    q1 (reciprocalCoordinate r) = q2 r := by
  unfold q1 q2 reciprocalCoordinate
  field_simp [hr]; ring

theorem q2_reciprocal (r : ℚ) (hr : r ≠ 0) :
    q2 (reciprocalCoordinate r) = q1 r := by
  unfold q1 q2 reciprocalCoordinate
  field_simp [hr]; ring

/-- The actual source weights transform with the full reciprocal derivative and sign. -/
theorem firstWeight_reciprocal (r : ℚ) (hr : r ≠ 0)
    (h1 : 1 - r ^ 2 ≠ 0) (h16 : 16 * r ^ 2 - 1 ≠ 0) :
    firstWeight (reciprocalCoordinate r) * (-1 / (4 * r ^ 2)) =
      -secondWeight r := by
  have hrec1 : 1 - (reciprocalCoordinate r) ^ 2 ≠ 0 := by
    have hrepr : 1 - (reciprocalCoordinate r) ^ 2 =
        (16 * r ^ 2 - 1) / (16 * r ^ 2) := by
      unfold reciprocalCoordinate
      field_simp [hr]; ring
    rw [hrepr]
    exact div_ne_zero h16 (by exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
  have hrec16 : 16 * (reciprocalCoordinate r) ^ 2 - 1 ≠ 0 := by
    have hrepr : 16 * (reciprocalCoordinate r) ^ 2 - 1 =
        (1 - r ^ 2) / r ^ 2 := by
      unfold reciprocalCoordinate
      field_simp [hr]; ring
    rw [hrepr]
    exact div_ne_zero h1 (pow_ne_zero 2 hr)
  unfold firstWeight secondWeight
  field_simp [hr, h1, h16, hrec1, hrec16]
  unfold reciprocalCoordinate
  field_simp [hr]; ring

/-- The two actual conductor monomial fluxes, for arbitrary finite p and n. -/
theorem actual_two_flux_reciprocal (p n : ℕ) (r : ℚ) (hr : r ≠ 0)
    (h1 : 1 - r ^ 2 ≠ 0) (h16 : 16 * r ^ 2 - 1 ≠ 0) :
    firstFlux p n (reciprocalCoordinate r) * (-1 / (4 * r ^ 2)) =
      -secondFlux p n r := by
  unfold firstFlux secondFlux
  rw [q1_reciprocal r hr, q2_reciprocal r hr]
  calc
    firstWeight (reciprocalCoordinate r) * q1 r ^ p * q2 r ^ n *
        (-1 / (4 * r ^ 2)) =
      (firstWeight (reciprocalCoordinate r) * (-1 / (4 * r ^ 2))) *
        q1 r ^ p * q2 r ^ n := by ring
    _ = _ := by rw [firstWeight_reciprocal r hr h1 h16]; ring

/-- The exact antiderivative value of r^(ell-1), excluding a logarithmic slot. -/
def monomialEndpoint (ell : ℤ) (a b : ℚ) : ℚ :=
  (b ^ ell - a ^ ell) / (ell : ℚ)

theorem monomialEndpoint_join (ell : ℤ) (a b c : ℚ) :
    monomialEndpoint ell a b + monomialEndpoint ell b c =
      monomialEndpoint ell a c := by
  unfold monomialEndpoint
  ring

theorem reciprocal_two_zpow (ell : ℤ) :
    (1 / 2 : ℚ) ^ ell = (2 : ℚ) ^ (-ell) := by
  simp only [one_div, zpow_neg, inv_zpow]

theorem reciprocal_four_zpow (ell : ℤ) :
    (1 / 4 : ℚ) ^ ell = (4 : ℚ) ^ (-ell) := by
  simp only [one_div, zpow_neg, inv_zpow]

theorem reciprocal_weight_product (ell : ℤ) :
    (4 : ℚ) ^ (-ell) * (2 : ℚ) ^ ell = (2 : ℚ) ^ (-ell) := by
  rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_zpow, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp

/-- The reciprocal second flux on [1/2,1] is the first on [1/4,1/2]. -/
theorem reflected_monomial_endpoint (ell : ℤ) (hell : ell ≠ 0) :
    (4 : ℚ) ^ (-ell) * monomialEndpoint (-ell) (1 / 2) 1 =
      monomialEndpoint ell (1 / 4) (1 / 2) := by
  have hq : (ell : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hell
  have hmix := reciprocal_weight_product ell
  unfold monomialEndpoint
  rw [one_zpow, reciprocal_two_zpow (-ell), neg_neg,
    reciprocal_two_zpow ell, reciprocal_four_zpow ell]
  push_cast
  field_simp [hq]
  linear_combination hmix

/-- Both full finite Laurent fluxes combine, retaining the true lower and upper endpoints. -/
theorem finite_two_flux_endpoints (s : Finset ℤ) (a : ℤ → ℚ)
    (hs : ∀ ell ∈ s, ell ≠ 0) :
    (∑ ell ∈ s, a ell * monomialEndpoint ell (1 / 2) 1) +
      (∑ ell ∈ s, a ell * (4 : ℚ) ^ (-ell) *
        monomialEndpoint (-ell) (1 / 2) 1) =
      ∑ ell ∈ s, a ell * monomialEndpoint ell (1 / 4) 1 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [mul_assoc, reflected_monomial_endpoint ell (hs ell hell), ← mul_add,
    add_comm (monomialEndpoint ell (1 / 2) 1)
      (monomialEndpoint ell (1 / 4) (1 / 2)), monomialEndpoint_join]

end WPFiniteConductorReflection
