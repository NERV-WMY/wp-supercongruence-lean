import WPActualPartialHarmonic
import WPFiniteFieldLog

open scoped BigOperators QuadraticAlgebra
open WPActualHarmonicCubicTrace WPActualHarmonicCubeFilter

namespace WPFieldAssembly.ActualCubicUnitRoot

set_option maxHeartbeats 1400000

/-- The original entire integer divided-binomial row, before any field map. -/
def cubicSignedRow (p : ℕ) : CubicIntegers :=
  ∑ j ∈ Finset.Ico 1 p,
    (((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : CubicIntegers)*(-cubicOmega)^j

theorem cubic_unit_trace_vector (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    3*(1-cubicOmega)^p=
      (cubicTrace ((1-cubicOmega)^p) : CubicIntegers)*(1-cubicOmega^p) := by
  let N := (p-1)/2
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have he : (1-cubicOmega)^p=((-3 : CubicIntegers)^N)*
      (cubicOmega^N*(1-cubicOmega)) := by
    rw [show p=2*N+1 by dsimp [N]; omega, pow_succ, pow_mul,
      cubicOmega_minus_square, mul_pow]
    ring
  have hcast : (-3 : CubicIntegers)^N=((-3 : ℤ)^N : ℤ) := by
    push_cast
    rfl
  have hm : N%3=0 ∨ N%3=2 := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h | h <;>
      dsimp [N] <;> omega
  rw [he, hcast, cubicTrace_integer_mul, cubicOmega_power_mod N]
  rcases hm with h | h
  · have hp3 : p%3=1 := by dsimp [N] at h; omega
    rw [h, cubicOmega_power_mod p, hp3]
    ext <;> simp only [cubicTrace, QuadraticAlgebra.trace_def,
      cubicOmega, QuadraticAlgebra.omega, pow_zero, pow_succ,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> push_cast <;> ring
  · have hp3 : p%3=2 := by dsimp [N] at h; omega
    rw [h, cubicOmega_power_mod p, hp3]
    ext <;> simp only [cubicTrace, QuadraticAlgebra.trace_def,
      cubicOmega, QuadraticAlgebra.omega, pow_zero, pow_succ,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> push_cast <;> ring

theorem cubic_unit_principal_vector (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1-cubicOmega)^p=(1-cubicOmega^p)*
      ((1+(p : ℤ)*cubicQuotientSum p (-1) : ℤ) : CubicIntegers) := by
  have ht := cubicQuotientSum_minus_source p (by omega)
  have he := cubic_unit_trace_vector p hp
  have htrace : cubicTrace ((1-cubicOmega)^p)=
      3+3*(p : ℤ)*cubicQuotientSum p (-1) := by linear_combination ht
  rw [htrace] at he
  have hscalar : ((3+3*(p : ℤ)*cubicQuotientSum p (-1) : ℤ) : CubicIntegers)=
      3*((1+(p : ℤ)*cubicQuotientSum p (-1) : ℤ) : CubicIntegers) := by
    push_cast
    ring
  rw [hscalar] at he
  ext
  · have hr := congrArg QuadraticAlgebra.re he
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] at hr ⊢
    nlinarith [hr]
  · have hi := congrArg QuadraticAlgebra.im he
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] at hi ⊢
    nlinarith [hi]

theorem cubicSignedRow_binomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1-cubicOmega)^p=1-cubicOmega^p+(p : CubicIntegers)*cubicSignedRow p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [show 1-cubicOmega=-cubicOmega+1 by ring, add_pow,
    Finset.sum_range_succ, ←Finset.sum_range_add_sum_Ico _
      (Fact.out : p.Prime).one_le]
  simp only [Finset.sum_range_one, pow_zero, one_pow, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, mul_one]
  rw [hodd.neg_pow]
  unfold cubicSignedRow
  rw [Finset.mul_sum]
  have hs : (∑ j ∈ Finset.Ico 1 p,
      (-cubicOmega)^j*(Nat.choose p j : CubicIntegers))=
      ∑ j ∈ Finset.Ico 1 p,
        (p : CubicIntegers)*
          ((((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : CubicIntegers)*(-cubicOmega)^j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
      exact_mod_cast (Fact.out : p.Prime).dvd_choose_self
        (by have := (Finset.mem_Ico.mp hj).1; omega) (Finset.mem_Ico.mp hj).2
    have hc := congrArg (fun n : ℤ => (n : CubicIntegers)) (Int.mul_ediv_cancel' hd)
    push_cast at hc
    linear_combination -((-cubicOmega)^j)*hc
  rw [hs]
  ring

theorem cubicSignedRow_principal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    cubicSignedRow p=(1-cubicOmega^p)*(cubicQuotientSum p (-1) : CubicIntegers) := by
  have he := cubicSignedRow_binomial p hp
  rw [cubic_unit_principal_vector p hp] at he
  have hc : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h : (p : CubicIntegers)*cubicSignedRow p=
      (p : CubicIntegers)*((1-cubicOmega^p)*(cubicQuotientSum p (-1) : CubicIntegers)) := by
    push_cast at he
    linear_combination -he
  ext
  · apply mul_left_cancel₀ hc
    have hr := congrArg QuadraticAlgebra.re h
    simpa only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_natCast,
      QuadraticAlgebra.im_natCast, mul_zero, zero_mul, add_zero] using hr
  · apply mul_left_cancel₀ hc
    have hi := congrArg QuadraticAlgebra.im h
    simpa only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast,
      QuadraticAlgebra.im_natCast, mul_zero, zero_mul, add_zero, zero_add] using hi

variable {K : Type*} [Field K]

noncomputable def cubicRootHom (u : K) (hu : u^2+u+1=0) : CubicIntegers →ₐ[ℤ] K :=
  QuadraticAlgebra.lift ⟨u, by
    simp only [neg_one_smul]
    change u*u=(-1)+(-u)
    linear_combination hu⟩

theorem cubicRootHom_omega (u : K) (hu : u^2+u+1=0) :
    cubicRootHom u hu cubicOmega=u := by
  simp [cubicRootHom, cubicOmega, QuadraticAlgebra.lift, QuadraticAlgebra.omega]

theorem cubicSignedRow_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (hu : u^2+u+1=0) :
    cubicRootHom u hu (cubicSignedRow p)=-WPFiniteField.ell p u := by
  rw [cubicSignedRow, map_sum, WPFiniteField.ell, ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.divided_choose_cast p j hj)
  simp only [map_intCast, map_div₀, map_pow, map_neg, map_one, map_natCast] at hc
  rw [map_mul, map_intCast, map_pow, map_neg, cubicRootHom_omega, hc, neg_pow]
  have hs := negative_sign_pair (K := K) j (Finset.mem_Ico.mp hj).1
  simp only [div_eq_mul_inv]
  linear_combination (j : K)⁻¹*u^j*hs

/-- The primitive-root finite logarithm is forced by the original integer unit. -/
theorem actual_cubic_root_log (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2+u+1=0) :
    WPFiniteField.ell p u=-(1-u^p)*
      (WPFiniteInversion.integerFermatQuotient p 3 : K)/2 := by
  have he := congrArg (cubicRootHom u hu) (cubicSignedRow_principal p hp)
  rw [cubicSignedRow_field, map_mul, map_sub, map_one, map_pow,
    cubicRootHom_omega, map_intCast] at he
  have hS := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPActualPartialHarmonic.cubicQuotientSum_minus_fermat p (by omega))
  simp only [map_intCast, map_mul, map_ofNat] at hS
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2]
  linear_combination -2*he+(1-u^p)*hS

end WPFieldAssembly.ActualCubicUnitRoot
