import WPFieldAssembly.ActualUVSourceIdentification

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
  WPFieldAssembly.ActualUVSourceIdentification

namespace WPFieldAssembly.SourceClosureUVDescent

/- Every coefficient of the specified U has an expression in the squared
   finite alphabet. These identities retain both roots and do not require
   that 1/5 be a square in the prime field. -/

variable {K : Type*} [Field K]

noncomputable def descendedC (p : ℕ) : K :=
  (WPFiniteWSource.deltaE p).eval (1/5)

noncomputable def descendedZE (p : ℕ) : K :=
  (WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4+
    4*WPFiniteABSourceTail.epsilon p*descendedC p/15

noncomputable def descendedUcan (p : ℕ) : K[T;T⁻¹] :=
  originalK0 p*originalHsym p-
    LaurentPolynomial.C (descendedZE p)*(originalJa p+originalJb p)-
    LaurentPolynomial.C (1/2 : K)*WPFieldAssembly.SourceClosureUniversalLog.originalJ2log p

noncomputable def descendedU0 (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  (5/3 : K)*
    (WPFiniteLoop.D ((p-1)/2) (4/5) 1+WPFiniteLoop.D ((p-1)/2) (4/5) 4-
      WPFiniteLoop.D ((p-1)/2) (1/5) (1/4)-WPFiniteLoop.D ((p-1)/2) (1/5) 1-
      WPFiniteLoop.D ((p-1)/2) (4/5) (4/5)+WPFiniteLoop.D ((p-1)/2) (1/5) (1/5)+
      (WPFiniteLoop.D ((p-1)/2) (4/5) 0-WPFiniteLoop.D ((p-1)/2) (1/5) 0)/2)-
    (2*WPFiniteNC122.q p/3+
      (WPFiniteInversion.integerFermatQuotient p 3 : K)/2)*WPFiniteField.ell p (-4)+
      WPFiniteField.R p (-4)/6

noncomputable def descendedU (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  descendedUcan p-LaurentPolynomial.C (descendedU0 p)

theorem originalC_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    WPFifthEntropy.C p u=descendedC p :=
  (WPFiniteWSource.deltaE_fifth p hp u hu).symm

theorem originalZE_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originalZE p u=descendedZE p := by
  rw [originalZE,originalC_descended p hp u hu]
  rfl

theorem originalUcan_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originalUcan p u=descendedUcan p := by
  rw [originalUcan,originalZE_descended p hp u hu]
  rfl

/-- The entire u0 descends, including its dilogarithm branch correction. -/
theorem originalU0_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originalU0 p u=descendedU0 p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2u : (2*u)^2=4/5 := by
    calc
      (2*u)^2=4*u^2 := by ring
      _=4/5 := by rw [hu]; ring
  have hhalf : (1/2 : K)^2=1/4 := by
    field_simp [h2,h4]
    ring
  simp only [originalU0,descendedU0,WPFiniteLoop.S,h2u,hu,
    one_pow,zero_pow (by decide : (2 : ℕ)≠0),hhalf,
    show (2 : K)^2=4 by ring]

theorem originalU_descended (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) : originalU p u=descendedU p := by
  rw [originalU,originalUcan_descended p hp u hu,originalU0_descended p hp u hu]
  rfl

/-- Both square-root branches specify exactly the same whole Laurent U. -/
theorem originalU_branch_independent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u v : K) (hu : u^2=1/5) (hv : v^2=1/5) :
    originalU p u=originalU p v := by
  rw [originalU_descended p hp u hu,originalU_descended p hp v hv]

end WPFieldAssembly.SourceClosureUVDescent
