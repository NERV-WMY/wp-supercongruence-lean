import WPCartierFinite.Selector
import WPCartierFinite.Vectors
import WPCartierFinite.ScalarAlgebra
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

namespace WPCartierFinite

noncomputable section

abbrev OrdinaryPolynomial := MvPolynomial (Fin 6) ℚ
abbrev IntegerPolynomial := MvPolynomial (Fin 6) ℤ

/-- The literal six-variable representative of the Laurent polynomial. -/
def ordinaryF : OrdinaryPolynomial :=
  1 - MvPolynomial.C (1 / 10 : ℚ) * ∑ i : Fin 6, MvPolynomial.X i

/-- Exponent multiplication on the actual ordinary polynomial ring. -/
def ordinaryPhi (p : ℕ) : OrdinaryPolynomial →+* OrdinaryPolynomial :=
  (MvPolynomial.expand p).toRingHom

/-- The literal divided Frobenius error, before the diagonal quotient. -/
def ordinaryG (p : ℕ) : OrdinaryPolynomial :=
  MvPolynomial.C (1 / (p : ℚ)) * (ordinaryPhi p ordinaryF - ordinaryF ^ p)

/-- Clearing only the unit denominator ten gives this integer polynomial. -/
def integralF : IntegerPolynomial :=
  10 - ∑ i : Fin 6, MvPolynomial.X i

/-- The numerator after clearing the denominator `10^p`. -/
def integralError (p : ℕ) : IntegerPolynomial :=
  MvPolynomial.C ((10 : ℤ) ^ (p - 1)) * MvPolynomial.expand p integralF - integralF ^ p

theorem ordinaryF_degree : ordinaryF.totalDegree ≤ 1 := by
  have hs : (∑ i : Fin 6, (MvPolynomial.X i : OrdinaryPolynomial)).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    exact Finset.sup_le fun _ _ => by simp
  unfold ordinaryF
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hs)

theorem ordinaryPhi_F (p : ℕ) :
    ordinaryPhi p ordinaryF =
      1 - MvPolynomial.C (1 / 10 : ℚ) * ∑ i : Fin 6, MvPolynomial.X i ^ p := by
  simp [ordinaryPhi, ordinaryF, map_sum]

theorem ordinaryPhi_F_degree (p : ℕ) : (ordinaryPhi p ordinaryF).totalDegree ≤ p := by
  rw [ordinaryPhi_F]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    exact Finset.sup_le fun _ _ => by simp

theorem ordinaryG_degree (p : ℕ) : (ordinaryG p).totalDegree ≤ p := by
  unfold ordinaryG
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (ordinaryPhi_F_degree p)
  exact (MvPolynomial.totalDegree_pow ordinaryF p).trans
    (by simpa using Nat.mul_le_mul_left p ordinaryF_degree)

set_option maxHeartbeats 1000000 in
theorem integralError_mod (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (integralError p).map (Int.castRingHom (ZMod p)) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have ht : (10 : ZMod p) ≠ 0 := by
    intro hzero
    exact WPReview.prime_not_dvd_ten p hp hp7
      ((ZMod.natCast_eq_zero_iff 10 p).mp hzero)
  have hfermat : (10 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one ht
  have hfrob :
      ((integralF.map (Int.castRingHom (ZMod p))).expand p) =
        (integralF.map (Int.castRingHom (ZMod p))) ^ p := by
    simpa only [ZMod.frobenius_zmod, MvPolynomial.map_id] using
      (MvPolynomial.map_frobenius_expand (σ := Fin 6) (R := ZMod p) p
        (f := integralF.map (Int.castRingHom (ZMod p))))
  unfold integralError
  rw [map_sub, map_mul, MvPolynomial.map_C,
    (MvPolynomial.map (Int.castRingHom (ZMod p))).map_pow, MvPolynomial.map_expand]
  simp only [Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
  rw [hfermat, MvPolynomial.C_1, one_mul, hfrob, sub_self]

/-- The actual integer numerator coefficients, rather than an assumed
integral lift, are divisible by `p`. -/
theorem integralError_coefficient_dvd (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : Fin 6 →₀ ℕ) : (p : ℤ) ∣ MvPolynomial.coeff b (integralError p) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have h := congrArg (MvPolynomial.coeff b) (integralError_mod p hp hp7)
  simpa only [MvPolynomial.coeff_map, Int.coe_castRingHom,
    MvPolynomial.coeff_zero] using h

theorem integralF_map :
    integralF.map (Int.castRingHom ℚ) = MvPolynomial.C (10 : ℚ) * ordinaryF := by
  rw [ordinaryF, mul_sub, mul_one, ← mul_assoc, ← MvPolynomial.C_mul]
  norm_num
  simp only [integralF, map_sub, map_ofNat, map_sum, MvPolynomial.map_X]

theorem integralError_map (p : ℕ) (hp : 0 < p) :
    (integralError p).map (Int.castRingHom ℚ) =
      MvPolynomial.C ((10 : ℚ) ^ p) *
        (ordinaryPhi p ordinaryF - ordinaryF ^ p) := by
  have hexp : p - 1 + 1 = p := by omega
  have hten : (10 : ℚ) ^ (p - 1) * 10 = 10 ^ p := by
    rw [← pow_succ, hexp]
  unfold integralError
  rw [map_sub, map_mul, MvPolynomial.map_C,
    (MvPolynomial.map (Int.castRingHom ℚ)).map_pow, MvPolynomial.map_expand,
    integralF_map, map_mul, MvPolynomial.expand_C, mul_pow]
  simp only [Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
  change MvPolynomial.C ((10 : ℚ) ^ (p - 1)) *
      (MvPolynomial.C 10 * MvPolynomial.expand p ordinaryF) -
      MvPolynomial.C 10 ^ p * ordinaryF ^ p = _
  rw [← mul_assoc, ← MvPolynomial.C_mul, hten, ← MvPolynomial.C_pow]
  change _ = MvPolynomial.C ((10 : ℚ) ^ p) *
    (MvPolynomial.expand p ordinaryF - ordinaryF ^ p)
  ring

/-- Every literal coefficient is an integer divided by the explicit
denominator unit `10^p`. -/
theorem ordinaryG_coefficient_fraction (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : Fin 6 →₀ ℕ) :
    ∃ z : ℤ, MvPolynomial.coeff b (ordinaryG p) = (z : ℚ) / (10 : ℚ) ^ p := by
  obtain ⟨z, hz⟩ := integralError_coefficient_dvd p hp hp7 b
  have h := congrArg (MvPolynomial.coeff b) (integralError_map p hp.pos)
  simp only [MvPolynomial.coeff_map, Int.coe_castRingHom,
    MvPolynomial.coeff_C_mul] at h
  have hcoef : ((MvPolynomial.coeff b (integralError p) : ℤ) : ℚ) = (p : ℚ) * z := by
    exact_mod_cast hz
  rw [hcoef] at h
  refine ⟨z, ?_⟩
  simp only [ordinaryG, MvPolynomial.coeff_C_mul]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htq : (10 : ℚ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : MvPolynomial.coeff b (ordinaryPhi p ordinaryF - ordinaryF ^ p) =
      (p : ℚ) * z / (10 : ℚ) ^ p := by
    apply (eq_div_iff htq).mpr
    simpa only [mul_comm] using h.symm
  rw [hc]
  field_simp

theorem ordinaryF_coefficient_fraction (b : Fin 6 →₀ ℕ) :
    ∃ z : ℤ, MvPolynomial.coeff b ordinaryF = (z : ℚ) / 10 := by
  refine ⟨MvPolynomial.coeff b integralF, ?_⟩
  have h := congrArg (MvPolynomial.coeff b) integralF_map
  simp only [MvPolynomial.coeff_map, Int.coe_castRingHom, MvPolynomial.coeff_C_mul] at h
  apply (eq_div_iff (by norm_num : (10 : ℚ) ≠ 0)).mpr
  simpa only [mul_comm] using h.symm

theorem ordinaryF_coefficient_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : Fin 6 →₀ ℕ) : pIntegral p (MvPolynomial.coeff b ordinaryF) := by
  obtain ⟨z, hz⟩ := ordinaryF_coefficient_fraction b
  rw [hz]
  exact pIntegral_of_fraction p z 10 (WPReview.prime_not_dvd_ten p hp hp7)

theorem ordinaryG_coefficient_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (b : Fin 6 →₀ ℕ) : pIntegral p (MvPolynomial.coeff b (ordinaryG p)) := by
  obtain ⟨z, hz⟩ := ordinaryG_coefficient_fraction p hp hp7 b
  rw [hz]
  have hi := pIntegral_of_fraction p z (10 ^ p)
    (fun h => WPReview.prime_not_dvd_ten p hp hp7 (hp.dvd_of_dvd_pow h))
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hi

def ordinaryWeight (b : Fin 6 →₀ ℕ) : ℕ := b.sum fun _ n => n

/-- All ordinary coefficients of the literal power, with the vanishing
upper tail encoded by the binomial coefficient. -/
theorem ordinaryF_pow_coefficient (N : ℕ) (b : Fin 6 →₀ ℕ) :
    MvPolynomial.coeff b (ordinaryF ^ N) =
      (N.choose (ordinaryWeight b) : ℚ) * b.multinomial *
        (-1 / 10 : ℚ) ^ ordinaryWeight b := by
  classical
  have hf : ordinaryF =
      MvPolynomial.C (-1 / 10 : ℚ) * (∑ i : Fin 6, MvPolynomial.X i) + 1 := by
    simp only [ordinaryF, neg_div, map_neg]
    ring
  rw [hf, add_pow, MvPolynomial.coeff_sum]
  simp only [one_pow, mul_one]
  have hterm (m : ℕ) :
      MvPolynomial.coeff b
        ((MvPolynomial.C (-1 / 10 : ℚ) * ∑ i : Fin 6, MvPolynomial.X i) ^ m *
          (N.choose m : OrdinaryPolynomial)) =
        (N.choose m : ℚ) * (-1 / 10 : ℚ) ^ m *
          (if ordinaryWeight b = m then (b.multinomial : ℚ) else 0) := by
    rw [mul_pow, ← MvPolynomial.C_pow,
      mul_comm (MvPolynomial.C _ * _) (N.choose m : OrdinaryPolynomial),
      ← MvPolynomial.C_eq_coe_nat,
      ← mul_assoc, ← MvPolynomial.C_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_sum_X_pow_of_fintype]
    simp only [ordinaryWeight]
    split_ifs with hb <;> simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (ordinaryWeight b)]
  · simp
    ring
  · intro m hm hmd
    simp only [if_neg (Ne.symm hmd), mul_zero]
  · intro hb
    have hlt : N < ordinaryWeight b := by
      have hnl : ¬ ordinaryWeight b < N + 1 := by
        simpa only [Finset.mem_range] using hb
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]

def diagonalExponent (n : ℕ) : Fin 6 →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => n) (by simp)

@[simp] theorem diagonalExponent_apply (n : ℕ) (i : Fin 6) :
    diagonalExponent n i = n := rfl

@[simp] theorem diagonalExponent_weight (n : ℕ) :
    ordinaryWeight (diagonalExponent n) = 6 * n := by
  simp [ordinaryWeight, Finsupp.sum_fintype]

theorem diagonalExponent_multinomial (n : ℕ) :
    (diagonalExponent n).multinomial = WPReview.coefficientNat n := by
  have hm := Nat.multinomial_spec (Finset.univ : Finset (Fin 6)) (diagonalExponent n)
  rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at hm
  simp only [diagonalExponent_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, Nat.nsmul_eq_mul] at hm
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.factorial_pos n))
  rw [hm]
  simpa only [mul_comm] using (WPReview.coefficient_factorial_identity n).symm

/-- A diagonal ordinary exponent has precisely the checked sixfold
factorial coefficient. -/
theorem ordinaryF_pow_diagonal_coefficient (N n : ℕ) :
    MvPolynomial.coeff (diagonalExponent n) (ordinaryF ^ N) =
      (N.choose (6 * n) : ℚ) * (WPReview.coefficientNat n : ℚ) /
        (10 : ℚ) ^ (6 * n) := by
  rw [ordinaryF_pow_coefficient, diagonalExponent_weight, diagonalExponent_multinomial]
  have heven : (-1 : ℚ) ^ (6 * n) = 1 := by
    rw [show 6 * n = 2 * (3 * n) by omega, pow_mul]
    norm_num
  rw [div_pow, heven, one_div]
  ring

abbrev ordinaryDiagonal (b : Fin 6 →₀ ℕ) : Prop :=
  ∀ i, b i = b (Fin.last 5)

theorem ordinaryDiagonal_iff (b : Fin 6 →₀ ℕ) :
    ordinaryDiagonal b ↔ b = diagonalExponent (b (Fin.last 5)) := by
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    rw [h]
    rfl

/-- The diagonal coefficient functional on the ordinary representative.
The explicit Laurent bridge below identifies it with group-algebra CT. -/
def ordinaryConstantCoefficient (P : OrdinaryPolynomial) : ℚ := by
  classical
  exact ∑ b ∈ P.support, if ordinaryDiagonal b then MvPolynomial.coeff b P else 0

theorem ordinaryConstantCoefficient_eq_diagonal_sum (P : OrdinaryPolynomial)
    (p : ℕ) (hdegree : P.totalDegree < 6 * p) :
    ordinaryConstantCoefficient P =
      ∑ n ∈ Finset.range p, MvPolynomial.coeff (diagonalExponent n) P := by
  classical
  unfold ordinaryConstantCoefficient
  apply Finset.sum_bij_ne_zero (fun b _ _ => b (Fin.last 5))
  · intro b hb hne
    have hd : ordinaryDiagonal b := by
      by_contra h
      exact hne (if_neg h)
    have hb' : b = diagonalExponent (b (Fin.last 5)) := (ordinaryDiagonal_iff b).mp hd
    have hw : 6 * b (Fin.last 5) ≤ P.totalDegree := by
      have := MvPolynomial.le_totalDegree hb
      change ordinaryWeight b ≤ P.totalDegree at this
      have hweight := congrArg ordinaryWeight hb'
      rw [diagonalExponent_weight] at hweight
      rw [hweight] at this
      exact this
    exact Finset.mem_range.mpr (by omega)
  · intro b hb hbn c hc hcn heq
    have hbd : ordinaryDiagonal b := by
      by_contra h
      exact hbn (if_neg h)
    have hcd : ordinaryDiagonal c := by
      by_contra h
      exact hcn (if_neg h)
    rw [(ordinaryDiagonal_iff b).mp hbd, (ordinaryDiagonal_iff c).mp hcd, heq]
  · intro n hn hne
    have hb : diagonalExponent n ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
    have hd : ordinaryDiagonal (diagonalExponent n) := fun _ => rfl
    exact ⟨diagonalExponent n, hb, by simpa only [if_pos hd] using hne, rfl⟩
  · intro b hb hne
    have hd : ordinaryDiagonal b := by
      by_contra h
      exact hne (if_neg h)
    rw [if_pos hd, ← (ordinaryDiagonal_iff b).mp hd]

theorem ordinaryConstantCoefficient_F_pow (p N : ℕ) (hN : N < 6 * p) :
    ordinaryConstantCoefficient (ordinaryF ^ N) = WPReview.finiteCoefficient p N := by
  have hdegree : (ordinaryF ^ N).totalDegree < 6 * p := by
    have h := MvPolynomial.totalDegree_pow ordinaryF N
    have h' := Nat.mul_le_mul_left N ordinaryF_degree
    omega
  rw [ordinaryConstantCoefficient_eq_diagonal_sum _ p hdegree]
  unfold WPReview.finiteCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  exact ordinaryF_pow_diagonal_coefficient N n

/-- Coefficient selection below every expanded variable exponent. -/
theorem ordinaryExpand_mul_coefficient_below (p : ℕ) (hp : 0 < p)
    (P Q : OrdinaryPolynomial) (b : Fin 6 →₀ ℕ) (hb : ∀ i, b i < p) :
    MvPolynomial.coeff b (MvPolynomial.expand p P * Q) =
      MvPolynomial.coeff 0 P * MvPolynomial.coeff b Q := by
  classical
  rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single (0, b)]
  · simp [MvPolynomial.coeff_expand_zero p (Nat.ne_of_gt hp)]
  · intro x hx hxne
    have hsum : x.1 + x.2 = b := Finset.mem_antidiagonal.mp hx
    have hx0 : x.1 ≠ 0 := by
      intro hzero
      have hx2 : x.2 = b := by simpa only [hzero, zero_add] using hsum
      exact hxne (Prod.ext hzero hx2)
    have hex : ∃ i, x.1 i ≠ 0 := by
      by_contra h
      apply hx0
      ext i
      exact not_not.mp ((not_exists.mp h) i)
    obtain ⟨i, hi⟩ := hex
    have hsum_i : x.1 i + x.2 i = b i := by
      simpa using congrArg (fun d : Fin 6 →₀ ℕ => d i) hsum
    have hxlt : x.1 i < p := by have := hb i; omega
    have hdvd : ¬ p ∣ x.1 i := by
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
      omega
    rw [MvPolynomial.coeff_expand_of_not_dvd P hdvd]
    simp
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr (by simp))).elim

theorem ordinaryConstantCoefficient_expand_mul (p : ℕ) (hp : 0 < p)
    (P Q : OrdinaryPolynomial)
    (hPQ : (MvPolynomial.expand p P * Q).totalDegree < 6 * p)
    (hQ : Q.totalDegree < 6 * p) :
    ordinaryConstantCoefficient (MvPolynomial.expand p P * Q) =
      MvPolynomial.coeff 0 P * ordinaryConstantCoefficient Q := by
  rw [ordinaryConstantCoefficient_eq_diagonal_sum _ p hPQ,
    ordinaryConstantCoefficient_eq_diagonal_sum _ p hQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact ordinaryExpand_mul_coefficient_below p hp P Q (diagonalExponent n)
    (fun _ => Finset.mem_range.mp hn)

theorem ordinaryF_pow_zero_coefficient (N : ℕ) :
    MvPolynomial.coeff 0 (ordinaryF ^ N) = 1 := by
  rw [ordinaryF_pow_coefficient]
  simp [ordinaryWeight, Finsupp.multinomial]

/-- The exact finite support exclusion used in the five-weight identity. -/
theorem ordinaryConstantCoefficient_phi_power (p h m : ℕ) (hp : 0 < p)
    (hdegree : p * h + m < 6 * p) :
    ordinaryConstantCoefficient (ordinaryPhi p (ordinaryF ^ h) * ordinaryF ^ m) =
      ordinaryConstantCoefficient (ordinaryF ^ m) := by
  have hQ : (ordinaryF ^ m).totalDegree ≤ m := by
    exact (MvPolynomial.totalDegree_pow _ _).trans
      (by simpa using Nat.mul_le_mul_left m ordinaryF_degree)
  have hP : (ordinaryPhi p (ordinaryF ^ h)).totalDegree ≤ p * h := by
    rw [map_pow]
    exact (MvPolynomial.totalDegree_pow _ _).trans
      (by simpa only [mul_comm] using Nat.mul_le_mul_left h (ordinaryPhi_F_degree p))
  have hPQ : (ordinaryPhi p (ordinaryF ^ h) * ordinaryF ^ m).totalDegree < 6 * p := by
    exact lt_of_le_of_lt ((MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add hP hQ)) hdegree
  have hQlt : (ordinaryF ^ m).totalDegree < 6 * p := by omega
  exact (ordinaryConstantCoefficient_expand_mul p hp _ _ hPQ hQlt).trans
    (by rw [ordinaryF_pow_zero_coefficient, one_mul])

/-- The concrete diagonal quotient on ordinary natural exponents. -/
def ordinaryExponent : (Fin 6 →₀ ℕ) →+ Exponents where
  toFun b i := (b i.castSucc : ℤ) - b (Fin.last 5)
  map_zero' := by ext i; simp
  map_add' b c := by
    ext i
    simp only [Finsupp.add_apply, Nat.cast_add, Pi.add_apply]
    ring

theorem ordinaryExponent_eq_zero (b : Fin 6 →₀ ℕ) :
    ordinaryExponent b = 0 ↔ ordinaryDiagonal b := by
  constructor
  · intro h i
    refine Fin.lastCases (by rfl) (fun j => ?_) i
    have hj := congrFun h j
    change (b j.castSucc : ℤ) - b (Fin.last 5) = 0 at hj
    exact_mod_cast (sub_eq_zero.mp hj)
  · intro h
    ext i
    change (b i.castSucc : ℤ) - b (Fin.last 5) = 0
    rw [h i.castSucc, sub_self]

/-- Actual finite coefficient pushforward into the specified Laurent algebra. -/
def laurentMap : OrdinaryPolynomial →ₐ[ℚ] LaurentPolynomial :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ ordinaryExponent

@[simp] theorem laurentMap_monomial (b : Fin 6 →₀ ℕ) (c : ℚ) :
    laurentMap (MvPolynomial.monomial b c) =
      AddMonoidAlgebra.single (ordinaryExponent b) c := by
  simp [laurentMap, AddMonoidAlgebra.mapDomainAlgHom, MvPolynomial.monomial]

theorem laurentMap_coefficient (P : OrdinaryPolynomial) (x : Exponents) :
    (laurentMap P).coeff x =
      ∑ b ∈ P.support, if ordinaryExponent b = x then MvPolynomial.coeff b P else 0 := by
  classical
  simp [laurentMap, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain,
    Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply, MvPolynomial.coeff,
    MvPolynomial.support]

/-- The group-algebra constant coefficient selects six equal exponents. -/
theorem laurentMap_constantCoefficient (P : OrdinaryPolynomial) :
    (laurentMap P).coeff 0 = ordinaryConstantCoefficient P := by
  rw [laurentMap_coefficient]
  unfold ordinaryConstantCoefficient
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hd : ordinaryDiagonal b
  · have hx := (ordinaryExponent_eq_zero b).mpr hd
    simp only [if_pos hd, if_pos hx]
  · have hx : ordinaryExponent b ≠ 0 := fun h => hd ((ordinaryExponent_eq_zero b).mp h)
    simp only [if_neg hd, if_neg hx]

theorem ordinaryConstantCoefficient_add (P Q : OrdinaryPolynomial) :
    ordinaryConstantCoefficient (P + Q) =
      ordinaryConstantCoefficient P + ordinaryConstantCoefficient Q := by
  simp only [← laurentMap_constantCoefficient, map_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]

theorem ordinaryConstantCoefficient_smul (c : ℚ) (P : OrdinaryPolynomial) :
    ordinaryConstantCoefficient (c • P) = c * ordinaryConstantCoefficient P := by
  simp only [← laurentMap_constantCoefficient, map_smul, AddMonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul]

def ordinaryCTLinear : OrdinaryPolynomial →ₗ[ℚ] ℚ where
  toFun := ordinaryConstantCoefficient
  map_add' := ordinaryConstantCoefficient_add
  map_smul' c P := ordinaryConstantCoefficient_smul c P

theorem ordinaryG_scaled (p : ℕ) (hp : 0 < p) :
    (p : ℚ) • ordinaryG p = ordinaryPhi p ordinaryF - ordinaryF ^ p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  simp only [ordinaryG, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [mul_one_div_cancel hpq, MvPolynomial.C_1, one_mul]

theorem ordinaryConstantCoefficient_mixed (p r h j : ℕ) (hp : 0 < p)
    (hr : r ≤ p) (hhj : h + j ≤ 4) :
    ordinaryConstantCoefficient
      ((ordinaryPhi p ordinaryF) ^ h * (ordinaryF ^ p) ^ j * ordinaryF ^ (p - r)) =
      ordinaryConstantCoefficient (ordinaryF ^ ((j + 1) * p - r)) := by
  have hshift : p * j + (p - r) = (j + 1) * p - r := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm p j, Nat.add_sub_assoc hr]
  rw [← pow_mul, mul_assoc, ← pow_add, hshift, ← (ordinaryPhi p).map_pow]
  apply ordinaryConstantCoefficient_phi_power p h _ hp
  have hbound : p * (h + j + 1) ≤ p * 5 :=
    Nat.mul_le_mul_left p (by omega)
  have hm : (j + 1) * p - r ≤ (j + 1) * p := Nat.sub_le _ _
  nlinarith

def literalF : LaurentPolynomial := laurentMap ordinaryF

def literalG (p : ℕ) : LaurentPolynomial := laurentMap (ordinaryG p)

theorem ordinaryExponent_scale (p : ℕ) (b : Fin 6 →₀ ℕ) :
    ordinaryExponent (p • b) = exponentScale p (ordinaryExponent b) := by
  ext i
  simp [ordinaryExponent, exponentScale, Nat.cast_mul, mul_sub]

theorem ordinaryExponent_qSix (b : Fin 6 →₀ ℕ) :
    ordinaryExponent b = qSix (fun i => (b i : ℤ)) := rfl

theorem laurentMap_phi (p : ℕ) (P : OrdinaryPolynomial) :
    laurentMap (ordinaryPhi p P) = phi p (laurentMap P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | monomial b c =>
      change laurentMap (MvPolynomial.expand p (MvPolynomial.monomial b c)) = _
      simp only [MvPolynomial.expand_monomial,
        laurentMap_monomial, phi_single, ordinaryExponent_scale]

theorem literalG_scaled (p : ℕ) (hp : 0 < p) :
    (p : ℚ) • literalG p = phi p literalF - literalF ^ p := by
  rw [literalG, ← map_smul, ordinaryG_scaled p hp, map_sub, laurentMap_phi, map_pow]
  rfl

theorem literalG_formula (p : ℕ) :
    literalG p = (1 / (p : ℚ)) • (phi p literalF - literalF ^ p) := by
  simp only [literalG, ordinaryG, ← MvPolynomial.smul_eq_C_mul, map_smul,
    map_sub, laurentMap_phi, map_pow, literalF]

theorem literalF_formula :
    literalF = 1 - (1 / 10 : ℚ) • ∑ i : Fin 6, laurentMap (MvPolynomial.X i) := by
  simp only [literalF, ordinaryF, ← MvPolynomial.smul_eq_C_mul,
    map_sub, map_one, map_smul, map_sum]

theorem laurentMap_integral (p : ℕ) (hp : p.Prime) (P : OrdinaryPolynomial)
    (hP : ∀ b, pIntegral p (MvPolynomial.coeff b P)) (x : Exponents) :
    pIntegral p ((laurentMap P).coeff x) := by
  classical
  rw [laurentMap_coefficient]
  apply pIntegral_sum p hp
  intro b hb
  by_cases h : ordinaryExponent b = x
  · simpa only [if_pos h] using hP b
  · simpa only [if_neg h, Nat.cast_zero] using pIntegral_natCast p hp 0

theorem literalF_coefficient_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (x : Exponents) : pIntegral p (literalF.coeff x) :=
  laurentMap_integral p hp ordinaryF (ordinaryF_coefficient_integral p hp hp7) x

theorem literalG_coefficient_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (x : Exponents) : pIntegral p ((literalG p).coeff x) :=
  laurentMap_integral p hp (ordinaryG p) (ordinaryG_coefficient_integral p hp hp7) x

theorem literalF_power_constantCoefficient (p N : ℕ) (hN : N < 6 * p) :
    (literalF ^ N).coeff 0 = WPReview.finiteCoefficient p N := by
  rw [literalF, ← map_pow, laurentMap_constantCoefficient]
  exact ordinaryConstantCoefficient_F_pow p N hN

theorem constantCoefficient_laurentMap (P : OrdinaryPolynomial) :
    constantCoefficient (laurentMap P) = ordinaryConstantCoefficient P :=
  laurentMap_constantCoefficient P

theorem laurentMap_monomial_CT (b : Fin 6 →₀ ℕ) (c : ℚ) :
    constantCoefficient (laurentMap (MvPolynomial.monomial b c)) =
      if ordinaryDiagonal b then c else 0 := by
  classical
  rw [laurentMap_monomial]
  change (AddMonoidAlgebra.single (ordinaryExponent b) c).coeff 0 = _
  by_cases hd : ordinaryDiagonal b
  · have hx := (ordinaryExponent_eq_zero b).mpr hd
    simp [hd, hx]
  · have hx : ordinaryExponent b ≠ 0 := fun h => hd ((ordinaryExponent_eq_zero b).mp h)
    simp [hd, Ne.symm hx]

theorem literalF_power_CT (p N : ℕ) (hN : N < 6 * p) :
    constantCoefficient (literalF ^ N) = WPReview.finiteCoefficient p N :=
  literalF_power_constantCoefficient p N hN

theorem literal_mixed_CT (p r h j : ℕ) (hp : 0 < p) (hr : r ≤ p) (hhj : h + j ≤ 4) :
    constantCoefficient
      ((phi p literalF) ^ h * (literalF ^ p) ^ j * literalF ^ (p - r)) =
      constantCoefficient (literalF ^ ((j + 1) * p - r)) := by
  have hmap :
      laurentMap ((ordinaryPhi p ordinaryF) ^ h * (ordinaryF ^ p) ^ j *
        ordinaryF ^ (p - r)) =
        (phi p literalF) ^ h * (literalF ^ p) ^ j * literalF ^ (p - r) := by
    simp only [map_mul, map_pow, laurentMap_phi, literalF]
  have hpow : laurentMap (ordinaryF ^ ((j + 1) * p - r)) =
      literalF ^ ((j + 1) * p - r) := by
    simpa only [literalF] using (map_pow laurentMap ordinaryF ((j + 1) * p - r))
  rw [← hmap, constantCoefficient_laurentMap, ← hpow, constantCoefficient_laurentMap]
  exact ordinaryConstantCoefficient_mixed p r h j hp hr hhj

/-- The exact scalar row weights of the finite literal Cartier column. -/
theorem literal_five_weight_identity (p r : ℕ) (hp : 0 < p) (hr : r ≤ p) :
    (∑ k ∈ Finset.range 5, (p : ℚ) ^ k *
      constantCoefficient (literalG p ^ k * literalF ^ (p - r))) =
      WPReview.fiveInterpolation
        (fun a => constantCoefficient (literalF ^ (a * p - r))) := by
  have hexcl (h j : ℕ) (hhj : h + j ≤ 4) :
      constantCoefficient
        ((phi p literalF) ^ h * (literalF ^ p) ^ j * literalF ^ (p - r)) =
      constantCoefficient ((literalF ^ p) ^ j * literalF ^ (p - r)) := by
    have h0 := literal_mixed_CT p r 0 j hp hr (by omega)
    simp only [pow_zero, one_mul] at h0
    exact (literal_mixed_CT p r h j hp hr hhj).trans h0.symm
  have hs := scalar_weighted_hockey_stick (p : ℚ) (phi p literalF)
    (literalF ^ p) (literalF ^ (p - r)) (literalG p) constantCoefficient
    (literalG_scaled p hp) hexcl
  have h1 := literal_mixed_CT p r 0 1 hp hr (by decide)
  have h2 := literal_mixed_CT p r 0 2 hp hr (by decide)
  have h3 := literal_mixed_CT p r 0 3 hp hr (by decide)
  have h4 := literal_mixed_CT p r 0 4 hp hr (by decide)
  simp only [pow_zero, pow_one, one_mul] at h1 h2 h3 h4
  rw [h1, h2, h3, h4] at hs
  simpa only [WPReview.fiveInterpolation, one_mul] using hs

/-- The finite literal selector scalar is exactly the retained five-point
coefficient expression, before the interpolation congruence. -/
theorem literal_five_weight_finiteCoefficient (p r : ℕ) (hp : 0 < p) (hr : r ≤ p) :
    (∑ k ∈ Finset.range 5, (p : ℚ) ^ k *
      constantCoefficient (literalG p ^ k * literalF ^ (p - r))) =
      WPReview.fiveInterpolation (fun a => WPReview.finiteCoefficient p (a * p - r)) := by
  rw [literal_five_weight_identity p r hp hr]
  simp only [WPReview.fiveInterpolation]
  have hN (a : ℕ) (ha : a ≤ 5) : a * p - r < 6 * p := by
    have := Nat.mul_le_mul_right p ha
    have := Nat.sub_le (a * p) r
    omega
  rw [literalF_power_CT p _ (hN 1 (by decide)),
    literalF_power_CT p _ (hN 2 (by decide)),
    literalF_power_CT p _ (hN 3 (by decide)),
    literalF_power_CT p _ (hN 4 (by decide)),
    literalF_power_CT p _ (hN 5 (by decide))]

theorem literal_five_weight_binomial (p r : ℕ) (hp : 0 < p) (hr : r ≤ p) :
    (∑ k ∈ Finset.range 5, (p : ℚ) ^ k *
      constantCoefficient (literalG p ^ k * literalF ^ (p - r))) =
      ∑ a ∈ Finset.range 5, (-1 : ℚ) ^ a * (Nat.choose 5 (a + 1) : ℚ) *
        constantCoefficient (literalF ^ ((a + 1) * p - r)) := by
  rw [literal_five_weight_identity p r hp hr, WPReview.fiveInterpolation_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha5 : a < 5 := Finset.mem_range.mp ha
  interval_cases a <;> norm_num [WPReview.interpolationWeight, Nat.choose]

end

end WPCartierFinite
