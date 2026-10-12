import WPActualGaussBottom

open scoped BigOperators Polynomial
open Polynomial WPActualCMGauss

namespace WPFieldAssembly.ActualGaussHarmonic

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- These are the literal integer shifted-Legendre coefficients in the field. -/
noncomputable def gaussA (d n : ℕ) : K :=
  (-1 : K)^n*(d.choose n : K)*((d+n).choose d : K)

theorem gaussA_zero (d : ℕ) : gaussA (K:=K) d 0=1 := by
  simp [gaussA]

theorem gaussA_tail (d n : ℕ) (hn : d<n) : gaussA (K:=K) d n=0 := by
  simp only [gaussA,Nat.choose_eq_zero_of_lt hn,Nat.cast_zero,mul_zero,zero_mul]

/-- The entire coefficient recurrence includes the terminal zero. -/
theorem gaussA_recurrence (d n : ℕ) :
    ((n : K)+1)^2*gaussA (K:=K) d (n+1)=
      ((n : K)-d)*((n : K)+d+1)*gaussA (K:=K) d n := by
  have he := congrArg (Int.castRingHom K) (shiftedLegendre_cleared_recurrence d n)
  simpa only [coeff_shiftedLegendre,map_mul,map_pow,map_add,map_sub,map_natCast,
    map_one,map_neg,gaussA] using he

/-- Contiguity changes the actual integer degree, with no singular scalar division. -/
theorem gaussA_degree_step (d n : ℕ) :
    ((d : K)+1-n)*gaussA (K:=K) (d+1) n=
      ((d : K)+1+n)*gaussA (K:=K) d n := by
  by_cases hn : n≤d+1
  · have h1 : ((d+1).choose n : K)*((d : K)+1-n)=
        (d.choose n : K)*((d : K)+1) := by
      have he := congrArg (fun r : ℕ => (r : K)) (Nat.choose_mul_succ_eq d n).symm
      simpa only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_add,Nat.cast_one] using he
    have h2 : ((d+n+1).choose (d+1) : K)*((d : K)+1)=
        ((d+n).choose d : K)*((d : K)+n+1) := by
      have he := congrArg (fun r : ℕ => (r : K)) (Nat.add_one_mul_choose_eq (d+n) d).symm
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_comm] using he
    unfold gaussA
    rw [show d+1+n=d+n+1 by omega]
    calc
      _ = (-1 : K)^n*(((d+1).choose n : K)*((d : K)+1-n))*
          ((d+n+1).choose (d+1) : K) := by ring
      _ = (-1 : K)^n*(d.choose n : K)*
          (((d+n+1).choose (d+1) : K)*((d : K)+1)) := by rw [h1]; ring
      _ = _ := by rw [h2]; ring
  · rw [gaussA_tail (d+1) n (by omega),gaussA_tail d n (by omega)]
    ring

noncomputable def gaussT (d n : ℕ) : K := gaussA (K:=K) d n/((d+n : ℕ) : K)

/-- One finite telescoper proves the entire finite identity at z=d. -/
theorem gaussT_telescoper (d n : ℕ)
    (hleft : ((d+n : ℕ) : K)≠0) (hright : ((d+n+1 : ℕ) : K)≠0) :
    (d : K)^2*gaussT (K:=K) d n=
      (n : K)^2*gaussT (K:=K) d n-
        ((n : K)+1)^2*gaussT (K:=K) d (n+1) := by
  have hr := gaussA_recurrence (K:=K) d n
  have hl : (d : K)+n≠0 := by simpa only [Nat.cast_add] using hleft
  have hh : (d : K)+n+1≠0 := by simpa only [Nat.cast_add,Nat.cast_one] using hright
  unfold gaussT
  simp only [Nat.cast_add,Nat.cast_one,←add_assoc]
  field_simp [hl,hh]
  linear_combination ((d : K)+n)*hr

/-- The full finite row sums to zero; both its zero and terminal slots are retained. -/
theorem gaussT_sum_zero (d : ℕ) (hd : 1≤d)
    (hu : ∀ n : ℕ, 1≤n → n≤2*d+1 → (n : K)≠0) :
    (∑ n ∈ Finset.range (d+1),gaussT (K:=K) d n)=0 := by
  have hs (m : ℕ) (hm : m≤d+1) :
      (d : K)^2*(∑ n ∈ Finset.range m,gaussT (K:=K) d n)=
        -(m : K)^2*gaussT (K:=K) d m := by
    induction m with
    | zero => simp only [Finset.range_zero,Finset.sum_empty,Nat.cast_zero,
        zero_pow (by omega : (2 : ℕ)≠0),neg_zero,mul_zero,zero_mul]
    | succ m ih =>
      have hi := ih (by omega)
      have ht := gaussT_telescoper (K:=K) d m
        (hu (d+m) (by omega) (by omega))
        (hu (d+m+1) (by omega) (by omega))
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linear_combination hi+ht
  have he := hs (d+1) (by omega)
  rw [gaussT,gaussA_tail d (d+1) (by omega),zero_div,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (hu d hd (by omega)))

end WPFieldAssembly.ActualGaussHarmonic
