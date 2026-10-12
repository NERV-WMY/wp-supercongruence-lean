import WPFieldAssembly.ActualGaussHarmonic

open scoped BigOperators

namespace WPFieldAssembly.ActualGaussHarmonic

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

noncomputable def gaussHarmonic (d : ℕ) : K :=
  ∑ n ∈ Finset.range d,1/((n+1 : ℕ) : K)

noncomputable def gaussFirstMoment (d : ℕ) : K :=
  ∑ n ∈ Finset.range (d+1),gaussA (K:=K) d n/(n : K)

noncomputable def gaussSecondMoment (d : ℕ) : K :=
  ∑ n ∈ Finset.range (d+1),gaussA (K:=K) d n/(n : K)^2

private theorem gaussA_difference (d n : ℕ)
    (hden : ((d+1+n : ℕ) : K)≠0) :
    gaussA (K:=K) (d+1) n-gaussA (K:=K) d n=
      2*(n : K)*gaussA (K:=K) (d+1) n/((d+1+n : ℕ) : K) := by
  have hc := gaussA_degree_step (K:=K) d n
  have hu : (d : K)+1+n≠0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hden
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp [hu]
  linear_combination hc

private theorem gauss_first_step_term (d n : ℕ)
    (hunit : (n : K)≠0) (hden : ((d+1+n : ℕ) : K)≠0) :
    gaussA (K:=K) (d+1) n/(n : K)-gaussA (K:=K) d n/(n : K)=
      2*gaussT (K:=K) (d+1) n := by
  rw [←sub_div,gaussA_difference d n hden,gaussT]
  field_simp [hunit,hden]

private theorem gauss_second_step_term (d n : ℕ)
    (hunit : (n : K)≠0) (hd : ((d+1 : ℕ) : K)≠0)
    (hden : ((d+1+n : ℕ) : K)≠0) :
    gaussA (K:=K) (d+1) n/(n : K)^2-gaussA (K:=K) d n/(n : K)^2=
      (2/((d+1 : ℕ) : K))*
        (gaussA (K:=K) (d+1) n/(n : K)-gaussT (K:=K) (d+1) n) := by
  rw [←sub_div,gaussA_difference d n hden,gaussT]
  have hh : (d : K)+1≠0 := by simpa only [Nat.cast_add,Nat.cast_one] using hd
  have hn : (d : K)+1+n≠0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hden
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp [hunit,hh,hn]
  ring

theorem gaussFirstMoment_step (d : ℕ)
    (hu : ∀ n : ℕ, 1≤n → n≤2*d+3 → (n : K)≠0) :
    gaussFirstMoment (K:=K) (d+1)-gaussFirstMoment (K:=K) d=
      -2/((d+1 : ℕ) : K) := by
  have ht (n : ℕ) (hn : n∈Finset.range (d+2)) :
      gaussA (K:=K) (d+1) n/(n : K)-gaussA (K:=K) d n/(n : K)=
        2*gaussT (K:=K) (d+1) n-
          (if n=0 then 2/((d+1 : ℕ) : K) else 0) := by
    by_cases hz : n=0
    · subst n
      (simp only [Nat.cast_zero,div_zero,sub_self,gaussT,Nat.add_zero,gaussA_zero,
        if_true]; ring)
    · rw [if_neg hz,sub_zero]
      exact gauss_first_step_term d n (hu n (by omega)
        (by have := Finset.mem_range.mp hn; omega))
        (hu (d+1+n) (by omega) (by have := Finset.mem_range.mp hn; omega))
  have hs := Finset.sum_congr rfl ht
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at hs
  have hz := gaussT_sum_zero (K:=K) (d+1) (by omega)
    (fun n hn hb => hu n hn (by omega))
  have hp : (∑ n ∈ Finset.range (d+2),gaussA (K:=K) d n/(n : K))=
      gaussFirstMoment (K:=K) d := by
    rw [show d+2=(d+1)+1 by omega,Finset.sum_range_succ,
      gaussA_tail d (d+1) (by omega),zero_div,add_zero]
    rfl
  rw [hp,hz,mul_zero,zero_sub] at hs
  simpa only [gaussFirstMoment,show d+1+1=d+2 by omega,
    Finset.sum_ite_eq',Finset.mem_range,show 0<d+2 by omega,if_true,neg_div] using hs

theorem gaussFirstMoment_value (d : ℕ)
    (hu : ∀ n : ℕ, 1≤n → n≤2*d+1 → (n : K)≠0) :
    gaussFirstMoment (K:=K) d=-2*gaussHarmonic (K:=K) d := by
  induction d with
  | zero => simp [gaussFirstMoment,gaussHarmonic]
  | succ d ih =>
    have hi := ih (fun n hn hb => hu n hn (by omega))
    have hs := gaussFirstMoment_step (K:=K) d
      (fun n hn hb => hu n hn (by omega))
    rw [gaussHarmonic,Finset.sum_range_succ]
    change gaussFirstMoment (K:=K) (d+1)=
      -2*(gaussHarmonic (K:=K) d+1/((d+1 : ℕ) : K))
    linear_combination hs+hi

theorem gaussSecondMoment_step (d : ℕ)
    (hu : ∀ n : ℕ, 1≤n → n≤2*d+3 → (n : K)≠0) :
    gaussSecondMoment (K:=K) (d+1)-gaussSecondMoment (K:=K) d=
      (2/((d+1 : ℕ) : K))*gaussFirstMoment (K:=K) (d+1)+
        2/((d+1 : ℕ) : K)^2 := by
  have hd := hu (d+1) (by omega) (by omega)
  have ht (n : ℕ) (hn : n∈Finset.range (d+2)) :
      gaussA (K:=K) (d+1) n/(n : K)^2-gaussA (K:=K) d n/(n : K)^2=
        (2/((d+1 : ℕ) : K))*
          (gaussA (K:=K) (d+1) n/(n : K)-gaussT (K:=K) (d+1) n)+
          (if n=0 then 2/((d+1 : ℕ) : K)^2 else 0) := by
    by_cases hz : n=0
    · subst n
      (simp only [Nat.cast_zero,zero_pow (by omega : (2 : ℕ)≠0),div_zero,sub_self,
        gaussT,Nat.add_zero,gaussA_zero,if_true]; field_simp [hd]; ring)
    · rw [if_neg hz,add_zero]
      exact gauss_second_step_term d n (hu n (by omega)
        (by have := Finset.mem_range.mp hn; omega)) hd
        (hu (d+1+n) (by omega) (by have := Finset.mem_range.mp hn; omega))
  have hs := Finset.sum_congr rfl ht
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hz := gaussT_sum_zero (K:=K) (d+1) (by omega)
    (fun n hn hb => hu n hn (by omega))
  have hp : (∑ n ∈ Finset.range (d+2),gaussA (K:=K) d n/(n : K)^2)=
      gaussSecondMoment (K:=K) d := by
    rw [show d+2=(d+1)+1 by omega,Finset.sum_range_succ,
      gaussA_tail d (d+1) (by omega),zero_div,add_zero]
    rfl
  rw [hp,hz,sub_zero] at hs
  simpa only [gaussFirstMoment,gaussSecondMoment,show d+1+1=d+2 by omega,
    Finset.sum_ite_eq',Finset.mem_range,show 0<d+2 by omega,if_true] using hs

/-- The second harmonic moment uses the same entire finite integer row. -/
theorem gaussSecondMoment_value (d : ℕ)
    (hu : ∀ n : ℕ, 1≤n → n≤2*d+1 → (n : K)≠0) :
    gaussSecondMoment (K:=K) d=-2*(gaussHarmonic (K:=K) d)^2 := by
  induction d with
  | zero => simp [gaussSecondMoment,gaussHarmonic]
  | succ d ih =>
    have hi := ih (fun n hn hb => hu n hn (by omega))
    have hs := gaussSecondMoment_step (K:=K) d
      (fun n hn hb => hu n hn (by omega))
    have hf := gaussFirstMoment_value (K:=K) (d+1) hu
    have hd := hu (d+1) (by omega) (by omega)
    rw [hf,gaussHarmonic,Finset.sum_range_succ] at hs
    change gaussSecondMoment (K:=K) (d+1)-gaussSecondMoment (K:=K) d=
      (2/((d+1 : ℕ) : K))*(-2*(gaussHarmonic (K:=K) d+1/((d+1 : ℕ) : K)))+
        2/((d+1 : ℕ) : K)^2 at hs
    rw [gaussHarmonic,Finset.sum_range_succ]
    change gaussSecondMoment (K:=K) (d+1)=
      -2*(gaussHarmonic (K:=K) d+1/((d+1 : ℕ) : K))^2
    have hc : -2*(gaussHarmonic (K:=K) d+1/((d+1 : ℕ) : K))^2-
        gaussSecondMoment (K:=K) d=
        (2/((d+1 : ℕ) : K))*(-2*(gaussHarmonic (K:=K) d+1/((d+1 : ℕ) : K)))+
          2/((d+1 : ℕ) : K)^2 := by
      rw [hi]
      field_simp [hd]
      ring
    linear_combination hs-hc

end WPFieldAssembly.ActualGaussHarmonic
