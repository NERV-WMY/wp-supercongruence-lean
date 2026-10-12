import WPKFifthEndpoint
import WPActualPartialHarmonic

open scoped BigOperators
open WPFiniteField

namespace WPFieldAssembly.ActualHarmonicReflection

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K]

noncomputable def harmonicTwo (n : ℕ) : K :=
  ∑ j ∈ Finset.Ico 1 (n+1), 1/(j : K)^2

theorem harmonicTwo_split (n m : ℕ) (hnm : n ≤ m) :
    harmonicTwo (K := K) m=harmonicTwo n+
      ∑ j ∈ Finset.Ico (n+1) (m+1), 1/(j : K)^2 := by
  exact (Finset.sum_Ico_consecutive (fun j => 1/(j : K)^2)
    (by omega : 1 ≤ n+1) (by omega : n+1 ≤ m+1)).symm

theorem harmonicTwo_reflected_suffix (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hn : n < p) :
    (∑ j ∈ Finset.Ico (n+1) p, 1/(j : K)^2)=harmonicTwo (K := K) (p-1-n) := by
  have hr := Finset.sum_Ico_reflect (fun j => 1/(j : K)^2) 1
    (m := p-n) (n := p) (by omega)
  rw [show p+1-(p-n)=n+1 by omega, show p+1-1=p by omega] at hr
  rw [←hr]
  unfold harmonicTwo
  rw [show p-1-n+1=p-n by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [reflected_denominator p j (Finset.mem_Ico.mpr (by omega)), neg_sq]

theorem harmonicTwo_full_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    harmonicTwo (K := K) (p-1)=0 := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_one_eq_zero p (by omega))
  rw [←R_castHom, map_one, map_zero] at h
  simpa only [R, harmonicTwo, one_pow,
    Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using h

theorem harmonicTwo_half_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    harmonicTwo (K := K) ((p-1)/2)=0 := by
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hs := harmonicTwo_split (K := K) ((p-1)/2) (p-1) (by omega)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    harmonicTwo_reflected_suffix p ((p-1)/2) (by omega),
    show p-1-(p-1)/2=(p-1)/2 by omega, harmonicTwo_full_zero p hp] at hs
  have h2 : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  apply (mul_eq_zero.mp (show (2 : K)*harmonicTwo ((p-1)/2)=0 by
    linear_combination -hs)).resolve_left h2

private theorem harmonicTwo_even_part (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hn : n < p) :
    (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => 2 ∣ j), 1/(j : K)^2)=
      harmonicTwo (K := K) (n/2)/4 := by
  rw [WPActualPartialHarmonic.even_filter_sum]
  unfold harmonicTwo
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hu : (j : K) ≠ 0 := denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  push_cast
  field_simp [hu, h2, h4]
  ring

theorem harmonicTwo_odd_part (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hn : n < p) :
    (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => ¬2 ∣ j), 1/(j : K)^2)=
      harmonicTwo (K := K) n-harmonicTwo (n/2)/4 := by
  have hs : (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => 2 ∣ j), 1/(j : K)^2)+
      (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => ¬2 ∣ j), 1/(j : K)^2)=
      harmonicTwo (K := K) n := by
    rw [Finset.sum_filter, Finset.sum_filter, ←Finset.sum_add_distrib]
    unfold harmonicTwo
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : 2 ∣ j <;> simp only [he, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, add_zero, zero_add]
  rw [harmonicTwo_even_part p n hp hn] at hs
  linear_combination hs

/-- The entire odd band is a bijective image; neither end index is omitted. -/
theorem proper_odd_band_image (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (Finset.Ico (p/6+1) ((p-1)/2+1)).image (fun j => p-2*j)=
      (Finset.Ico 1 (p-1-p/3+1)).filter (fun j => ¬2 ∣ j) := by
  have hc := WPActualNativeParameter.prime_six_classes p (by omega)
  ext r
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨j, ⟨hj0, hjN⟩, rfl⟩
    have hrmod : (p-2*j)%2=1 := by rcases hc with h | h <;> omega
    refine ⟨⟨by rcases hc with h | h <;> omega,
      by rcases hc with h | h <;> omega⟩, ?_⟩
    simpa only [Nat.dvd_iff_mod_eq_zero, hrmod] using (by omega : (1 : ℕ) ≠ 0)
  · rintro ⟨⟨hr0, hrK⟩, hrOdd⟩
    have hrmod : r%2=1 := by
      have hlt := Nat.mod_lt r (by omega : 0 < 2)
      have hz : r%2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hrOdd
      omega
    refine ⟨(p-r)/2, ⟨?_, ?_⟩, ?_⟩ <;> rcases hc with h | h <;> omega

theorem proper_second_harmonic_band (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : K)^2)=
      4*harmonicTwo (K := K) (p-1-p/3)-harmonicTwo (p/3) := by
  have hc := WPActualNativeParameter.prime_six_classes p (by omega)
  have hi : Set.InjOn (fun j => p-2*j)
      (Finset.Ico (p/6+1) ((p-1)/2+1) : Set ℕ) := by
    intro j hj k hk he
    have hj' := Finset.mem_Ico.mp hj
    have hk' := Finset.mem_Ico.mp hk
    change p-2*j=p-2*k at he
    omega
  have he : (∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : K)^2)=
      ∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 4/((p-2*j : ℕ) : K)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hle : 2*j ≤ p := by omega
    have hu : (j : K) ≠ 0 := denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
    have h2 : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat, CharP.cast_eq_zero K p, zero_sub]
    field_simp [hu, h2]
    ring
  have him : (∑ r ∈ (Finset.Ico (p/6+1) ((p-1)/2+1)).image (fun j => p-2*j),
      4/(r : K)^2)=
        ∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 4/((p-2*j : ℕ) : K)^2 := by
    apply Finset.sum_image
    exact hi
  rw [he, ←him, proper_odd_band_image p hp]
  have hs : (∑ j ∈ (Finset.Ico 1 (p-1-p/3+1)).filter (fun j => ¬2 ∣ j),
      4/(j : K)^2)=4*∑ j ∈ (Finset.Ico 1 (p-1-p/3+1)).filter (fun j => ¬2 ∣ j),
        1/(j : K)^2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
  rw [hs, harmonicTwo_odd_part p (p-1-p/3) hp (by omega),
    show (p-1-p/3)/2=p/3 by rcases hc with h | h <;> omega]
  have h4 : (4 : K) ≠ 0 := denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  field_simp [h4]

/-- The second-harmonic terms cancel in the actual NC95 proper endpoint. -/
theorem actual_sixth_second_harmonic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : harmonicTwo (K := K) (p/6)=5*harmonicTwo (p/3) := by
  have hc := WPActualNativeParameter.prime_six_classes p (by omega)
  have hf := harmonicTwo_split (K := K) (p/3) (p-1) (by omega)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    harmonicTwo_reflected_suffix p (p/3) (by omega), harmonicTwo_full_zero p hp] at hf
  have hs := harmonicTwo_split (K := K) (p/6) ((p-1)/2)
    (by rcases hc with h | h <;> omega)
  rw [harmonicTwo_half_zero p hp, proper_second_harmonic_band p hp] at hs
  linear_combination -hs+4*hf

end WPFieldAssembly.ActualHarmonicReflection
