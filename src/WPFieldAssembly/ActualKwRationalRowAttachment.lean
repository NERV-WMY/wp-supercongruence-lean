import WPFieldAssembly.ActualKwOrderedEndpoints
import WPFieldAssembly.ActualRationalSignRows

namespace WPFieldAssembly.ActualKwRationalRowAttachment

open ActualKwOrderedEndpoints ActualKwFiniteHBridge ActualRationalSignRows
open WPFiniteField WPFiniteSignTrace

variable {K : Type*} [Field K]

/- The original half-cutoff S and every k=j diagonal are retained. The checked
full sign identity supplies the conversion; neither G endpoint is assigned. -/

theorem native_S_full_trace (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x y : K) :
    WPFiniteLoop.S p x y=fullTraceS p x y := by
  simp only [full_trace_eq_half_cutoff p hp]

theorem native_S_one_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1 : K) 1=2*(q2 (K:=K) p)^2 := by
  rw [native_S_full_trace p hp]
  exact S_one_one p hp

theorem native_S_half_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1/2 : K) 1=-(2/3 : K)*R p (-2 : K)-
      (16/3 : K)*(q2 (K:=K) p)^2+4*q2 p*q3 p-(3/4 : K)*(q3 p)^2 := by
  rw [native_S_full_trace p hp]
  exact S_half_one p hp

theorem native_S_one_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1 : K) 2=(2/3 : K)*R p (-2 : K)-
      (2/3 : K)*(q2 (K:=K) p)^2-4*q2 p*q3 p+3*(q3 p)^2 := by
  rw [native_S_full_trace p hp]
  exact S_one_two p hp

theorem native_S_half_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1/2 : K) (1/2)=-R p (-2 : K)/3+
      (2*q2 (K:=K) p-3*q3 p)^2/12 := by
  rw [native_S_full_trace p hp]
  exact S_half_half p hp

theorem native_S_two_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (2 : K) 2=(10/3 : K)*R p (-2 : K)-
      (10/3 : K)*(q2 (K:=K) p)^2+4*q2 p*q3 p+(3/2 : K)*(q3 p)^2 := by
  rw [native_S_full_trace p hp]
  exact S_two_two p hp

theorem native_S_two_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (2 : K) 1=-(4/3 : K)*R p (-2 : K)+
      (4/3 : K)*(q2 (K:=K) p)^2+2*q2 p*q3 p-(3/2 : K)*(q3 p)^2 := by
  rw [native_S_full_trace p hp]
  exact S_two_one p hp

theorem native_S_one_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1 : K) (1/2)=-(2/3 : K)*R p (-2 : K)+
      (2*q2 (K:=K) p-3*q3 p)^2/6 := by
  rw [native_S_full_trace p hp]
  exact S_one_half p hp

/-- All seven native rows use the original full diagonal convention. -/
theorem actual_rational_trace_rows (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteLoop.S p (1 : K) 1=2*(q2 (K:=K) p)^2 ∧
    WPFiniteLoop.S p (1/2 : K) 1=-(2/3 : K)*R p (-2 : K)-
      (16/3 : K)*(q2 (K:=K) p)^2+4*q2 p*q3 p-(3/4 : K)*(q3 p)^2 ∧
    WPFiniteLoop.S p (1 : K) 2=(2/3 : K)*R p (-2 : K)-
      (2/3 : K)*(q2 (K:=K) p)^2-4*q2 p*q3 p+3*(q3 p)^2 ∧
    WPFiniteLoop.S p (1/2 : K) (1/2)=-R p (-2 : K)/3+
      (2*q2 (K:=K) p-3*q3 p)^2/12 ∧
    WPFiniteLoop.S p (2 : K) 2=(10/3 : K)*R p (-2 : K)-
      (10/3 : K)*(q2 (K:=K) p)^2+4*q2 p*q3 p+(3/2 : K)*(q3 p)^2 ∧
    WPFiniteLoop.S p (2 : K) 1=-(4/3 : K)*R p (-2 : K)+
      (4/3 : K)*(q2 (K:=K) p)^2+2*q2 p*q3 p-(3/2 : K)*(q3 p)^2 ∧
    WPFiniteLoop.S p (1 : K) (1/2)=-(2/3 : K)*R p (-2 : K)+
      (2*q2 (K:=K) p-3*q3 p)^2/6 := by
  exact ⟨native_S_one_one p hp,native_S_half_one p hp,native_S_one_two p hp,
    native_S_half_half p hp,native_S_two_two p hp,native_S_two_one p hp,native_S_one_half p hp⟩

/-- SB103's literal seven-row combination is attached to the native half-cutoff source. -/
theorem actual_SB103_rational_combination (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    rationalOrderedRows (K:=K) p=
      (17/5 : K)*R p (-2 : K)-(18/5 : K)*(q2 (K:=K) p)^2+
        (63/5 : K)*q2 p*q3 p-(18/5 : K)*(q3 p)^2 := by
  unfold rationalOrderedRows
  simp only [native_S_full_trace p hp]
  exact SB103_ordered_rational_combination p hp

theorem movingTw_actual_rational_rows (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    -movingTw (K:=K) p=
      (17/5 : K)*R p (-2 : K)-(18/5 : K)*(q2 (K:=K) p)^2+
        (63/5 : K)*q2 p*q3 p-(18/5 : K)*(q3 p)^2-3*originalT5 p u/2+
          2*originalG p (1/5)/5-11*originalG p (3/11)/10-
        movingDend p/5*(33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-
          138*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
            ActualKwWeightedTrace.finiteLogValue p 16) := by
  rw [movingTw_SB103e p hp u hu,actual_SB103_rational_combination p hp]

/-- The exact NC130 input retains both G carriers and the original whole Q11 quotient. -/
theorem actual_T5_consumer_rational_rows (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (2/3 : K)*(-movingTw p)+originalT5 p u=
      (34/15 : K)*R p (-2 : K)-(12/5 : K)*(q2 (K:=K) p)^2+
        (42/5 : K)*q2 p*q3 p-(12/5 : K)*(q3 p)^2+
          (4/15 : K)*originalG p (1/5)-(11/15 : K)*originalG p (3/11)-
      (2/15 : K)*(q2 p+3*q3 p/4)*
        (33*(WPFiniteInversion.integerFermatQuotient p 11 : K)-74*q2 p-15*q3 p-
          15*(WPFiniteInversion.integerFermatQuotient p 5 : K)) := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  have h2 : (2 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 2 (by omega) (by omega)
  have h3 : (3 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 3 (by omega) (by omega)
  have h4 : (4 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 4 (by omega) (by omega)
  have h5 : (5 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 5 (by omega) (by omega)
  have h15 : (15 : K)≠0 := by simpa only [Nat.cast_ofNat] using hn 15 (by omega) (by omega)
  rw [original_T5_consumer_fermat p hp u hu,actual_SB103_rational_combination p hp]
  unfold q2 q3
  field_simp [h2,h3,h4,h5,h15]
  ring

end WPFieldAssembly.ActualKwRationalRowAttachment
