import WPFieldAssembly.SourceClosureUVFieldTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureUVCanonicalHoles WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVFieldTransport

namespace WPFieldAssembly.SourceClosureUVSupport

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

theorem above_T (j : ℤ) : Above (T j : K[T;T⁻¹]) j := by
  simpa only [map_one,one_mul] using Above_monomial (1 : K) j

theorem above_add_same (b : ℤ) (F G : K[T;T⁻¹])
    (hF : Above F b) (hG : Above G b) : Above (F+G) b := by
  simpa only [max_self] using Above_add hF hG

theorem above_sub_same (b : ℤ) (F G : K[T;T⁻¹])
    (hF : Above F b) (hG : Above G b) : Above (F-G) b := by
  simpa only [max_self] using Above_sub hF hG

/-- The whole shifted finite log retains both cutoff ends before taking a bound. -/
theorem log_phase_bounds (p : ℕ) (hp : 0<p) (c : K) (F : K[T;T⁻¹])
    (hF : ∀ j : ℤ, j≤0 ∨ (p : ℤ)≤j → F.coeff j=0) :
    Above ((T (-(p : ℤ))-LaurentPolynomial.C c)*F) ((p : ℤ)-1) ∧
      Above (invert ((T (-(p : ℤ))-LaurentPolynomial.C c)*F)) ((p : ℤ)-1) := by
  have hf : Above F ((p : ℤ)-1) := by
    intro j hj
    exact hF j (Or.inr (by omega))
  have hfi : Above (invert F) (-1) := by
    intro j hj
    rw [invert_apply]
    exact hF (-j) (Or.inl (by omega))
  have hphase : Above (T (-(p : ℤ))-LaurentPolynomial.C c : K[T;T⁻¹]) 0 :=
    above_sub_same 0 _ _ (Above_mono (above_T _) (by omega)) (Above_C c)
  have hiphase : Above (T (p : ℤ)-LaurentPolynomial.C c : K[T;T⁻¹]) (p : ℤ) :=
    above_sub_same _ _ _ (above_T _) (Above_mono (Above_C c) (by omega))
  constructor
  · simpa only [zero_add] using Above_mul hphase hf
  · simpa only [map_mul,map_sub,invert_T,neg_neg,invert_C,
      show (p : ℤ) + (-1) = (p : ℤ) - 1 by omega] using
      Above_mul hiphase hfi

theorem originalJab_bounds (p : ℕ) [Fact p.Prime] :
    Above (originalJa p+originalJb p : K[T;T⁻¹]) ((p : ℤ)-1) ∧
      Above (invert (originalJa p+originalJb p : K[T;T⁻¹])) ((p : ℤ)-1) := by
  have ha := log_phase_bounds (K:=K) p (Fact.out : p.Prime).pos (1/4 : K)
    (scaledLog p 4) (scaledLog_coeff_outside p 4)
  have hb := log_phase_bounds (K:=K) p (Fact.out : p.Prime).pos (4 : K)
    (scaledLog p (1/4)) (scaledLog_coeff_outside p (1/4))
  have hJa : Above (originalJa p : K[T;T⁻¹]) ((p : ℤ)-1) := by
    simpa only [originalJa,mul_assoc] using
      Above_C_mul ha.1 (2/WPFiniteABSourceTail.epsilon p : K)
  have hJb : Above (originalJb p : K[T;T⁻¹]) ((p : ℤ)-1) := by
    simpa only [originalJb,mul_assoc] using
      Above_C_mul hb.1 (2/WPFiniteABSourceTail.epsilon p : K)
  have hiJa : Above (invert (originalJa p : K[T;T⁻¹])) ((p : ℤ)-1) := by
    simpa only [originalJa,map_mul,invert_C,mul_assoc] using
      Above_C_mul ha.2 (2/WPFiniteABSourceTail.epsilon p : K)
  have hiJb : Above (invert (originalJb p : K[T;T⁻¹])) ((p : ℤ)-1) := by
    simpa only [originalJb,map_mul,invert_C,mul_assoc] using
      Above_C_mul hb.2 (2/WPFiniteABSourceTail.epsilon p : K)
  constructor
  · exact above_add_same _ _ _ hJa hJb
  · simpa only [map_add] using above_add_same _ _ _ hiJa hiJb

theorem originalJlog_bounds (p : ℕ) [Fact p.Prime] :
    Above (originalJlog p : K[T;T⁻¹]) ((p : ℤ)-1) ∧
      Above (invert (originalJlog p : K[T;T⁻¹])) ((p : ℤ)-1) := by
  have ha := log_phase_bounds p (Fact.out : p.Prime).pos (1/4 : K)
    (scaledLog p 4) (scaledLog_coeff_outside p 4)
  have hb := log_phase_bounds p (Fact.out : p.Prime).pos (4 : K)
    (scaledLog p (1/4)) (scaledLog_coeff_outside p (1/4))
  constructor
  · exact Above_C_mul (above_sub_same _ _ _ ha.1 hb.1) _
  · simpa only [originalJlog,map_mul,map_sub,invert_C] using
      Above_C_mul (above_sub_same _ _ _ ha.2 hb.2) (2/15 : K)

theorem originalJ2log_bounds (p : ℕ) [Fact p.Prime] :
    Above (originalJ2log p : K[T;T⁻¹]) ((p : ℤ)-1) ∧
      Above (invert (originalJ2log p : K[T;T⁻¹])) ((p : ℤ)-1) := by
  have ha := log_phase_bounds p (Fact.out : p.Prime).pos (1/4 : K)
    (scaledDilog p 4) (scaledDilog_coeff_outside p 4)
  have hb := log_phase_bounds p (Fact.out : p.Prime).pos (4 : K)
    (scaledDilog p (1/4)) (scaledDilog_coeff_outside p (1/4))
  constructor
  · exact Above_C_mul (above_sub_same _ _ _ ha.1 hb.1) _
  · simpa only [originalJ2log,map_mul,map_sub,invert_C] using
      Above_C_mul (above_sub_same _ _ _ ha.2 hb.2) (2/15 : K)

theorem originalK0_bound (p : ℕ) : Above (originalK0 p : K[T;T⁻¹]) (p : ℤ) := by
  have ht := above_add_same (p : ℤ) (T (p : ℤ) : K[T;T⁻¹]) (T (-(p : ℤ)))
    (above_T _) (Above_mono (above_T _) (by omega))
  exact above_sub_same (p : ℤ)
    (LaurentPolynomial.C (17/(2*WPFiniteABSourceTail.epsilon p) : K))
    (LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
      (T (p : ℤ)+T (-(p : ℤ))))
    (Above_mono (Above_C (17/(2*WPFiniteABSourceTail.epsilon p) : K)) (by omega))
    (Above_C_mul ht (2/WPFiniteABSourceTail.epsilon p : K))

theorem originalK0_reflection (p : ℕ) : invert (originalK0 p : K[T;T⁻¹])=originalK0 p := by
  simp only [originalK0,map_sub,map_mul,map_add,invert_C,invert_T,neg_neg]
  ring

theorem originalHsym_bound (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    Above (originalHsym p : K[T;T⁻¹]) (((p-1)/2-1 : ℕ) : ℤ) := by
  let b : ℤ := (((p-1)/2-1 : ℕ) : ℤ)
  have hd := originalH_degree (K:=K) p hp
  have hx := Above_toLaurent _ _ hd.1
  have ha := Above_toLaurent _ _ hd.2.1
  have hb := Above_toLaurent _ _ hd.2.2.1
  have hm := Above_toLaurent _ _ hd.2.2.2
  have hi (P : K[X]) : Above (invert P.toLaurent) b :=
    Above_mono (Above_invert_toLaurent P) (by dsimp only [b]; omega)
  exact above_sub_same b _ _
    (above_sub_same b _ _ (above_sub_same b _ _ (above_sub_same b _ _
      (above_sub_same b _ _ (above_add_same b _ _ hx (hi _)) ha) hb) (hi _)) (hi _))
    (Above_C_mul (above_add_same b _ _ hm (hi _)) (1/2 : K))

/-- The actual whole Ucan bound comes from its original primitives and full log phases. -/
theorem descendedUcan_bounds (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    Above (descendedUcan p : K[T;T⁻¹]) (3*(((p-1)/2 : ℕ) : ℤ)) ∧
      Above (invert (descendedUcan p : K[T;T⁻¹])) (3*(((p-1)/2 : ℕ) : ℤ)) := by
  let b : ℤ := 3*(((p-1)/2 : ℕ) : ℤ)
  have hn := WPFiniteWSource.half_exponent p hp
  have hmain : Above (originalK0 p*originalHsym p : K[T;T⁻¹]) b :=
    Above_mono (Above_mul (originalK0_bound p) (originalHsym_bound p hp))
      (by dsimp only [b]; omega)
  have hj := originalJab_bounds (K:=K) p
  have h2 := originalJ2log_bounds (K:=K) p
  have hlog : Above (LaurentPolynomial.C (descendedZE p : K)*
      (originalJa p+originalJb p)) b :=
    Above_mono (Above_C_mul hj.1 (descendedZE p : K)) (by dsimp only [b]; omega)
  have hdilog : Above (LaurentPolynomial.C (1/2 : K)*originalJ2log p) b :=
    Above_mono (Above_C_mul h2.1 (1/2 : K)) (by dsimp only [b]; omega)
  have hilog : Above (LaurentPolynomial.C (descendedZE p : K)*
      invert (originalJa p+originalJb p)) b :=
    Above_mono (Above_C_mul hj.2 (descendedZE p : K)) (by dsimp only [b]; omega)
  have hidilog : Above (LaurentPolynomial.C (1/2 : K)*invert (originalJ2log p)) b :=
    Above_mono (Above_C_mul h2.2 (1/2 : K)) (by dsimp only [b]; omega)
  constructor
  · exact above_sub_same b _ _ (above_sub_same b _ _ hmain hlog) hdilog
  · simpa only [descendedUcan,map_sub,map_mul,invert_C,originalK0_reflection,
      originalHsym_symmetric] using
      above_sub_same b _ _ (above_sub_same b _ _ hmain hilog) hidilog

theorem descendedU_bounds (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    Above (descendedU p : K[T;T⁻¹]) (3*(((p-1)/2 : ℕ) : ℤ)) ∧
      Above (invert (descendedU p : K[T;T⁻¹])) (3*(((p-1)/2 : ℕ) : ℤ)) := by
  have hu := descendedUcan_bounds (K:=K) p hp
  have hc := Above_mono (Above_C (descendedU0 p : K)) (by omega : 0≤3*(((p-1)/2 : ℕ) : ℤ))
  constructor
  · exact above_sub_same _ _ _ hu.1 hc
  · simpa only [descendedU,map_sub,invert_C] using above_sub_same _ _ _ hu.2 hc

/-- Invisible phases are bounded but never deleted. -/
theorem descendedInvisibleP_bounds (p : ℕ) [Fact p.Prime] [CharP K p] :
    Above (descendedInvisibleP p : K[T;T⁻¹]) (p : ℤ) ∧
      Above (invert (descendedInvisibleP p : K[T;T⁻¹])) (p : ℤ) := by
  have h (a b c : K) : Above (LaurentPolynomial.C a*T (p : ℤ)+
      LaurentPolynomial.C b+LaurentPolynomial.C c*T (-(p : ℤ))) (p : ℤ) :=
    above_add_same _ _ _ (above_add_same _ _ _ (Above_monomial a _)
      (Above_mono (Above_C b) (by omega)))
      (Above_mono (Above_monomial c _) (by omega))
  constructor
  · exact h _ _ _
  · simp only [descendedInvisibleP,map_add,map_mul,invert_C,invert_T,neg_neg]
    have he := h (4*(WPFiniteNC122.q p-descendedC p)/15)
      (17*descendedC p/15) (-4*(WPFiniteNC122.q p+descendedC p)/15)
    convert he using 1
    ring

theorem descendedP_bounds (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    Above (descendedP p : K[T;T⁻¹]) (3*(((p-1)/2 : ℕ) : ℤ)) ∧
      Above (invert (descendedP p : K[T;T⁻¹])) (p : ℤ) := by
  have hn := WPFiniteWSource.half_exponent p hp
  have hw := Above_toLaurent (WPFiniteWSource.W p : K[X]) _ (WPFiniteWSource.W_degree p hp)
  have hm := Above_mono (Above_mul (originalK0_bound p) hw)
    (by omega : (p : ℤ)+(((p-1)/2-1 : ℕ) : ℤ)≤3*(((p-1)/2 : ℕ) : ℤ))
  have hmi := Above_mul (originalK0_bound (K:=K) p)
    (Above_invert_toLaurent (WPFiniteWSource.W p : K[X]))
  have hj := originalJlog_bounds (K:=K) p
  have hi := descendedInvisibleP_bounds (K:=K) p
  constructor
  · exact above_add_same _ _ _ (above_add_same _ _ _ hm (Above_mono hj.1 (by omega)))
      (Above_mono hi.1 (by omega))
  · simpa only [descendedP,map_add,map_mul,originalK0_reflection,add_zero] using
      above_add_same (p : ℤ) _ _ (above_add_same (p : ℤ) _ _ hmi
        (Above_mono hj.2 (by omega))) hi.2

end WPFieldAssembly.SourceClosureUVSupport
