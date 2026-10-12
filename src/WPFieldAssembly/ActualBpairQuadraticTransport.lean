import WPFieldAssembly.ActualBpairQuadraticGreen
import WPFieldAssembly.ScalarFinalSuccessorG2Source

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2400000

/-- The original uncontracted NC123 quadratic block is the evaluated native residue. -/
theorem actual_NC123_quadratic_block (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (c : K) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      (LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*actualZ52 p u+
        LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))+
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (5*WPFiniteNC122.h p/4 : K)*T (p : ℤ)*actualR52 p-
        LaurentPolynomial.C (10*WPFiniteNC122.h p/3 : K)*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))=
      actualNativeG2Residue (K:=K) p := by
  rw [actual_Z52_quadratic_origin p hp u hu c,actual_R52_metric_origin p hp c]
  rfl

/-- The entire original NC123 block has the NC126 value, with every strict tail and metric phase. -/
theorem actual_NC123_quadratic_block_NC126 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (c : K) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      (LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*actualZ52 p u+
        LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))+
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (5*WPFiniteNC122.h p/4 : K)*T (p : ℤ)*actualR52 p-
        LaurentPolynomial.C (10*WPFiniteNC122.h p/3 : K)*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))=
      5*WPFieldAssembly.ActualKwOrderedEndpoints.originalG p (1/5)/12-
        5*WPFiniteField.R p (-2)/6-WPFiniteField.R p 16/20-
        193*(WPFiniteNC122.q p)^2/50-
          9*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/100-
            177*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/800+
              4*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
                11*(WPFifthEntropy.C p u)^2/15-
                  10*WPFiniteNC122.q p*WPFifthEntropy.C p u/3-
                    5*(WPFiniteInversion.integerFermatQuotient p 3 : K)*WPFifthEntropy.C p u/2 := by
  rw [actual_NC123_quadratic_block p hp u hu c,actualNativeG2Residue_full_tails p hp,
    actualNativeG2Tail_NC126 p hp u hu]

/-- The actual pure quadratic block keeps its Dstar correction and the whole original R52 metric. -/
theorem actual_NC123_pure_quadratic_block_NC126 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (c : K) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      (LaurentPolynomial.C (5/24 : K)*T (p : ℤ)*
          ((actualAK p : K[X]).toLaurent^2-(invert (actualAK p : K[X]).toLaurent)^2)+
        LaurentPolynomial.C (1/4 : K)*(4-11*T (p : ℤ))*
          invert (actualAK p : K[X]).toLaurent*Dsym p+
        LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))+
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (5*WPFiniteNC122.h p/4 : K)*T (p : ℤ)*actualR52 p-
        LaurentPolynomial.C (10*WPFiniteNC122.h p/3 : K)*
          (invert (actualAK p : K[X]).toLaurent-LaurentPolynomial.C c)))=
      5*WPFieldAssembly.ActualKwOrderedEndpoints.originalG p (1/5)/12-
        5*WPFiniteField.R p (-2)/6-WPFiniteField.R p 16/20-
        193*(WPFiniteNC122.q p)^2/50-
          9*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/100-
            177*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2/800+
              4*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 5 : K)+
                11*(WPFifthEntropy.C p u)^2/15-
                  10*WPFiniteNC122.q p*WPFifthEntropy.C p u/3-
                    5*(WPFiniteInversion.integerFermatQuotient p 3 : K)*WPFifthEntropy.C p u/2 := by
  rw [←actual_Z52_pure_quadratic_source p hp u hu]
  exact actual_NC123_quadratic_block_NC126 p hp u hu c

end WPFieldAssembly.ActualBpairContraction
