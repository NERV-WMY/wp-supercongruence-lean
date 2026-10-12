import WPFieldAssembly.ActualKwOrderedEndpoints
import WPFiniteLVSource

namespace WPFieldAssembly.SourceClosureWholeTraceCollection

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: this unchanged finite expression is separated only to
   expose its definition to the original B2 arithmetic consumer. The actual
   UV/whole-trace source equations remain in ScalarFinalSuccessorWholeTraceSource.
   No value of an actual source or remaining trace is asserted by this definition. -/

/-- The complete UW18f alphabet remaining after its actual T5 and beta terms are separated. -/
noncomputable def originalUVFiniteRemainder (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  (7/15 : K)*ActualKwOrderedEndpoints.originalG p (1/5)+
    (17/15 : K)*WPFiniteField.R p 4-WPFiniteField.R p 16/25+
    (11/10 : K)*(WPFiniteLoop.D ((p-1)/2) (4/5) 0-
      WPFiniteLoop.D ((p-1)/2) (1/5) 0)+
    (451/75 : K)*q^2+(31/5 : K)*q*r+(9/10 : K)*r^2+
    (51/5 : K)*q*k-(3/2 : K)*r*k+
    ((104/5 : K)*q-(44/5 : K)*k)*WPFifthEntropy.C p u-
    (22/5 : K)*q*(WPFiniteLVSource.evenSquared p).eval (4/5)

end WPFieldAssembly.SourceClosureWholeTraceCollection
