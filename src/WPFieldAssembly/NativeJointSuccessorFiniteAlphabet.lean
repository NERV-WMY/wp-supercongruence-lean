import WPFieldAssembly.ActualKwOrderedEndpoints
import WPFiniteLoop
import WPFifthEntropy

namespace WPFieldAssembly.NativeJointSuccessorB2Finite

open ActualKwOrderedEndpoints

variable {K : Type*} [Field K]

/-- The original finite B2 alphabet, stated independently of its whole-trace attachment.
Its G5 letter is the genuine original G carrier, rather than an assigned scalar. -/
noncomputable def finiteB2Alphabet (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  let c := WPFifthEntropy.C p u
  let loop := WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u
  let ke := WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u
  77 * loop / 75 + 22 * ke / 5 - 11 * originalG p (1 / 5) / 30 -
    5056 * q ^ 2 / 375 + 204 * q * r / 25 + 104 * q * k / 25 -
    153 * r * k / 25 - 399 * r ^ 2 / 500 + 3 * k ^ 2 / 4 +
    5434 * q * c / 375 - 341 * r * c / 125 - 319 * c ^ 2 / 75 -
    11 * WPFiniteField.R p (-2) / 15 - 11 * WPFiniteField.R p 16 / 150

end WPFieldAssembly.NativeJointSuccessorB2Finite
