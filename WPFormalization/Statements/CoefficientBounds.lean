import WPFormalization.HigherOrder.CoefficientBoundsProof

/-! Original Lemma C.4. The full statement was frozen independently in
CoefficientBoundsTarget before the proof was constructed. It concerns the
actual finite triangular algorithm on one common complex neighborhood, with
constants preceding every order, degree tuple, marking count and parameter.
Arbitrary-path compatibility and actual finite-genus remainders remain
separate obligations of Proposition C.3. -/
noncomputable section
namespace WP

@[blueprint "lem:coefficient-bounds"]
theorem coefficient_bounds (P : PsiTheory) :
    HigherOrder.ComplexCanonical.CanonicalCoefficientBoundsTarget P := by
  exact HigherOrder.ComplexCanonical.canonicalCoefficientBoundsTarget_proof P

end WP
