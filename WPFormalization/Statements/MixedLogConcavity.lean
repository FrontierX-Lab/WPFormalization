import WPFormalization.Coefficients.MixedLogConcavityProof
noncomputable section
namespace WP
open Filter
open scoped Topology

/- Blueprint label(s): eq:C7
Paper v3: 13.7 [PDF 53]
Status: CONDITIONALLY_PROVED; PsiTheory and classical INT-NEF remain
-/
@[blueprint "eq:C7"]
theorem mixed_log_concavity (P : PsiTheory) (g k : ℕ) (hg : 1 ≤ g)
    (hk : 1 ≤ k) (ht : k < 3*g-2) :
    mixedJ P g (k-1)*mixedJ P g (k+1) ≤ mixedJ P g k^2 := by
  exact mixed_log_concavity_proof P g k hg hk ht

end WP
