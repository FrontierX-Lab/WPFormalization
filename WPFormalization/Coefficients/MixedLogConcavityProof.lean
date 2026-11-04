import WPFormalization.Geometry.NefMixedIntersection
noncomputable section
namespace WP

lemma mixed_log_concavity_proof (P : PsiTheory) (g k : ℕ) (hg : 1 ≤ g)
    (hk : 1 ≤ k) (ht : k < 3*g-2) :
    mixedJ P g (k-1)*mixedJ P g (k+1) ≤ mixedJ P g k^2 := by
  have hg2 : 2 ≤ g := by omega
  obtain ⟨R⟩ := External.classical_onepoint_nef_realization P g hg2
  exact Geometry.mixed_log_concavity_of_nef_realization P g R k hg hk ht

end WP
