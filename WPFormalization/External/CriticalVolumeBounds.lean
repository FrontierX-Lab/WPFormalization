import WPFormalization.Statements.Volumes

/-! Classical volume estimates used in Appendix G.

Source: Y. Shen and Y. Wu, *Arbitrarily small spectral gaps for random
hyperbolic surfaces with many cusps*, arXiv:2203.15681v4, Lemmas 18 and 19,
printed pp.12--13. Lemma 18 gives the upper estimate for complexity at
least two. Enlarging its absolute constant includes the two stable
complexity-one types (0,3) and (1,1). Lemma 19, and its finite-product
proof using Mirzakhani--Zograf Theorem 5.1, give the lower estimate
uniformly for n <= A sqrt(g), for each fixed A. Replacing sqrt(g) by
sqrt(2g-2+n) changes only constants on that range.

The exponent d-1 and Gamma(d) are the original WP volume normalization.
These declarations contain neither a cut-count estimate nor a cusp/genus
allocation estimate. Transfer from geometric WP volumes to an arbitrary
PsiTheory uses classical DVV uniqueness and the KMZ/Wolpert normalization;
that transfer is part of the deferred classical proof. An actual geometric
instance of PsiTheory is not constructed here. -/

noncomputable section
namespace WP.External

@[blueprint "ext:shen-wu-volumes"]
theorem shenWu_volume_upper (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, Stable a b →
      volumeModel P a b ≤
        C * (4 * Real.pi ^ 2) ^ (complexity a b - 1) *
          Real.Gamma (complexity a b) / Real.sqrt (complexity a b) := by
  sorry

@[blueprint "ext:shen-wu-volumes"]
theorem shenWu_volume_critical_lower (P : PsiTheory) (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      (n : ℝ) ≤ A * Real.sqrt (g : ℝ) →
      c * (4 * Real.pi ^ 2) ^ (complexity g n - 1) *
          Real.Gamma (complexity g n) / Real.sqrt (complexity g n) ≤
        volumeModel P g n := by
  sorry

end WP.External
