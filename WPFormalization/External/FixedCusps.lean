import WPFormalization.Statements.Volumes

/-! The classical fixed-cusp leading expansion with an unknown universal constant.

Source: Mirzakhani--Zograf, GAFA 25 (2015), Theorem 1.2 and Remark 1.3,
arXiv:1112.1151, PDF pp.1--2. Taking the first fixed-order expansion gives
this weaker leading estimate. Our scale contains sqrt(pi*g), so its unknown
constant is sqrt(pi) times the constant in that theorem. No value of this
constant, uniformity in the cusp count, or growing-order bound is admitted.

Transfer from geometric WP volumes to an arbitrary PsiTheory uses classical
DVV uniqueness and the KMZ/Wolpert normalization. Those transfers belong to
this deferred external proof; no geometric instance has been constructed.
The new identification of the constant as one remains a paper proof obligation.
-/
noncomputable section
namespace WP.External

theorem fixed_cusps_universal_leading (P : PsiTheory) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      |volumeModel P g n /
        ((2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3)/Real.sqrt (Real.pi*g))-c| ≤ C/g := by
  sorry

end WP.External
