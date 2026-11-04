import WPFormalization.External.WeilPeterssonGeometry

/-! Classical uniform boundary comparison, only in the missing genus-zero scope.

Sources: Mirzakhani, J. Differential Geom. 94 (2013), printed p.279,
Lemma 3.2(2), equation (3.7); Shen--Wu, arXiv:2203.15681v4, PDF p.11,
Lemma 14(1). Both state the estimate uniformly over stable topological types.
The normalization is V(0,3)=1 and the physical boundary vector is L, so the
exponent is (sum L)/2. All lengths are nonnegative and n>=3 is essential.

The generalized PsiTheory/geometry-family transfer also uses the classical
uniqueness of the normalized DVV/WP intersection theory. That transfer has not
been proved in Lean. The theorem below is a sourced phase-one external input,
not a consequence already established from the local structure fields.
No counting, moment, tail estimate or paper asymptotic is included.
-/
noncomputable section
universe u v
namespace WP.External

/- Mirzakhani's uniform estimate restricted to stable genus zero. -/
theorem wpVolume_genus_zero_boundary_upper (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (n : ℕ) (hn : 3 ≤ n)
    (L : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) :
    wpVolume G 0 n L ≤ Real.exp ((∑ i, L i)/2) * cuspVolume G 0 n := by
  sorry

end WP.External
