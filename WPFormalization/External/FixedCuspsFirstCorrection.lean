import WPFormalization.External.FixedCusps
/-! The classical fixed-n=0 first correction, with an UNKNOWN normalization.

Mirzakhani--Zograf, GAFA 25 (2015), Theorem 1.2 and Remark 1.3,
arXiv:1112.1151, PDF pp.1--2, gives c_0^(1)=7/12-17/(6*pi^2).
The displayed convergence is a weaker consequence of its fixed-order error.
The normalization c here is sqrt(pi) times their unknown positive constant;
its value is not assumed. No cusp-uniformity or growing-order error is given.

As for fixed_cusps_universal_leading, the deferred transfer to an arbitrary
PsiTheory includes classical DVV uniqueness and KMZ/Wolpert normalization.
The actual geometric instance is not supplied. This classical input is used
only for the sharp lower bound in Theorem 11.1, not for the new all-order
unmarked expansion or Theorems 8.2/10.2/1.1.
-/
noncomputable section
namespace WP.External
open Filter
open scoped Topology

theorem fixed_zero_cusps_first_correction (P : PsiTheory) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun g : ℕ => (g : ℝ) *
        (volumeModel P g 0 /
          ((2*g-3).factorial*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g)) / c - 1))
        atTop (𝓝 (7/12-17/(6*Real.pi^2))) := by
  sorry
end WP.External
