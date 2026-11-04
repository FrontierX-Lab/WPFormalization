import WPFormalization.Marked.UnmarkedReduction

/-! The original unmarked-volume reduction and its exact leading factor. -/
noncomputable section
namespace WP

/- Eq.11.6. h=2g-1; the p=0 correction is kept as the exact finite-genus ratio. -/
/- Blueprint label(s): eq:AV6
Paper v3: 11.6 [PDF 50]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:AV6"]
theorem unmarked_reduction (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    volumeModel P g 0 = volumeModel P g 1 *
      ((complexity g 0 : ℝ)/A 0*W P g 0 0/W P g 1 0)/(4*Real.pi^2*(2*(g : ℝ)-2)) ∧
    leadingVolume g 1/(4*Real.pi^2*(2*(g : ℝ)-2)*leadingVolume g 0) =
      Real.sqrt (1+1/(2*(g : ℝ)-1)) := by
  exact unmarked_reduction_proof P g hg

end WP
