import WPFormalization.Volumes.VolumeRatiosProof

noncomputable section
namespace WP

/- Theorem 1.3, three rates with one constant, uniform over all cusp counts. -/
/- Blueprint label(s): thm:volume
Paper v3: 1.3 [PDF 7]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "thm:volume"]
theorem volume_ratios (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      (∀ n : ℕ,
        |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n : ℝ)/g)-1| ≤ C/g ∧
        |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g) ∧
      (∀ n : ℕ, 1 ≤ n →
        |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g) := by
  exact volume_ratios_proof P

end WP
