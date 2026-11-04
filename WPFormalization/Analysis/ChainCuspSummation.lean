import WPFormalization.Statements.Basic

/-! Telescoping logarithmic cusp increments with a genuinely uniform error. -/
noncomputable section
namespace WP.Analysis

lemma chain_log_increment_sum (z f : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ j : ℕ, |z (j+1)-z j-f j| ≤ δ) (n : ℕ) :
    |z n-z 0-(∑ j ∈ Finset.range n, f j)| ≤ n*δ := by
  have ht := Finset.sum_range_sub z n
  have he : z n-z 0-(∑ j ∈ Finset.range n, f j) =
      ∑ j ∈ Finset.range n, (z (j+1)-z j-f j) := by
    rw [Finset.sum_sub_distrib,ht]
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    calc
      (∑ j ∈ Finset.range n, |z (j+1)-z j-f j|) ≤
          ∑ _j ∈ Finset.range n, δ := Finset.sum_le_sum (fun j _ => hb j)
      _ = n*δ := by simp)

end WP.Analysis
