import WPFormalization.Marked.RatioBounds
import WPFormalization.Weighted.ModelValidity
import WPFormalization.Intersection.CriticalComparison
/-! Strict positivity of the actual normalized amplitudes and marked W
functions. The critical pure-intersection lower bound and the genuine
Painleve comparison supply positivity without a logarithmic comparison
hypothesis. -/
noncomputable section
open Set

namespace WP
lemma normalized_pos_valid_nonempty (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1 ≤ d.length) (hs : Stable g d.length) (hd : d.sum ≤ dimension g d.length)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 < normalized P g d Y := by
  have hr : 0 < ratio P g d y₀ := lt_of_lt_of_le (by positivity) (critical_ratio_zero_bounds P g d hs hd).1
  have hm : 0 < model g d y₀ := model_pos g d y₀ hs ⟨y₀_pos.le,le_rfl⟩
  have hn0 : 0 < normalized P g d y₀ := (div_pos_iff_of_pos_right hm).mp hr
  exact hn0.trans_le (normalized_pi_le P g d hn Y hY)

lemma W_pos (P : PsiTheory) (g p : ℕ) (hn : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 < W P g p Y := by
  unfold W
  apply mul_pos (by positivity)
  exact normalized_pos_valid_nonempty P g _ (by simpa using hn) (by simpa using hs)
    (by simp) Y hY

lemma W_nonneg (P : PsiTheory) (g p : ℕ) (hn : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 ≤ W P g p Y := by
  unfold W
  exact mul_nonneg (by positivity) (normalized_nonneg_nonempty P g _ (by simpa using hn) Y hY)

end WP
