import WPFormalization.Statements.Basic

/-! A nonzero continuous value separates the positive zero set from zero. -/
noncomputable section
namespace WP.Analysis
open Filter Set
open scoped Topology

lemma positive_zero_sInf_pos (f : ℝ → ℂ) (hc : ContinuousAt f 0) (h0 : f 0 ≠ 0)
    (hs : {x : ℝ | 0 < x ∧ f x = 0}.Nonempty) :
    0 < sInf {x : ℝ | 0 < x ∧ f x = 0} := by
  obtain ⟨ε,hε,hne⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_ne h0)
  apply lt_of_lt_of_le hε
  apply le_csInf hs
  intro x hx
  by_contra hh
  have hd : dist x 0 < ε := by simpa [Real.dist_eq,abs_of_pos hx.1] using not_le.mp hh
  exact hne hd hx.2

end WP.Analysis
