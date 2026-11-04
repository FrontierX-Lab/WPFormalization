import WPFormalization.Analysis.ComplexGermGluing
/-! A common-radius bounded holomorphic coefficient family pulls back along a genuine analytic parameter map on one neighborhood shared by every order. The real trace event is common to all orders; no countable intersection of neighborhoods is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma bounded_complex_family_local_pullback (a b x : ℝ) (v : ℕ → ℝ → ℂ)
    (F : ℕ → ℂ → ℂ) (q : ℂ → ℂ) (R C B : ℝ) (hR : 0 < R)
    (hF : ∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 R))
    (hbound : ∀ j z, ‖z‖ < R → ‖F j z‖ ≤ C * B^j * (j.factorial : ℝ)^2)
    (hq : AnalyticAt ℂ q (x : ℂ)) (hq0 : q (x : ℂ) = 0)
    (htrace : ∀ᶠ t : ℝ in 𝓝 x, t ∈ Icc a b → ∀ j, F j (q (t : ℂ)) = v j t) :
    ∃ r : ℝ, 0 < r ∧
      (∀ j, AnalyticOnNhd ℂ (fun z => F j (q z)) (Metric.ball (x : ℂ) r)) ∧
      (∀ j t, t ∈ Icc a b → (t : ℂ) ∈ Metric.ball (x : ℂ) r → F j (q (t : ℂ)) = v j t) ∧
      ∀ j z, z ∈ Metric.ball (x : ℂ) r → ‖F j (q z)‖ ≤ C * B^j * (j.factorial : ℝ)^2 := by
  have hsmall : ∀ᶠ z : ℂ in 𝓝 (x : ℂ), ‖q z‖ < R :=
    hq.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by rw [hq0,norm_zero]; exact hR))
  obtain ⟨r1,hr1,hgood⟩ := Metric.eventually_nhds_iff.mp (hq.eventually_analyticAt.and hsmall)
  obtain ⟨r2,hr2,hreal⟩ := Metric.eventually_nhds_iff.mp htrace
  refine ⟨min r1 r2,lt_min hr1 hr2,?_,?_,?_⟩
  · intro j z hz
    have hdist : dist z (x : ℂ) < r1 := hz.trans_le (min_le_left _ _)
    have hstate := hgood hdist
    exact (hF j (q z) (by simpa only [Metric.mem_ball,dist_zero_right] using hstate.2)).comp hstate.1
  · intro j t ht hdist
    have hd : dist t x < min r1 r2 := by
      simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real] using hdist
    exact hreal (hd.trans_le (min_le_right _ _)) ht j
  · intro j z hz
    exact hbound j (q z) (hgood (hz.trans_le (min_le_left _ _))).2
end WP.Analysis
