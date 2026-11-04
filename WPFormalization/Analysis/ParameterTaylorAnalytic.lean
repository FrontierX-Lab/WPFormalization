import WPFormalization.Volumes.CriticalPhaseCalculus
/-! Jointly analytic Taylor coefficient extraction along the second coordinate.
Repeated partial derivatives agree with actual one-variable iterated derivatives;
restriction to the parameter axis preserves the original analytic neighborhood. -/
noncomputable section
open Filter
open scoped Topology
namespace WP.Analysis
lemma sndPartial_iterate_analyticAt (F:ℂ × ℂ → ℂ) (n:ℕ) (z:ℂ × ℂ)
    (hF:AnalyticAt ℂ F z) : AnalyticAt ℂ ((sndPartial^[n]) F) z := by
  induction n with
  | zero=>exact hF
  | succ n ih=>
    rw [Function.iterate_succ_apply']
    exact sndPartial_analytic _ _ ih
lemma sndPartial_iterate_eq_iteratedDeriv (F:ℂ × ℂ → ℂ) (n:ℕ) (z:ℂ × ℂ)
    (hF:AnalyticAt ℂ F z) :
    ((sndPartial^[n]) F) z=iteratedDeriv n (fun u:ℂ=>F (z.1,u)) z.2 := by
  induction n generalizing z with
  | zero=>rfl
  | succ n ih=>
    rw [Function.iterate_succ_apply',sndPartial_eq_deriv _ _ (sndPartial_iterate_analyticAt F n z hF)]
    have hc : ContinuousAt (fun u:ℂ=>(z.1,u)) z.2 := by fun_prop
    have he:(fun u:ℂ=>((sndPartial^[n]) F) (z.1,u))=ᶠ[𝓝 z.2]
        (fun u:ℂ=>iteratedDeriv n (fun v:ℂ=>F (z.1,v)) u) := by
      filter_upwards [hc.tendsto.eventually hF.eventually_analyticAt] with u hu
      exact ih (z.1,u) hu
    rw [he.deriv_eq,iteratedDeriv_succ]

lemma parameter_taylor_coefficient_analyticAt (F:ℂ × ℂ → ℂ) (p:ℂ) (n:ℕ)
    (hF:AnalyticAt ℂ F (p,0)) :
    AnalyticAt ℂ (fun q:ℂ=>WP.coeff (fun u:ℂ=>F (q,u)) n) p := by
  have ha:AnalyticAt ℂ (fun q:ℂ=>((sndPartial^[n]) F) (q,0)/(n.factorial:ℂ)) p :=
    (sndPartial_iterate_analyticAt F n (p,0) hF).curry_left.div_const
  apply ha.congr
  have hc:ContinuousAt (fun q:ℂ=>(q,(0:ℂ))) p := by fun_prop
  filter_upwards [hc.tendsto.eventually hF.eventually_analyticAt] with q hq
  simp only [WP.coeff]
  rw [sndPartial_iterate_eq_iteratedDeriv F n (q,0) hq]
end WP.Analysis
