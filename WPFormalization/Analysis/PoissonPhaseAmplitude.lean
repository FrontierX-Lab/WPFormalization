import WPFormalization.Statements.PhaseChangeDefinitions
import WPFormalization.Analysis.DiagonalTaylorAnalytic
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma sliceDeriv_analyticAt (Z:ℂ × ℂ → ℂ) (p:ℂ × ℂ) (hZ:AnalyticAt ℂ Z p):
    AnalyticAt ℂ (fun v:ℂ × ℂ=>deriv (fun u:ℂ=>Z (u,v.2)) v.1) p:=by
  apply (firstPartial_analyticAt Z p hZ).congr
  filter_upwards[hZ.eventually_analyticAt] with v hv
  have hc:HasDerivAt (fun u:ℂ=>(u,v.2)) ((1,0):ℂ × ℂ) v.1:=
    (hasDerivAt_id v.1).prodMk (hasDerivAt_const v.1 v.2)
  have hh:=hv.differentiableAt.hasFDerivAt.comp_hasDerivAt v.1 hc
  exact hh.deriv.symm
lemma phaseAmplitude_analyticAt_zero (Z q:ℂ × ℂ → ℂ)
    (hZ:AnalyticAt ℂ Z 0) (hZ0:Z 0=0) (hq:AnalyticAt ℂ q 0) (hq0:q 0≠0)
    (heq:∀ᶠv:ℂ × ℂ in 𝓝 0,phaseQuotient Z v.1 v.2=q v)
    (H:ℂ → ℂ) (hH:AnalyticAt ℂ H 0):
    AnalyticAt ℂ (phaseAmplitude Z H) 0:=by
  have hHZ:AnalyticAt ℂ (fun v:ℂ × ℂ=>H (Z v)) 0:=by
    have hh:AnalyticAt ℂ H (Z 0):=by rw[hZ0];exact hH
    exact hh.comp (f:=Z) hZ
  have hquot:AnalyticAt ℂ (fun v:ℂ × ℂ=>phaseQuotient Z v.1 v.2) 0:=hq.congr (by filter_upwards[heq] with v hv;exact hv.symm)
  have hquot0:phaseQuotient Z (0:ℂ) 0≠0:=by
    have he:phaseQuotient Z (0:ℂ) 0=q 0:=heq.self_of_nhds
    rw[he]
    exact hq0
  exact (hHZ.mul (sliceDeriv_analyticAt Z 0 hZ)).div hquot hquot0
end WP.Analysis
