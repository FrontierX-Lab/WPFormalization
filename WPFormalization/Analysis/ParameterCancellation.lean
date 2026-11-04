import WPFormalization.Analysis.ParameterHadamard
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma analytic_parameter_coordinate_cancel (G H:E × ℂ → ℂ)
    (hG:AnalyticAt ℂ G 0) (hH:AnalyticAt ℂ H 0)
    (hmul:∀ᶠv:E × ℂ in 𝓝 0,v.2*G v=v.2*H v):
    G=ᶠ[𝓝 0] H:=by
  have hp:∀ᶠv:E × ℂ in 𝓝 0,AnalyticAt ℂ G v∧AnalyticAt ℂ H v∧v.2*G v=v.2*H v:=by
    filter_upwards[hG.eventually_analyticAt,hH.eventually_analyticAt,hmul] with v hgv hhv he
    exact ⟨hgv,hhv,he⟩
  obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp hp
  filter_upwards[Metric.ball_mem_nhds (0:E × ℂ) hr] with v hv
  have hpt:=hball (by simpa only[Metric.mem_ball,dist_zero_right] using hv)
  by_cases hz:v.2=0
  · have he_v:(v.1,(0:ℂ))=v:=Prod.ext rfl hz.symm
    have hcv:ContinuousAt (fun u:ℂ=>(v.1,u)) 0:=
      (continuous_const.prodMk continuous_id).continuousAt
    have ht:Tendsto (fun u:ℂ=>(v.1,u)) (𝓝 0) (𝓝 v):=by simpa only[he_v] using hcv.tendsto
    have hmem:∀ᶠu:ℂ in 𝓝 0,(v.1,u)∈Metric.ball (0:E × ℂ) r:=
      ht.eventually (Metric.isOpen_ball.mem_nhds hv)
    have hgv:ContinuousAt (fun u:ℂ=>G (v.1,u)) 0:=by
      have hh:ContinuousAt G (v.1,(0:ℂ)):=by rw[he_v];exact hpt.1.continuousAt
      exact hh.comp (f:=fun u:ℂ=>(v.1,u)) hcv
    have hhv:ContinuousAt (fun u:ℂ=>H (v.1,u)) 0:=by
      have hh:ContinuousAt H (v.1,(0:ℂ)):=by rw[he_v];exact hpt.2.1.continuousAt
      exact hh.comp (f:=fun u:ℂ=>(v.1,u)) hcv
    have heq:(fun u:ℂ=>G (v.1,u))=ᶠ[𝓝[≠] (0:ℂ)] (fun u:ℂ=>H (v.1,u)):=by
      filter_upwards[hmem.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with u hu hune
      have huneq:u≠0:=by simpa only[mem_compl_iff,mem_singleton_iff] using hune
      have hp':=hball (by simpa only[Metric.mem_ball,dist_zero_right] using hu)
      exact mul_left_cancel₀ huneq hp'.2.2
    have hres:=tendsto_nhds_unique_of_eventuallyEq
      (hgv.tendsto.mono_left nhdsWithin_le_nhds)
      (hhv.tendsto.mono_left nhdsWithin_le_nhds) heq
    simpa only[he_v] using hres
  · exact mul_left_cancel₀ hz hpt.2.2
end WP.Analysis
