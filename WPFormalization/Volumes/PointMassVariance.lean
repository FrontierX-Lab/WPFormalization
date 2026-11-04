import WPFormalization.Analysis.PsiAnalyticFactors
noncomputable section
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma eulerPsi_critical_upper :
    ∃ε0:ℝ,0<ε0∧∀ε∈Ioo 0 ε0,
      euler Psi (xCritical*(1-ε))≤2/ε^2:=by
  obtain ⟨r,hr,f₀,f₁,f₂,hf₀,hf₁,hf₂,hf₀0,hf₁0,hf⟩:=Analysis.Psi_critical_analytic_factors
  have ht:Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have hh:ContinuousAt Real.sqrt (0:ℝ):=Real.continuous_sqrt.continuousAt
    simpa only[Real.sqrt_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hb:∀ᶠε:ℝ in 𝓝[>] 0,f₁ (Real.sqrt ε)<2:=by
    have hh:=hf₁.continuousAt.tendsto.comp ht
    rw[hf₁0] at hh
    exact hh.eventually (eventually_lt_nhds (by norm_num))
  have hs:∀ᶠε:ℝ in 𝓝[>] 0,Real.sqrt ε<r:=ht.eventually (eventually_lt_nhds hr)
  have he:∀ᶠε:ℝ in 𝓝[>] 0,euler Psi (xCritical*(1-ε))≤2/ε^2:=by
    filter_upwards[self_mem_nhdsWithin,hb,hs] with ε hε hbound hsmall
    have hh:=(hf (Real.sqrt ε) ⟨Real.sqrt_pos.mpr hε,hsmall⟩).2.1
    have hpow:(Real.sqrt ε)^4=ε^2:=by rw[show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hε.le]
    rw[Real.sq_sqrt hε.le,hpow] at hh
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    linarith
  obtain ⟨ε0,hε0,he⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he)
  refine ⟨ε0,hε0,?_⟩
  intro ε hε
  exact he (by simpa only[Real.dist_eq,sub_zero,abs_of_pos hε.1] using hε.2) hε.1
end WP.PositiveConvolution
