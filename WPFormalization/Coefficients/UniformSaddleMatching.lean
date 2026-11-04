import WPFormalization.Coefficients.UniformSaddleMeanBounds
import WPFormalization.Coefficients.UniformSaddleLogAction
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Matching. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma kernelComplexMean_real (z:ℝ):kernelComplexMean (z:ℂ)=(unscaledMean z:ℂ):=by
  apply Complex.ext
  · simpa only[Complex.ofReal_re] using kernelComplexMean_re z
  · simp only[kernelComplexMean,Complex.mul_im,Complex.ofReal_im,zero_mul,zero_add,
      kernelLogSlope_real,Complex.ofReal_im,mul_zero]
lemma analytic_saddle_matches_saddleZeta (R:ℝ)(hR:0<R)(S xco:ℂ→ℂ)
    (hSd:∀w∈Metric.ball (0:ℂ) R,HasDerivAt S (kernelLogSlope w) w)
    (hxco:AnalyticAt ℂ xco 0)(hx0:xco 0=0)
    (hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν):
    ∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),xco (ν:ℂ)=(saddleZeta ν:ℂ):=by
  have ha:AnalyticAt ℂ kernelComplexMean 0:=
    analyticAt_id.mul ((((H_differentiable 0).analyticAt 0).deriv.neg).div
      ((H_differentiable 0).analyticAt 0) (by rw[H_zero,Analysis.derivX_zero];norm_num))
  have hn:deriv kernelComplexMean 0≠0:=by rw[kernelComplexMean_deriv_zero];norm_num
  let I:=ha.hasStrictDerivAt.localInverse kernelComplexMean (deriv kernelComplexMean 0) 0 hn
  have hleft:∀ᶠz:ℂ in 𝓝 0,I (kernelComplexMean z)=z:=ha.hasStrictDerivAt.eventually_left_inverse hn
  have ht:Tendsto (fun ν:ℝ=>(ν:ℂ)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℂ)):=by
    have he:=Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
    simpa only[Complex.ofReal_zero] using he.mono_left nhdsWithin_le_nhds
  have htc:Tendsto (fun ν:ℝ=>xco (ν:ℂ)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℂ)):=by
    simpa only[Function.comp_def,hx0] using hxco.continuousAt.tendsto.comp ht
  have htζ:Tendsto (fun ν:ℝ=>(saddleZeta ν:ℂ)) (𝓝[≥] (0:ℝ)) (𝓝 (0:ℂ)):=by
    have he:=Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ)) |>.comp saddleZeta_tendsto_zero_right
    simpa only[Function.comp_def,Complex.ofReal_zero] using he
  filter_upwards[htc.eventually hleft,htζ.eventually hleft,ht.eventually hsaddle,
    htc.eventually (Metric.ball_mem_nhds (0:ℂ) hR),self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num:(0:ℝ)<3/2)).filter_mono nhdsWithin_le_nhds] with ν hc hζ hs hx hν0 hνU
  have hμ:unscaledMean (saddleZeta ν)=ν:=(saddleZeta_spec ν ⟨hν0,hνU.le⟩).2
  have hκ:kernelComplexMean (xco (ν:ℂ))=(ν:ℂ):=by
    unfold kernelComplexMean
    rw[←(hSd _ hx).deriv]
    exact hs
  rw[hκ] at hc
  rw[kernelComplexMean_real,hμ] at hζ
  exact hc.symm.trans hζ
end WP.Coefficients
