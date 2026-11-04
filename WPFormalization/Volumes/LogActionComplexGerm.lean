import WPFormalization.Analysis.RealPrimitiveDerivative
import WPFormalization.Analysis.NormalizedComplexExtension
import WPFormalization.Volumes.PrefactorIntegration
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_log_action_complex_extension_at (η:ℝ) (hη:η∈Ico (0:ℝ) y₀):
    ∃G:ℂ → ℂ,AnalyticAt ℂ G (η:ℂ)∧
      G (η:ℂ)=((Real.log (Z 0)-Real.log (Z η):ℝ):ℂ)∧
      deriv G (η:ℂ)=(((A η*r η)⁻¹:ℝ):ℂ)∧
      ∀ᶠY:ℝ in 𝓝 η,0≤Y→G (Y:ℂ)=((Real.log (Z 0)-Real.log (Z Y):ℝ):ℂ):=by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hKH,hmatch,hunit,hraw,hRcrit,hR'⟩:=
    common_holomorphic_normalized_kernel_data
  have hηc:η∈Icc (0:ℝ) y₀:=⟨hη.1,hη.2.le⟩
  have hηΩ:(η:ℂ)∈Ω:=hcover η hηc
  have hAη:Ahat (η:ℂ)=(A η:ℂ):=(hmatch η hηc).2.1
  have hRη:R (η:ℂ)=(r η:ℂ):=hraw η hη
  have hne:Ahat (η:ℂ)*R (η:ℂ)≠0:=by
    rw[hAη,hRη,←Complex.ofReal_mul]
    exact_mod_cast (mul_pos (marked_A_pos η hηc) (r_pos η hη)).ne'
  let q:ℂ → ℂ:=fun z=>(Ahat z*R z)⁻¹
  have hq:AnalyticAt ℂ q (η:ℂ):=((hA _ hηΩ).mul (hR _ hηΩ)).inv hne
  have hqη:q (η:ℂ)=(((A η*r η)⁻¹:ℝ):ℂ):=by
    dsimp[q]
    rw[hAη,hRη]
    push_cast
    rfl
  obtain ⟨rad,hrad,hball⟩:=Metric.eventually_nhds_iff.mp hq.eventually_analyticAt
  have hqball:AnalyticOnNhd ℂ q (Metric.ball (η:ℂ) rad):=fun z hz=>hball hz
  let b:ℝ:=(η+y₀)/2
  have hb:0<b:=by dsimp[b];linarith[hη.1,y₀_pos]
  have hηb:η<b:=by dsimp[b];linarith[hη.2]
  have hby:b<y₀:=by dsimp[b];linarith[hη.2]
  let f:ℝ → ℝ:=fun Y=>Real.log (Z 0)-Real.log (Z Y)
  have hf:ContinuousOn f (Icc (0:ℝ) b):=
    continuousOn_const.sub (logZ_continuousOn_parameter.mono (by intro Y hY;exact ⟨hY.1,hY.2.trans_lt hby⟩))
  have hdf(Y:ℝ) (hY:Y∈Ioo (0:ℝ) b):HasDerivAt (fun t:ℝ=>(f t:ℂ)) (q (Y:ℂ)) Y:=by
    have hYi:Y∈Ico (0:ℝ) y₀:=⟨hY.1.le,hY.2.trans hby⟩
    have hd:HasDerivAt f ((A Y*r Y)⁻¹) Y:=by
      convert! (hasDerivAt_const Y (Real.log (Z 0))).sub
        (logZ_hasDerivAt_open_parameter Y ⟨hY.1,hYi.2⟩) using 1 <;> simp only[zero_sub,neg_div,neg_neg,one_div]
    have he:q (Y:ℂ)=(((A Y*r Y)⁻¹:ℝ):ℂ):=by
      dsimp[q]
      rw[(hmatch Y ⟨hYi.1,hYi.2.le⟩).2.1,hraw Y hYi]
      push_cast
      rfl
    rw[he]
    exact hd.ofReal_comp
  obtain ⟨G,hG,hGd,hGmatch⟩:=real_primitive_complex_extension_with_derivative_on_ball 0 b hb f hf
    (Metric.ball (η:ℂ) rad) q hqball hdf η ⟨hη.1,hηb.le⟩ rad hrad (by intro z hz;exact hz)
  have hcenter:(η:ℂ)∈Metric.ball (η:ℂ) rad:=Metric.mem_ball_self hrad
  refine ⟨G,hG _ hcenter,hGmatch η ⟨hη.1,hηb.le⟩ hcenter,?_,?_⟩
  · rw[(hGd _ hcenter).deriv,hqη]
  · have hrmem:∀ᶠY:ℝ in 𝓝 η,(Y:ℂ)∈Metric.ball (η:ℂ) rad:=
      (Complex.continuous_ofReal.tendsto η).eventually (Metric.ball_mem_nhds _ hrad)
    filter_upwards[hrmem,eventually_lt_nhds hηb] with Y hYr hYb hY0
    exact hGmatch Y ⟨hY0,hYb.le⟩ hYr
end WP.Analysis
