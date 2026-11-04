import Mathlib
/-! A continuous complex extension of a real left-endpoint trace realizes the original one-sided limUnder value. Both real and imaginary parts are justified by filter limit uniqueness. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma delta_extension_limit_real_trace (g:ℝ→ℝ) (a:ℝ)
    (F:ℂ→ℂ) (R:ℝ) (hR:0<R) (hF:ContinuousAt F 0)
    (htrace:∀δ∈Ioo (0:ℝ) R,F (δ:ℂ)=(g (a-δ):ℂ)) :
    F 0=((Filter.limUnder (𝓝[<] a) g:ℝ):ℂ) := by
  have hFc:ContinuousAt (fun δ:ℝ=>F (δ:ℂ)) 0:=
    ContinuousAt.comp (f:=fun δ:ℝ=>(δ:ℂ)) (g:=F) (x:=(0:ℝ)) hF Complex.continuous_ofReal.continuousAt
  have hFr:ContinuousAt (fun δ:ℝ=>(F (δ:ℂ)).re) 0 :=
    ContinuousAt.comp (f:=fun δ:ℝ=>F (δ:ℂ)) (g:=Complex.re) (x:=(0:ℝ)) Complex.continuous_re.continuousAt hFc
  have hFi:ContinuousAt (fun δ:ℝ=>(F (δ:ℂ)).im) 0 :=
    ContinuousAt.comp (f:=fun δ:ℝ=>F (δ:ℂ)) (g:=Complex.im) (x:=(0:ℝ)) Complex.continuous_im.continuousAt hFc
  have hδlim:Tendsto (fun Y:ℝ=>a-Y) (𝓝[<] a) (𝓝 (0:ℝ)) := by
    have hh:ContinuousAt (fun Y:ℝ=>a-Y) a:=by fun_prop
    simpa only[sub_self] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hlim:Tendsto (fun Y:ℝ=>(F ((a-Y:ℝ):ℂ)).re) (𝓝[<] a) (𝓝 ((F 0).re)):=hFr.tendsto.comp hδlim
  have hδupper:∀ᶠY:ℝ in 𝓝[<] a,a-Y<R:=hδlim.eventually (eventually_lt_nhds hR)
  have he:∀ᶠY:ℝ in 𝓝[<] a,(F ((a-Y:ℝ):ℂ)).re=g Y := by
    filter_upwards[hδupper,self_mem_nhdsWithin] with Y hY hlt
    have hd:a-Y∈Ioo (0:ℝ) R:=⟨by exact sub_pos.mpr hlt,hY⟩
    have ht:=congrArg Complex.re (htrace (a-Y) hd)
    simpa only[sub_sub_cancel,Complex.ofReal_re] using ht
  have hcrit:Filter.limUnder (𝓝[<] a) g=(F 0).re := by
    exact (hlim.congr' he).limUnder_eq
  have him:∀ᶠδ:ℝ in 𝓝[>] 0,(F (δ:ℂ)).im=0 := by
    have hupper:∀ᶠδ:ℝ in 𝓝[>] 0,δ<R:=
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
    filter_upwards[hupper,self_mem_nhdsWithin] with δ hδ hp
    rw[htrace δ ⟨hp,hδ⟩]
    simp
  have him0:(F 0).im=0 := by
    have ht:Tendsto (fun δ:ℝ=>(F (δ:ℂ)).im) (𝓝[>] 0) (𝓝 ((F 0).im)):=hFi.tendsto.mono_left nhdsWithin_le_nhds
    have hz:Tendsto (fun δ:ℝ=>(F (δ:ℂ)).im) (𝓝[>] 0) (𝓝 (0:ℝ)):=
      tendsto_const_nhds.congr' (by filter_upwards[him] with δ he;exact he.symm)
    exact tendsto_nhds_unique ht hz
  apply Complex.ext
  · simpa only[Complex.ofReal_re] using hcrit.symm
  · simpa only[Complex.ofReal_im] using him0
end WP.Analysis
