import WPFormalization.Volumes.CriticalTrueComparison
/-! Actual positive generating-function ratios inherit the proved real
relative error through an exact physical model trace. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma actual_centered_real_comparison_from_model_trace (P:PsiTheory)(g p k J:ℕ)
    (hp:1≤p)(hs:Stable g p)(x σ R ε:ℝ)(M:ℂ→ℂ)
    (hx:x∈Ico (0:ℝ) xCritical)(hε:0≤ε)
    (hP:∀Y∈Icc (0:ℝ) y₀,HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y≠0)
    (hrel:∀Y∈Ico (0:ℝ) y₀,
      |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J Y-1|≤ε)
    (htrace:∀u:ℝ,|u|<R→
      let xt:ℝ:=x*Real.exp (u/σ)
      xt∈Ico (0:ℝ) xCritical ∧ M (u:ℂ)=
        Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ))*
          ((markedModel g p (inverseY xt)/markedModel g p (inverseY x)*
            HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY xt)/
              HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x):ℝ):ℂ)):
    let e0:ℂ:=(((Real.pi*markedF P g p x/markedModel g p (inverseY x))/
      HigherOrder.realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x)-1:ℝ):ℂ)
    ‖e0‖≤ε ∧ ∀u:ℝ,|u|<R→∃e:ℂ,‖e‖≤ε ∧
      centeredMarkedGenerating P g p k x σ (u:ℂ)=M (u:ℂ)*((1+e)/(1+e0)):=by
  dsimp only
  let h:ℝ:=complexity g p
  let Y:ℝ:=inverseY x
  have hY:Y∈Ico (0:ℝ) y₀:=(inverseY_branch x hx).1
  have hXY:XR Y=x:=(inverseY_branch x hx).2
  refine ⟨?_,?_⟩
  · have he:=hrel Y hY
    rw[hXY] at he
    simpa only[Complex.norm_real,Real.norm_eq_abs] using he
  · intro u hu
    let xt:ℝ:=x*Real.exp (u/σ)
    have ht:=htrace u hu
    dsimp only at ht
    have hxt:xt∈Ico (0:ℝ) xCritical:=ht.1
    let Yt:ℝ:=inverseY xt
    have hYt:Yt∈Ico (0:ℝ) y₀:=(inverseY_branch xt hxt).1
    let e:ℂ:=(((Real.pi*markedF P g p xt/markedModel g p Yt)/
      HigherOrder.realFiniteMarkedFactor P p h J Yt-1:ℝ):ℂ)
    have heb:‖e‖≤ε:=by
      have he:=hrel Yt hYt
      rw[(inverseY_branch xt hxt).2] at he
      simpa only[e,Complex.norm_real,Real.norm_eq_abs] using he
    refine ⟨e,heb,?_⟩
    have hF0:markedF P g p x≠0:=(markedF_positive_cusp_weight P g p hp hs x hx).ne'
    have hM0:markedModel g p Y≠0:=(markedModel_pos_parameter g p hs Y hY).ne'
    have hMt:markedModel g p Yt≠0:=(markedModel_pos_parameter g p hs Yt hYt).ne'
    have hP0:HigherOrder.realFiniteMarkedFactor P p h J Y≠0:=hP Y ⟨hY.1,hY.2.le⟩
    have hPt:HigherOrder.realFiniteMarkedFactor P p h J Yt≠0:=hP Yt ⟨hYt.1,hYt.2.le⟩
    have heq:=centered_ratio_algebra
      (Complex.exp (-(k:ℂ)*(u:ℂ)/(σ:ℂ)))
      ((Real.pi*markedF P g p xt:ℝ):ℂ) ((Real.pi*markedF P g p x:ℝ):ℂ)
      (markedModel g p Yt:ℂ) (markedModel g p Y:ℂ)
      (HigherOrder.realFiniteMarkedFactor P p h J Yt:ℂ) (HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ)
      (by exact_mod_cast (mul_ne_zero Real.pi_ne_zero hF0))
      (by exact_mod_cast hMt) (by exact_mod_cast hM0) (by exact_mod_cast hPt) (by exact_mod_cast hP0)
    unfold centeredMarkedGenerating
    have htilt:(x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ))=(xt:ℂ):=by
      rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
    rw[htilt,marked_generating_value_real P g p hs xt hxt,marked_generating_value_real P g p hs x hx,ht.2]
    dsimp only[e]
    push_cast at heq ⊢
    have hpi:(Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_ne_zero
    have hf0c:(markedF P g p x:ℂ)≠0:=by exact_mod_cast hF0
    dsimp only[h,Y,Yt] at heq ⊢
    convert heq using 1 <;>field_simp [hpi,hf0c] <;>ring
end WP.Analysis
