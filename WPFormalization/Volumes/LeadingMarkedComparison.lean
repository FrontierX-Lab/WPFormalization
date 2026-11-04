import WPFormalization.Volumes.RealCenteredMarkedGenerating
import WPFormalization.HigherOrder.MarkedExpansionProof
import WPFormalization.Analysis.SlitDiskComparison
/-! The actual zero-order marked expansion supplies the real relative
errors used in a centered complex comparison. Positive-series domination
and Mathlib Hadamard three-lines transfer these errors to the inner disk.
The analytic leading-model trace and bound are explicit local inputs to
this intermediate lemma, supplied by the actual parameter charts. -/
noncomputable section
namespace WP
open Set
def markedLeadingError (P:PsiTheory)(g p:ℕ)(x:ℝ):ℝ:=
  Real.pi*markedF P g p x/markedModel g p (inverseY x)-1

lemma marked_leading_relative_error (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃C H:ℝ,0<C ∧ 0<H ∧ 2*C≤H ∧ ∀g:ℕ,H≤(complexity g p:ℝ)→
      ∀x∈Ico (0:ℝ) xCritical,|markedLeadingError P g p x|≤C/(complexity g p:ℝ):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,_,he,_,_⟩:=HigherOrder.full_expansion_proof P p hp
  refine ⟨C*B,max H (2*(C*B)),mul_pos hC hB,hH.trans_le (le_max_left _ _),le_max_right _ _,?_⟩
  intro g hg x hx
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x hx).1
  have hz:((0:ℕ):ℝ)≤c*Real.sqrt (complexity g p) :=by simp only[Nat.cast_zero];positivity
  have ht:=he g 0 ((le_max_left _ _).trans hg) hz (inverseY x) hY
  simpa [markedLeadingError,(inverseY_branch x hx).2] using ht

lemma real_centered_marked_leading_identity (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (x μ σ u:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hxu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical):
    realCenteredMarkedGenerating P g p x μ σ (u:ℂ)=
      ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
          markedModel g p (inverseY x):ℝ):ℂ)*
        (((1+markedLeadingError P g p (x*Real.exp (u/σ)))/
          (1+markedLeadingError P g p x):ℝ):ℂ):=by
  rw[realCenteredMarkedGenerating_real P g p hs x μ σ u hx hxu,←Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hf:markedF P g p x≠0:=(markedF_positive_cusp_weight P g p hp hs x hx).ne'
  have hm:markedModel g p (inverseY x)≠0:=
    (markedModel_pos_parameter g p hs _ (inverseY_branch x hx).1).ne'
  have hmt:markedModel g p (inverseY (x*Real.exp (u/σ)))≠0:=
    (markedModel_pos_parameter g p hs _ (inverseY_branch _ hxu).1).ne'
  dsimp only[markedLeadingError]
  have hpineq:Real.pi≠0:=Real.pi_ne_zero
  field_simp
  <;>ring


lemma marked_leading_slit_comparison (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (C:ℝ)(hC:0<C)(hh:0<(complexity g p:ℝ))(hsmall:2*C≤(complexity g p:ℝ))
    (hrel:∀x∈Ico (0:ℝ) xCritical,|markedLeadingError P g p x|≤C/(complexity g p:ℝ))
    (x μ σ r G:ℝ)(hx:x∈Ico (0:ℝ) xCritical)(hr:0<r)(hG:0<G)
    (M:ℂ→ℂ)(hM:AnalyticOnNhd ℂ M (Metric.ball 0 (16*r)))
    (hMb:∀z:ℂ,‖z‖<16*r→‖M z‖≤G)
    (htilt:∀z:ℂ,‖z‖<16*r→x*Real.exp (z.re/σ)∈Ico (0:ℝ) xCritical)
    (htrace:∀u:ℝ,|u|<16*r→M (u:ℂ)=
      ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
        markedModel g p (inverseY x):ℝ):ℂ))
    (w:ℂ)(hw:‖w‖≤3*r/2):
    ‖realCenteredMarkedGenerating P g p x μ σ w-M w‖≤
      4*Real.sqrt (C/(complexity g p:ℝ))*G:=by
  have hε:0<C/(complexity g p:ℝ):=div_pos hC hh
  have hεhalf:C/(complexity g p:ℝ)≤1/2:=(div_le_iff₀ hh).mpr (by linarith)
  apply Analysis.centered_slit_comparison _ M r G (C/(complexity g p:ℝ)) hr hG hε hεhalf
    (realCenteredMarkedGenerating_analytic_disk P g p x μ σ (16*r) hx.1 (fun z hz=>(htilt z hz).2))
    hM hMb
    (fun z hz=>realCenteredMarkedGenerating_norm_domination P g p hp hs x μ σ hx z (htilt z hz))
    (markedLeadingError P g p x:ℂ) _ _ w hw
  · simpa only[Complex.norm_real,Real.norm_eq_abs] using hrel x hx
  · intro u hu
    have huc:‖(u:ℂ)‖<16*r:=by simpa only[Complex.norm_real,Real.norm_eq_abs] using hu
    have hxu:x*Real.exp (u/σ)∈Ico (0:ℝ) xCritical:=by
      simpa only[Complex.ofReal_re] using htilt (u:ℂ) huc
    refine ⟨(markedLeadingError P g p (x*Real.exp (u/σ)):ℂ),?_,?_⟩
    · simpa only[Complex.norm_real,Real.norm_eq_abs] using hrel _ hxu
    · rw[htrace u hu]
      simpa only[Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one] using
        real_centered_marked_leading_identity P g p hp hs x μ σ u hx hxu
end WP
