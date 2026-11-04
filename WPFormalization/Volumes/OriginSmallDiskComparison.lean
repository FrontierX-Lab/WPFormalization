import WPFormalization.Volumes.OriginFiniteModel
import WPFormalization.Analysis.SmallDiskComparison
/-! Actual D.7 comparison on the shrinking origin disk. The same square-root
optimal truncation of the original canonical marked hierarchy is used throughout.
The conclusion compares the true marked EGF, normalized by its original zero
model scale, with the actual phase/amplitude finite model at exponential precision.
This does not yet assert the normalized coefficient extraction on the Q scale. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma origin_small_disk_model_comparison (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(κ d a C H ρ:ℝ),
      0<κ ∧ 0<d ∧ 0<a ∧ 0<C ∧ 0<H ∧ 0<ρ ∧ ρ<xCritical ∧
      S 0=0 ∧ Bc 0=1 ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀z:ℂ,‖z‖≤d/(4*Real.sqrt (complexity g p))→
        ‖normalizedMarkedGenerating P g p z-
          normalizedFiniteMarkedModel P g p S Bc L ⌊κ*Real.sqrt (complexity g p)⌋₊ z‖≤
            C*Real.exp (-a*Real.sqrt (complexity g p)):=by
  obtain ⟨S,Bc,L,κ,a,H₀,ρ,D,E,hκ,ha,hH₀,hρ,hρx,hD,hE,hS0,hBc0,hLr,hSR,hdata⟩:=
    origin_normalized_model_data P p hp
  let d:ℝ:=min (ρ/18) (a/(36*D))
  let H:ℝ:=max H₀ 1
  have hd:0<d:=lt_min (by positivity) (by positivity)
  have hdr:d≤ρ/18:=min_le_left _ _
  have hda:36*D*d≤a:=by
    have ht:=(le_div_iff₀ (by positivity:0<36*D)).mp (min_le_right (ρ/18) (a/(36*D)))
    dsimp only[d]
    nlinarith
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  refine ⟨S,Bc,L,κ,d,a/4,(E+2)*D,H,ρ,hκ,hd,by positivity,by positivity,hH,hρ,hρx,
    hS0,hBc0,hLr,hSR,?_⟩
  intro g hg z hz
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  have hh1:1≤h:=(le_max_right _ _).trans hg
  have hg₀:H₀≤h:=(le_max_left _ _).trans hg
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *;omega
  have hm:=hdata g hg₀
  have hM:AnalyticOnNhd ℂ (normalizedFiniteMarkedModel P g p S Bc L J) (Metric.ball 0 ρ):=by
    intro w hw
    exact (hm.1 w (show ‖w‖≤ρ from (by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<ρ).le)).1
  exact Analysis.small_disk_comparison_of_real_relative_error
    (normalizedMarkedGenerating P g p) (normalizedFiniteMarkedModel P g p S Bc L J)
    ρ D E a d h hρ hD hE ha hd hdr hda hh1
    (normalizedMarkedGenerating_analytic_disk P g p ρ hρx.le) hM
    (fun w hw=>(hm.1 w hw).2)
    (fun w hw=>normalizedMarkedGenerating_disk_domination P g p hp hs ‖w‖ ⟨norm_nonneg _,hw.trans_lt hρx⟩ w le_rfl)
    hm.2 z hz
end WP.HigherOrder
