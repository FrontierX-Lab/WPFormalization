import WPFormalization.Volumes.CriticalMorseForward
/-! Common ordinary fibers of the already constructed joint critical Morse coordinates. The actual inverse identities are first restricted to a common polydisk; no joint germ is incorrectly specialized at a nonzero parameter. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.exists_morse_fibers (d:CriticalGaussianCoordinateData) :
    ∃(W:ℂ × ℂ→ℂ)(R C:ℝ),0<R ∧ 0<C ∧ ∀δ:ℂ,‖δ‖<R→
      AnalyticAt ℂ (fun u:ℂ=>d.U (δ,u)) 0 ∧
      AnalyticAt ℂ (fun u:ℂ=>W (δ,u)) 0 ∧ d.U (δ,0)=0 ∧
      (∀ᶠu:ℂ in 𝓝 0,d.U (δ,W (δ,u))=u ∧
        d.kernel.centeredPhase d.L d.q (δ,d.U (δ,u))=-u^2/2) ∧
      ∀u:ℂ,‖u‖<R→‖W (δ,u)-u‖≤C*‖u‖^2 := by
  obtain ⟨W,hW,hW0,hWa,hWd,hUW,hWU,hphase,Rc,C,hRc,hC,hclose⟩:=d.exists_forward_morse_coordinate
  obtain ⟨Rn,hRn,hL,hq,hU,haxis,hfold,hphysical⟩:=d.common_neighborhood
  have hnear:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ W z ∧ d.U (z.1,W z)=z.2 := by
    filter_upwards[hW.eventually_analyticAt,hUW] with z hw he
    exact ⟨hw,he⟩
  obtain ⟨Rw,hRw,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  let R:ℝ:=min Rn (min Rw Rc)
  have hR:0<R:=lt_min hRn (lt_min hRw hRc)
  have hRRn:R≤Rn:=min_le_left _ _
  have hRRw:R≤Rw:=(min_le_right _ _).trans (min_le_left _ _)
  have hRRc:R≤Rc:=(min_le_right _ _).trans (min_le_right _ _)
  have hwgood(δ u:ℂ)(hδ:‖δ‖<R)(hu:‖u‖<R):AnalyticAt ℂ W (δ,u) ∧ d.U (δ,W (δ,u))=u := by
    apply hball (y:=(δ,u))
    change dist (δ,u) (0:ℂ × ℂ)<Rw
    rw[dist_zero_right,Prod.norm_def,max_lt_iff]
    exact ⟨hδ.trans_le hRRw,hu.trans_le hRRw⟩
  refine ⟨W,R,C,hR,hC,?_⟩
  intro δ hδ
  have hδn:‖δ‖<Rn:=hδ.trans_le hRRn
  have hzero:‖(0:ℂ)‖<R:=by simpa using hR
  have hUn:AnalyticAt ℂ d.U (δ,0):=hU _ ⟨by simpa only[Metric.mem_ball,dist_zero_right] using hδn,
    by simpa only[Metric.mem_ball,dist_zero_right] using hzero.trans_le hRRn⟩
  refine ⟨hUn.curry_right,(hwgood δ 0 hδ hzero).1.curry_right,(haxis δ hδn).2,?_,?_⟩
  · have hn:∀ᶠu:ℂ in 𝓝 0,u∈Metric.ball 0 R:=Metric.ball_mem_nhds 0 hR
    filter_upwards[hn] with u hu
    have huR:‖u‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hu
    exact ⟨(hwgood δ u hδ huR).2,(hfold δ u hδn (huR.trans_le hRRn)).2⟩
  · intro u hu
    exact hclose δ u (hδ.trans_le hRRc) (hu.trans_le hRRc)
end WP.Analysis
