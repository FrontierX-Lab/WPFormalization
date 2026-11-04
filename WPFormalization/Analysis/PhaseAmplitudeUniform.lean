import WPFormalization.Analysis.PoissonPhaseAmplitude
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma phaseAmplitude_eq_mul_unit (Z:ℂ × ℂ → ℂ) (H:ℂ → ℂ) (v:ℂ × ℂ):
    phaseAmplitude Z H v=H (Z v)*phaseAmplitude Z (fun _:ℂ=>1) v:=by
  simp only[phaseAmplitude,one_mul]
  ring
lemma phaseAmplitude_uniform_family (Z:ℂ × ℂ → ℂ) (hZ:AnalyticAt ℂ Z 0)
    (hZ0:Z 0=0) (hU:AnalyticAt ℂ (phaseAmplitude Z (fun _:ℂ=>1)) 0)
    (RH:ℝ) (hRH:0<RH):
    ∃δ C:ℝ,0<δ∧0<C∧∀(H:ℂ → ℂ)(M:ℝ),
      (∀z:ℂ,‖z‖<RH→AnalyticAt ℂ H z∧‖H z‖≤M)→
      AnalyticOnNhd ℂ (phaseAmplitude Z H) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ)∧
      ∀v∈Metric.ball (0:ℂ) δ ×ˢ Metric.ball (0:ℂ) δ,‖phaseAmplitude Z H v‖≤C*M:=by
  let U:ℂ × ℂ → ℂ:=phaseAmplitude Z (fun _:ℂ=>1)
  let C:ℝ:=‖U 0‖+1
  have hC:0<C:=by dsimp[C];positivity
  have hZt:Tendsto Z (𝓝 0) (𝓝 (0:ℂ)):=by simpa only[hZ0] using hZ.continuousAt.tendsto
  have hUb:∀ᶠv:ℂ × ℂ in 𝓝 0,‖U v‖<C:=
    hU.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by dsimp[C,U];linarith))
  have hp:∀ᶠv:ℂ × ℂ in 𝓝 0,AnalyticAt ℂ Z v∧AnalyticAt ℂ U v∧‖Z v‖<RH∧‖U v‖≤C:=by
    filter_upwards[hZ.eventually_analyticAt,hU.eventually_analyticAt,
      hZt.eventually (Metric.ball_mem_nhds (0:ℂ) hRH),hUb] with v hz hu hzm hub
    refine ⟨hz,hu,?_,hub.le⟩
    simpa only[Metric.mem_ball,dist_zero_right] using hzm
  obtain ⟨δ,hδ,hball⟩:=Metric.eventually_nhds_iff.mp hp
  have hP(v:ℂ × ℂ) (hv:v∈Metric.ball (0:ℂ) δ ×ˢ Metric.ball (0:ℂ) δ):=
    hball (by
      have h1:‖v.1‖<δ:=by simpa only[Metric.mem_ball,dist_zero_right] using hv.1
      have h2:‖v.2‖<δ:=by simpa only[Metric.mem_ball,dist_zero_right] using hv.2
      simpa only[dist_zero_right,Prod.norm_def] using max_lt h1 h2)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro H M hH
  constructor
  · intro v hv
    have hlocal:=hP v hv
    have ha:AnalyticAt ℂ (fun p:ℂ × ℂ=>H (Z p)*U p) v:=
      (((hH (Z v) hlocal.2.2.1).1).comp (f:=Z) hlocal.1).mul hlocal.2.1
    convert! ha using 1
    funext p
    exact phaseAmplitude_eq_mul_unit Z H p
  · intro v hv
    have hlocal:=hP v hv
    rw[phaseAmplitude_eq_mul_unit,norm_mul]
    calc
      _≤M*C:=mul_le_mul (hH (Z v) hlocal.2.2.1).2 hlocal.2.2.2 (norm_nonneg _) (by
        exact (norm_nonneg _).trans (hH (Z v) hlocal.2.2.1).2)
      _=C*M:=mul_comm _ _
end WP.Analysis

namespace WP.Analysis
open Set
lemma phaseAmplitude_uniform_gevrey_two_family (Z:ℂ × ℂ → ℂ) (hZ:AnalyticAt ℂ Z 0)
    (hZ0:Z 0=0) (hU:AnalyticAt ℂ (phaseAmplitude Z (fun _:ℂ=>1)) 0)
    (RH CH BH:ℝ) (hRH:0<RH) (hCH:0<CH) (H:ℕ → ℂ → ℂ)
    (hH:∀j z,‖z‖<RH→AnalyticAt ℂ (H j) z∧‖H j z‖≤CH*BH^j*(j.factorial:ℝ)^2):
    ∃δ C:ℝ,0<δ∧0<C∧∀j,
      AnalyticOnNhd ℂ (phaseAmplitude Z (H j)) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ)∧
      ∀v∈Metric.ball (0:ℂ) δ ×ˢ Metric.ball (0:ℂ) δ,
        ‖phaseAmplitude Z (H j) v‖≤C*BH^j*(j.factorial:ℝ)^2:=by
  obtain ⟨δ,C,hδ,hC,hfam⟩:=phaseAmplitude_uniform_family Z hZ hZ0 hU RH hRH
  refine ⟨δ,C*CH,hδ,mul_pos hC hCH,?_⟩
  intro j
  obtain ⟨ha,hb⟩:=hfam (H j) (CH*BH^j*(j.factorial:ℝ)^2) (hH j)
  refine ⟨ha,?_⟩
  intro v hv
  simpa only[mul_assoc] using hb v hv
end WP.Analysis
