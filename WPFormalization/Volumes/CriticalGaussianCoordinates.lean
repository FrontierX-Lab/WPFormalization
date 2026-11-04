import WPFormalization.Analysis.JointMorse
import WPFormalization.Volumes.CriticalPhaseCalculus

/-! Actual common critical Gaussian coordinates. The phase and its standardized
angle are constructed from the existing X kernel, A/a/r units, true mean and
variance, and the logarithmic Z unit. The same complex polydisk includes delta=0.
The public existence theorem supplies every field; none is a new external input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
structure CriticalGaussianCoordinateData where
  kernel : CriticalKernelUnits
  L : ℂ→ℂ
  q : ℂ × ℂ→ℂ
  U : ℂ × ℂ→ℂ
  L_analytic : AnalyticAt ℂ L 0
  L_zero : L 0=(((Real.sqrt (5*y₀^2))⁻¹:ℝ):ℂ)
  q_analytic : AnalyticAt ℂ q (0,0)
  q_zero : q (0,0)=1
  q_axis : ∀ᶠδ:ℂ in 𝓝 0,q (δ,0)=1
  q_fold : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
    X ((y₀:ℂ)-p.1*q p)=X ((y₀:ℂ)-p.1)*Complex.exp (Complex.I*p.2*p.1^2*L p.1)
  physical_normalization : ∀ᶠδ:ℝ in 𝓝 0,0<δ→
    (δ:ℂ)^2*L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ) ∧
    kernel.psiUnit (δ:ℂ)*L (δ:ℂ)=((Psi (XR (y₀-δ))/Real.sqrt (euler Psi (XR (y₀-δ))):ℝ):ℂ)
  U_analytic : AnalyticAt ℂ U (0,0)
  U_zero : U (0,0)=0
  U_axis : ∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0
  U_deriv : deriv (fun w:ℂ=>U (0,w)) 0=1
  phase_identity : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
    kernel.centeredPhase L q (p.1,U p)=-(p.2)^2/2

lemma exists_criticalGaussianCoordinateData : Nonempty CriticalGaussianCoordinateData := by
  obtain ⟨k⟩ := exists_criticalKernelUnits
  obtain ⟨d⟩ := exists_criticalFoldData
  obtain ⟨L,hL,hL0,hnorm⟩ := k.normalization
  obtain ⟨q,hq,hq0,hqaxis,hfold⟩ := d.joint_relative_inverse L hL
  have hns : ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ) := by
    filter_upwards [hnorm] with δ hδ hpos
    exact (hδ hpos).1
  have hsquare := k.normalization_square L hL hns
  have hjets := k.centeredPhase_jets L q hL hq hq0 hqaxis hfold hsquare
  let F:ℂ × ℂ→ℂ := k.centeredPhase L q
  have hF : AnalyticAt ℂ F (0,0) := k.centeredPhase_analytic L q hL hq hq0
  have haxis : ∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 := by
    filter_upwards [hjets] with δ hδ
    exact hδ.1
  have haxisMap : Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  have hderiv : ∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=0 := by
    filter_upwards [hjets,haxisMap.eventually hF.eventually_analyticAt] with δ hδ hFδ
    rw [←sndPartial_eq_deriv F (δ,0) hFδ]
    exact hδ.2.1
  have hsecond : iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0=-1 := by
    have hc : ContinuousAt (fun u:ℂ=>((0:ℂ),u)) 0 := by fun_prop
    have he : deriv (fun u:ℂ=>F (0,u)) =ᶠ[𝓝 0]
        (fun u:ℂ=>sndPartial F (0,u)) := by
      filter_upwards [hc.tendsto.eventually hF.eventually_analyticAt] with u hu
      exact (sndPartial_eq_deriv F (0,u) hu).symm
    rw [iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
    rw [←sndPartial_eq_deriv (sndPartial F) (0,0) (sndPartial_analytic F (0,0) hF)]
    exact hjets.self_of_nhds.2.2
  obtain ⟨U,hU,hU0,hUaxis,hUderiv,hphase⟩ :=
    exists_joint_normalized_morse_inverse F hF haxis hderiv hsecond
  exact ⟨⟨k,L,q,U,hL,hL0,hq,hq0,hqaxis,hfold,hnorm,hU,hU0,hUaxis,hUderiv,hphase⟩⟩
end WP.Analysis

namespace WP.Analysis
lemma CriticalGaussianCoordinateData.common_neighborhood (d : CriticalGaussianCoordinateData) :
    ∃ ρ:ℝ,0<ρ ∧
      AnalyticOnNhd ℂ d.L (Metric.ball 0 ρ) ∧
      AnalyticOnNhd ℂ d.q (Metric.ball 0 ρ ×ˢ Metric.ball 0 ρ) ∧
      AnalyticOnNhd ℂ d.U (Metric.ball 0 ρ ×ˢ Metric.ball 0 ρ) ∧
      (∀δ:ℂ,‖δ‖<ρ→d.q (δ,0)=1 ∧ d.U (δ,0)=0) ∧
      (∀δ u:ℂ,‖δ‖<ρ→‖u‖<ρ→
        X ((y₀:ℂ)-δ*d.q (δ,u))=X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*u*δ^2*d.L δ) ∧
        d.kernel.centeredPhase d.L d.q (δ,d.U (δ,u))=-u^2/2) ∧
      (∀δ∈Ioo (0:ℝ) ρ,
        (δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ) ∧
        d.kernel.psiUnit (δ:ℂ)*d.L (δ:ℂ)=
          ((Psi (XR (y₀-δ))/Real.sqrt (euler Psi (XR (y₀-δ))):ℝ):ℂ)) := by
  have hf : Tendsto (Prod.fst:ℂ × ℂ→ℂ) (𝓝 (0,0)) (𝓝 (0:ℂ)) := continuous_fst.continuousAt.tendsto
  have hgood : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
      AnalyticAt ℂ d.q p ∧ AnalyticAt ℂ d.U p ∧ AnalyticAt ℂ d.L p.1 ∧
      d.q (p.1,0)=1 ∧ d.U (p.1,0)=0 ∧
      X ((y₀:ℂ)-p.1*d.q p)=X ((y₀:ℂ)-p.1)*Complex.exp (Complex.I*p.2*p.1^2*d.L p.1) ∧
      d.kernel.centeredPhase d.L d.q (p.1,d.U p)=-(p.2)^2/2 := by
    filter_upwards [d.q_analytic.eventually_analyticAt,d.U_analytic.eventually_analyticAt,
      hf.eventually d.L_analytic.eventually_analyticAt,hf.eventually d.q_axis,hf.eventually d.U_axis,
      d.q_fold,d.phase_identity] with p hq hU hL hqa hUa hfold hphase
    exact ⟨hq,hU,hL,hqa,hUa,hfold,hphase⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  obtain ⟨ε,hε,hphysical⟩ := Metric.eventually_nhds_iff.mp d.physical_normalization
  let ρ:ℝ := min r ε
  have hρ : 0<ρ := lt_min hr hε
  have hρr : ρ≤r := min_le_left _ _
  have hρε : ρ≤ε := min_le_right _ _
  have hpoint (δ u:ℂ) (hδ:‖δ‖<ρ) (hu:‖u‖<ρ) :=
    hball (show dist (δ,u) ((0,0):ℂ × ℂ)<r by
      simpa [dist_eq_norm,Prod.norm_def,max_lt_iff] using
        And.intro (hδ.trans_le hρr) (hu.trans_le hρr))
  refine ⟨ρ,hρ,?_,?_,?_,?_,?_,?_⟩
  · intro δ hδ
    have hn : ‖δ‖<ρ := by simpa only [Metric.mem_ball,dist_zero_right] using hδ
    exact (hpoint δ 0 hn (by simpa using hρ)).2.2.1
  · intro p hp
    have hn : ‖p.1‖<ρ ∧ ‖p.2‖<ρ := by
      simpa only [Set.mem_prod,Metric.mem_ball,dist_zero_right] using hp
    exact (hpoint p.1 p.2 hn.1 hn.2).1
  · intro p hp
    have hn : ‖p.1‖<ρ ∧ ‖p.2‖<ρ := by
      simpa only [Set.mem_prod,Metric.mem_ball,dist_zero_right] using hp
    exact (hpoint p.1 p.2 hn.1 hn.2).2.1
  · intro δ hδ
    have ht := hpoint δ 0 hδ (by simpa using hρ)
    exact ⟨ht.2.2.2.1,ht.2.2.2.2.1⟩
  · intro δ u hδ hu
    have ht := hpoint δ u hδ hu
    exact ⟨ht.2.2.2.2.2.1,ht.2.2.2.2.2.2⟩
  · intro δ hδ
    exact hphysical (show dist δ 0<ε by
      simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ.1] using hδ.2.trans_le hρε) hδ.1
end WP.Analysis
