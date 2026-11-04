import WPFormalization.Tight.ConnectedPoissonPhi
import WPFormalization.Tight.UnmarkedKappaFactor

noncomputable section
namespace WP.TightConnected
open Set Filter TightMoments
open scoped Topology

lemma connected_momentTightG_zero_eq_phi (P : PsiTheory) (g : ℕ) (hg : 2≤g)
    (L : Fin 0→ℝ) (z : ℂ) (hz : ‖z‖<xCritical) :
    momentTightG P g 0 L z=Phi P g z := by
  have hs : Stable g 0 := by unfold Stable;omega
  have hf : AnalyticOnNhd ℂ (momentTightG P g 0 L) (Metric.ball 0 xCritical) := by
    intro w hw
    exact momentTightG_analyticAt P g 0 L w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hp : AnalyticOnNhd ℂ (Phi P g) (Metric.ball 0 xCritical) := by
    intro w hw
    exact Phi_analyticAt_open_disk P g w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hc : xCritical/2∈Ioo (0:ℝ) xCritical :=
    ⟨half_pos Analysis.xCritical_pos_parameter,half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem : ((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he : EqOn (momentTightG P g 0 L) (Phi P g) (Metric.ball 0 xCritical) := by
    apply Analysis.complex_identity_of_real_germ _ _ _ (xCritical/2) hf hp
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
    rw [momentTightG_ofReal P g 0 L x ⟨hx.1.le,hx.2⟩,
      TightUnmarked.tightShiftedPolynomial_zero]
    have ht := PositiveConvolution.Phi_iteratedDeriv_ofReal P g 0 hs x ⟨hx.1.le,hx.2⟩
    simpa only [iteratedDeriv_zero,List.replicate_zero] using ht.symm
  exact he (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

lemma connected_momentTightG_zero_coeff (P : PsiTheory) (g : ℕ) (hg : 2≤g)
    (L : Fin 0→ℝ) (n : ℕ) :
    realCoeff (momentTightG P g 0 L) n=realCoeff (Phi P g) n := by
  have he : momentTightG P g 0 L=ᶠ[𝓝 (0:ℂ)] Phi P g := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz
    exact connected_momentTightG_zero_eq_phi P g hg L z
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  simp only [realCoeff,WP.coeff,he.iteratedDeriv_eq n]

end WP.TightConnected
