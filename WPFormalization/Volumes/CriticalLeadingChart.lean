import WPFormalization.Volumes.CriticalCenteredLog
import WPFormalization.Volumes.CriticalLeadingRealTrace
/-! A single proved critical leading Gaussian chart for the actual model.
The genuine coordinate and Theta unit are chosen from existing producers.
The common radius precedes the critical distance and genus. It retains the
literal centered log action, its normalized jets and quadratic bound, the
literal leading amplitude with axis value one, and the physical real tilt
trace centered at the arbitrary real mean h*Psi(x). No coefficient-index or
integer-saddle assumption is introduced. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma actual_critical_leading_gaussian_chart (P:PsiTheory)(p:ℕ):
    ∃(d:CriticalGaussianCoordinateData)(Q:ℂ→ℂ)(ρ C D:ℝ),
      AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      0<ρ ∧ ρ<y₀ ∧ 0<C ∧ 0<D ∧
      ∀δ∈Ioo (0:ℝ) ρ,∀g:ℕ,Stable g p→0<(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let L:ℂ→ℂ:=d.centeredLogAction h (δ:ℂ)
      let A:ℂ→ℂ:=d.leadingCenteredAmplitude Q p h (δ:ℂ)
      AnalyticOnNhd ℂ L (Metric.ball 0 (ρ*Real.sqrt h)) ∧
      L 0=0 ∧ WP.coeff L 1=0 ∧ WP.coeff L 2=(1/2:ℂ) ∧
      (∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖L w‖≤C*‖w‖^2) ∧
      AnalyticOnNhd ℂ A (Metric.ball 0 (ρ*Real.sqrt h)) ∧ A 0=1 ∧
      (∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖A w‖≤D) ∧
      ∀u:ℝ,|u|<ρ*Real.sqrt h→
        let x:ℝ:=XR (y₀-δ)
        let σ:ℝ:=Real.sqrt (h*euler Psi x)
        let xt:ℝ:=x*Real.exp (u/σ)
        xt∈Ioo (0:ℝ) xCritical ∧
        Complex.exp (L (u:ℂ))*A (u:ℂ)=
          Complex.exp (-((h*Psi x:ℝ):ℂ)*(u:ℂ)/(σ:ℂ))*
            ((markedModel g p (inverseY xt)/markedModel g p (y₀-δ):ℝ):ℂ):=by
  obtain ⟨d⟩:=exists_criticalGaussianCoordinateData
  obtain ⟨Q,hQa,hQ0,hQphys⟩:=exists_criticalThetaUnit
  obtain ⟨Rl,C,hRl,hC,hlog⟩:=d.centered_log_action_common_bound
  obtain ⟨Ra,hRa,hamp⟩:=d.leading_centered_amplitude_common_bound Q hQa hQ0 p
  obtain ⟨Rt,hRt,hRty,htrace⟩:=d.leading_model_real_trace P p Q hQphys
  let ρ:ℝ:=min Rl (min Ra Rt)
  have hρ:0<ρ:=lt_min hRl (lt_min hRa hRt)
  have hρl:ρ≤Rl:=min_le_left _ _
  have hρa:ρ≤Ra:=(min_le_right _ _).trans (min_le_left _ _)
  have hρt:ρ≤Rt:=(min_le_right _ _).trans (min_le_right _ _)
  have hρy:ρ<y₀:=hρt.trans_lt hRty
  refine ⟨d,Q,ρ,C,2,hQa,hQ0,hQphys,hρ,hρy,hC,by norm_num,?_⟩
  intro δ hδ g hs hh
  dsimp only
  let h:ℝ:=complexity g p
  have hδnorm:‖(δ:ℂ)‖<ρ:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2
  have hl:=hlog (δ:ℂ) (hδnorm.trans_le hρl) h hh
  have ha:=hamp (δ:ℂ) (hδnorm.trans_le hρa) h hh
  have hpos:0≤Real.sqrt h:=Real.sqrt_nonneg h
  have hballl:Metric.ball (0:ℂ) (ρ*Real.sqrt h)⊆Metric.ball 0 (Rl*Real.sqrt h):=
    Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hρl hpos)
  have hballa:Metric.ball (0:ℂ) (ρ*Real.sqrt h)⊆Metric.ball 0 (Ra*Real.sqrt h):=
    Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hρa hpos)
  refine ⟨hl.1.mono hballl,hl.2.1,?_,hl.2.2.2.1,?_,ha.1.mono hballa,ha.2.1,?_,?_⟩
  · simpa only[WP.coeff,Nat.factorial_one,Nat.cast_one,div_one,iteratedDeriv_one] using hl.2.2.1
  · intro w hw
    exact hl.2.2.2.2 w (hw.trans_le (mul_le_mul_of_nonneg_right hρl hpos))
  · intro w hw
    exact ha.2.2 w (hw.trans_le (mul_le_mul_of_nonneg_right hρa hpos))
  · intro u hu
    exact htrace δ ⟨hδ.1,hδ.2.trans_le hρt⟩ g hs hh u
      (hu.trans_le (mul_le_mul_of_nonneg_right hρt hpos))
end WP.Analysis
