import WPFormalization.Analysis.ChainParameterProfile
import WPFormalization.Statements.ChainDefinitions

/-! The closed form (12.1) of the original integral chain profile.
This is an identity for the paper's original density inverse and stationary
parameter, proved by an actual change of variables and differentiation. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

def chainIntegrand (t : ℝ) : ℝ :=
  Real.log (4*WP.Delta (WP.densityY (2*t/(1-t)))/Real.pi^2)

lemma chain_beta_density_coordinate (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    2*WP.beta Y/(1-WP.beta Y) = WP.density Y := by
  have hd := WP.density_nonneg Y hY
  have hn : 2+WP.density Y ≠ 0 := by positivity
  rw [WP.beta_density_identity Y hY]
  field_simp [hn]
  ring

lemma chainIntegrand_beta (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    chainIntegrand (WP.beta Y) = Real.log (4*WP.Delta Y/Real.pi^2) := by
  rw [chainIntegrand,chain_beta_density_coordinate Y hY,chain_densityY_density Y hY]

lemma chainIntegrand_continuousOn : ContinuousOn chainIntegrand (Ico 0 1) := by
  unfold chainIntegrand
  have hc : ContinuousOn (fun t : ℝ => 2*t/(1-t)) (Ico 0 1) :=
    (continuousOn_const.mul continuousOn_id).div (continuousOn_const.sub continuousOn_id)
      (fun t ht => sub_ne_zero.mpr (ne_of_gt ht.2))
  have hm : MapsTo (fun t : ℝ => 2*t/(1-t)) (Ico 0 1) (Ici 0) := by
    intro t ht
    exact div_nonneg (mul_nonneg (by norm_num) ht.1) (sub_pos.mpr ht.2).le
  have hden := chain_densityY_continuousOn.comp hc hm
  have hDel : ContinuousOn WP.Delta (Ico 0 y₀) :=
    fun Y hY => (chain_Delta_hasDerivAt Y hY).continuousAt.continuousWithinAt
  have hpar : MapsTo (fun t : ℝ => WP.densityY (2*t/(1-t))) (Ico 0 1) (Ico 0 y₀) :=
    fun t ht => (densityY_spec _ (hm ht)).1
  have hval : ContinuousOn (fun t : ℝ =>
      4*WP.Delta (WP.densityY (2*t/(1-t)))/Real.pi^2) (Ico 0 1) :=
    (continuousOn_const.mul (hDel.comp hden hpar)).div_const (Real.pi^2)
  exact hval.log
    (fun t ht => (div_pos (mul_pos (by norm_num)
      (WP.Delta_pos _ (hpar ht))) (sq_pos_of_pos Real.pi_pos)).ne')

lemma chainProfile_closed_form_parameter (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    WP.chainProfile (WP.beta Y) = chainClosedProfileY Y := by
  have hbY := WP.beta_lt_one Y hY
  have hu : uIcc (0 : ℝ) Y = Icc 0 Y := uIcc_of_le hY.1
  have hsubset : Icc (0 : ℝ) Y ⊆ Ico 0 y₀ :=
    fun t ht => ⟨ht.1,lt_of_le_of_lt ht.2 hY.2⟩
  have hbeta : ∀ t ∈ uIcc (0 : ℝ) Y,
      HasDerivAt WP.beta (deriv WP.beta t) t := by
    intro t ht
    rw [hu] at ht
    exact (beta_hasDerivAt_interior t (hsubset ht)).differentiableAt.hasDerivAt
  have hbcont : ContinuousOn (deriv WP.beta) (uIcc (0 : ℝ) Y) := by
    intro t ht
    rw [hu] at ht
    have hbt : AnalyticAt ℝ WP.beta t :=
      (XR_analyticAt t).div (J_analyticAt_interior t (hsubset ht))
        (WP.J_pos t (hsubset ht)).ne'
    exact hbt.deriv.continuousAt.continuousWithinAt
  have himg : WP.beta '' uIcc (0 : ℝ) Y ⊆ Ico 0 1 := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hu] at ht
    exact ⟨WP.beta_nonneg t (hsubset ht),WP.beta_lt_one t (hsubset ht)⟩
  have hsub := intervalIntegral.integral_comp_mul_deriv' hbeta hbcont
    (chainIntegrand_continuousOn.mono himg)
  have hint : IntervalIntegrable
      (fun t : ℝ => deriv WP.beta t*Real.log (4*WP.Delta t/Real.pi^2)) volume 0 Y := by
    apply ContinuousOn.intervalIntegrable
    apply hbcont.mul
    apply ContinuousOn.log
    · apply ContinuousOn.div_const
      exact continuousOn_const.mul
        (fun t ht => (chain_Delta_hasDerivAt t (hsubset (hu ▸ ht))).continuousAt.continuousWithinAt)
    · intro t ht
      exact (div_pos (mul_pos (by norm_num) (WP.Delta_pos t (hsubset (hu ▸ ht))))
        (sq_pos_of_pos Real.pi_pos)).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => chainClosedProfileY_hasDerivAt t (hsubset (hu ▸ ht))) hint
  have heq : (∫ t in (0 : ℝ)..Y, (chainIntegrand ∘ WP.beta) t*deriv WP.beta t) =
      ∫ t in (0 : ℝ)..Y, deriv WP.beta t*Real.log (4*WP.Delta t/Real.pi^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change chainIntegrand (WP.beta t)*deriv WP.beta t = _
    rw [chainIntegrand_beta t (hsubset (hu ▸ ht)),mul_comm]
  rw [heq,WP.beta_zero_value] at hsub
  rw [WP.chainProfile,if_neg (ne_of_lt hbY)]
  change (∫ t in (0 : ℝ)..WP.beta Y, chainIntegrand t) = _
  rw [← hsub,hFTC,chainClosedProfileY_zero,sub_zero]

end WP.Analysis
