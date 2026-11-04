import WPFormalization.Analysis.PsiAnalyticFactors
import Mathlib.Topology.Order.ExtendFrom

/-! Complete proof of Lemma3.1(iv). The analytic factors give all endpoint
errors and ratio limits; continuous extension to the closed interval gives
the uniform ratio bound. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
def cuspCoordinate (x : ℝ) : ℝ := Real.sqrt (1-x/xCritical)
lemma cuspCoordinate_tendsto : Tendsto cuspCoordinate (𝓝[<] xCritical) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x) (𝓝[<] xCritical) (𝓝 xCritical) := tendsto_id.mono_left nhdsWithin_le_nhds
  have he := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[<] xCritical) (𝓝 1)).sub (hi.div_const xCritical)
  simp only [div_self critical_x_pos.ne',sub_self] at he
  simpa only [cuspCoordinate,Function.comp_def,Real.sqrt_zero] using! Real.continuous_sqrt.continuousAt.tendsto.comp he
lemma cuspEpsilon_pos (x : ℝ) (hx : x ∈ Ioo 0 xCritical) : 0 < 1-x/xCritical :=
  sub_pos.mpr ((div_lt_one critical_x_pos).mpr hx.2)
lemma cuspCoordinate_pos (x : ℝ) (hx : x ∈ Ioo 0 xCritical) : 0 < cuspCoordinate x :=
  Real.sqrt_pos.mpr (cuspEpsilon_pos x hx)
lemma cuspCoordinate_square (x : ℝ) (hx : x ∈ Ioo 0 xCritical) :
    (cuspCoordinate x)^2 = 1-x/xCritical := Real.sq_sqrt (cuspEpsilon_pos x hx).le
lemma cuspCoordinate_curve (x : ℝ) (hx : x ∈ Ioo 0 xCritical) :
    xCritical*(1-(cuspCoordinate x)^2) = x := by
  rw [cuspCoordinate_square x hx]
  field_simp [critical_x_pos.ne'] <;> ring
lemma cuspWeight_interior_eventually : ∀ᶠ x in 𝓝[<] xCritical,x ∈ Ioo 0 xCritical := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds critical_x_pos).filter_mono nhdsWithin_le_nhds] with x hx hpos
  exact ⟨hpos,hx⟩
lemma cuspCoordinate_eventually_mem (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[<] xCritical,cuspCoordinate x ∈ Ioo 0 ε := by
  filter_upwards [cuspWeight_interior_eventually,cuspCoordinate_tendsto.eventually (eventually_lt_nhds hε)] with x hx ht
  exact ⟨cuspCoordinate_pos x hx,ht⟩
lemma Psi_critical_estimates :
    (fun x => WP.Psi x/(5/(4*(1-x/xCritical)))-1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (fun x => WP.euler WP.Psi x/(5/(4*(1-x/xCritical)^2))-1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (WP.euler (WP.euler WP.Psi)) =O[𝓝[<] xCritical] (fun x => (1-x/xCritical)⁻¹^3) ∧
    Tendsto (fun x => WP.Psi x^2/WP.euler WP.Psi x) (𝓝[<] xCritical) (𝓝 (5/4)) := by
  obtain ⟨ε,hε,f₀,f₁,f₂,hf₀,hf₁,hf₂,hf₀0,hf₁0,hf⟩ := Psi_critical_analytic_factors
  have he : ∀ᶠ x in 𝓝[<] xCritical,
      WP.Psi x*(cuspCoordinate x)^2 = f₀ (cuspCoordinate x) ∧
      WP.euler WP.Psi x*(cuspCoordinate x)^4 = f₁ (cuspCoordinate x) ∧
      WP.euler (WP.euler WP.Psi) x*(cuspCoordinate x)^6 = f₂ (cuspCoordinate x) := by
    filter_upwards [cuspWeight_interior_eventually,cuspCoordinate_eventually_mem ε hε] with x hx ht
    simpa only [cuspCoordinate_curve x hx] using hf (cuspCoordinate x) ht
  have hR₀a : AnalyticAt ℝ (fun t => (4/5:ℝ)*f₀ t-1) 0 := (analyticAt_const.mul hf₀).sub analyticAt_const
  have hR₀0 : (4/5:ℝ)*f₀ 0-1 = 0 := by rw [hf₀0];norm_num
  have hO₀ := (analytic_vanishing_isBigO _ hR₀a hR₀0).comp_tendsto cuspCoordinate_tendsto
  have hEq₀ : ((fun t => (4/5:ℝ)*f₀ t-1) ∘ cuspCoordinate) =ᶠ[𝓝[<] xCritical]
      (fun x => WP.Psi x/(5/(4*(1-x/xCritical)))-1) := by
    filter_upwards [he,cuspWeight_interior_eventually] with x hx hxi
    dsimp only [Function.comp_def]
    rw [← hx.1,cuspCoordinate_square x hxi]
    field_simp [(cuspEpsilon_pos x hxi).ne'] <;> ring
  have hR₁a : AnalyticAt ℝ (fun t => (4/5:ℝ)*f₁ t-1) 0 := (analyticAt_const.mul hf₁).sub analyticAt_const
  have hR₁0 : (4/5:ℝ)*f₁ 0-1 = 0 := by rw [hf₁0];norm_num
  have hO₁ := (analytic_vanishing_isBigO _ hR₁a hR₁0).comp_tendsto cuspCoordinate_tendsto
  have hEq₁ : ((fun t => (4/5:ℝ)*f₁ t-1) ∘ cuspCoordinate) =ᶠ[𝓝[<] xCritical]
      (fun x => WP.euler WP.Psi x/(5/(4*(1-x/xCritical)^2))-1) := by
    filter_upwards [he,cuspWeight_interior_eventually] with x hx hxi
    have ht4 : (cuspCoordinate x)^4 = (1-x/xCritical)^2 := by
      rw [show (cuspCoordinate x)^4 = ((cuspCoordinate x)^2)^2 by ring,cuspCoordinate_square x hxi]
    dsimp only [Function.comp_def]
    rw [← hx.2.1,ht4]
    field_simp [(cuspEpsilon_pos x hxi).ne'] <;> ring
  have hB₂ : f₂ =O[𝓝 (0:ℝ)] (fun _ => (1:ℝ)) :=
    Asymptotics.isBigO_const_of_tendsto hf₂.continuousAt.tendsto one_ne_zero
  let G : ℝ → ℝ := fun x => (1-x/xCritical)⁻¹^3
  have hO₂ := (hB₂.comp_tendsto cuspCoordinate_tendsto).mul
    (Asymptotics.isBigO_refl G (𝓝[<] xCritical))
  have hEq₂ : (fun x => f₂ (cuspCoordinate x)*G x) =ᶠ[𝓝[<] xCritical] WP.euler (WP.euler WP.Psi) := by
    filter_upwards [he,cuspWeight_interior_eventually] with x hx hxi
    have ht6 : (cuspCoordinate x)^6 = (1-x/xCritical)^3 := by
      rw [show (cuspCoordinate x)^6 = ((cuspCoordinate x)^2)^3 by ring,cuspCoordinate_square x hxi]
    dsimp only [G]
    rw [← hx.2.2,ht6]
    field_simp [(cuspEpsilon_pos x hxi).ne']
  have hR := ((hf₀.continuousAt.tendsto.comp cuspCoordinate_tendsto).pow 2).div
    (hf₁.continuousAt.tendsto.comp cuspCoordinate_tendsto) (by rw [hf₁0];norm_num)
  have hEqR : (fun x => (f₀ (cuspCoordinate x))^2/f₁ (cuspCoordinate x)) =ᶠ[𝓝[<] xCritical]
      (fun x => WP.Psi x^2/WP.euler WP.Psi x) := by
    filter_upwards [he,cuspWeight_interior_eventually] with x hx hxi
    have hE : 0 < WP.euler WP.Psi x := mul_pos hxi.1 (Psi_deriv_pos_interior x ⟨hxi.1.le,hxi.2⟩)
    rw [← hx.1,← hx.2.1]
    field_simp [hE.ne',(cuspCoordinate_pos x hxi).ne'] <;> ring
  refine ⟨hO₀.congr' hEq₀ Filter.EventuallyEq.rfl,hO₁.congr' hEq₁ Filter.EventuallyEq.rfl,?_,?_⟩
  · exact hO₂.congr' hEq₂ (by filter_upwards with x;exact one_mul (G x))
  · simpa only [hf₀0,hf₁0,show (5/4:ℝ)^2/(5/4) = 5/4 by norm_num] using hR.congr' hEqR
lemma Psi_origin_ratio_limit : Tendsto (fun x => WP.Psi x^2/WP.euler WP.Psi x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hP := Psi_origin_analytic.1
  have hE := Psi_origin_analytic.2.1
  have hE0 : WP.euler WP.Psi 0 = 0 := by simp only [WP.euler,zero_mul]
  have hEd : deriv (WP.euler WP.Psi) 0 = 2 := by rw [euler_deriv_zero hP,Psi_deriv_zero_value]
  obtain ⟨R,hR,hR0,he⟩ := analytic_removable_ratio_at_zero WP.Psi (WP.euler WP.Psi)
    hP hE Psi_zero_value hE0 (by rw [hEd];norm_num)
  rw [Psi_deriv_zero_value,hEd,div_self (by norm_num : (2:ℝ) ≠ 0)] at hR0
  have ht : Tendsto R (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa only [hR0] using hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : R =ᶠ[𝓝[>] (0:ℝ)] (fun x => WP.Psi x/WP.euler WP.Psi x) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hx hpos
    exact (hx (ne_of_gt hpos)).symm
  have hratio := ht.congr' heq
  have hPsi : Tendsto WP.Psi (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Psi_zero_value] using hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm := hPsi.mul hratio
  simpa only [zero_mul] using hm.congr' (Filter.Eventually.of_forall (fun x => by ring))
lemma Psi_ratio_continuousOn :
    ContinuousOn (fun x => WP.Psi x^2/WP.euler WP.Psi x) (Ioo 0 xCritical) := by
  intro x hx
  have hP := Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩
  have hE : AnalyticAt ℝ (WP.euler WP.Psi) x := analyticAt_id.mul hP.deriv
  have hp : 0 < WP.euler WP.Psi x := mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  exact ((hP.pow 2).continuousAt.div hE.continuousAt hp.ne').continuousWithinAt
lemma Psi_ratio_bounded : ∃ C : ℝ,∀ x ∈ Ioo 0 xCritical,|WP.Psi x^2/WP.euler WP.Psi x| ≤ C := by
  let F : ℝ → ℝ := fun x => WP.Psi x^2/WP.euler WP.Psi x
  have hc : ContinuousOn (extendFrom (Ioo 0 xCritical) F) (Icc 0 xCritical) :=
    continuousOn_Icc_extendFrom_Ioo Psi_ratio_continuousOn Psi_origin_ratio_limit Psi_critical_estimates.2.2.2
  have ha : ContinuousOn (fun x => |extendFrom (Ioo 0 xCritical) F x|) (Icc 0 xCritical) :=
    continuous_abs.comp_continuousOn hc
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image ha
  refine ⟨C,?_⟩
  intro x hx
  have hv : extendFrom (Ioo 0 xCritical) F x = F x :=
    extendFrom_eq (subset_closure hx) (Psi_ratio_continuousOn x hx)
  change |F x| ≤ C
  rw [← hv]
  exact hC ⟨x,⟨hx.1.le,hx.2.le⟩,rfl⟩
theorem parameter_cusp_weight_proof :
    (∀ x ∈ Set.Ioo 0 xCritical, AnalyticAt ℝ Psi x) ∧
    StrictMonoOn Psi (Set.Ioo 0 xCritical) ∧
    (∀ j ∈ Finset.range 3,
      (fun x => (euler^[j]) Psi x - 2*x) =O[𝓝[>] (0 : ℝ)] (fun x => x^2)) ∧
    (fun x => Psi x / (5/(4*(1-x/xCritical))) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (fun x => euler Psi x / (5/(4*(1-x/xCritical)^2)) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (euler (euler Psi)) =O[𝓝[<] xCritical] (fun x => (1-x/xCritical)⁻¹^3) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[<] xCritical) (𝓝 (5/4)) ∧
    (∃ C : ℝ, ∀ x ∈ Set.Ioo 0 xCritical, |Psi x^2 / euler Psi x| ≤ C) := by
  exact ⟨fun x hx => Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩,Psi_strictMonoOn,
    Psi_origin_errors,Psi_critical_estimates.1,Psi_critical_estimates.2.1,
    Psi_critical_estimates.2.2.1,Psi_origin_ratio_limit,Psi_critical_estimates.2.2.2,
    Psi_ratio_bounded⟩

end WP.Analysis
