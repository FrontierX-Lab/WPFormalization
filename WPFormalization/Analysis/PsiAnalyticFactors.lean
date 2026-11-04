import WPFormalization.Analysis.ParameterInverse
import WPFormalization.Analysis.CriticalCuspCoordinates

/-! Convergent analytic factors of the actual cusp profile in the square
root coordinate. Analytic inversion of the genuine critical X factor and
finite chain-rule identities construct all three Euler factors. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma Psi_critical_first_analytic_factor :
    ∃ ε : ℝ,0 < ε ∧ ∃ f₀ : ℝ → ℝ,AnalyticAt ℝ f₀ 0 ∧ f₀ 0 = 5/4 ∧
      ∀ t ∈ Ioo 0 ε,WP.Psi (xCritical*(1-t^2))*t^2 = f₀ t := by
  obtain ⟨D,hD,hD0,hDf⟩ := criticalDelta_factor
  obtain ⟨M,hM,hM0,hMf⟩ := analytic_factor_at_zero criticalMoment criticalMoment_analyticAt_zero criticalMoment_zero
  rw [criticalMoment_hasDerivAt_zero.deriv] at hM0
  obtain ⟨B,hB,hB0,hBf⟩ := criticalXDifference_factor
  have hb := criticalB_pos
  have hx := critical_x_pos
  let V : ℝ → ℝ := fun δ => δ*Real.sqrt (B δ/xCritical)
  have hs0 : 0 < B 0/xCritical := by rw [hB0];positivity
  have hBa : AnalyticAt ℝ (fun δ : ℝ => B δ/xCritical) 0 := hB.div_const
  have hSa : AnalyticAt ℝ (fun δ => Real.sqrt (B δ/xCritical)) 0 :=
    (sqrt_analyticAt_of_pos _ hs0).comp_of_eq hBa rfl
  have hV : AnalyticAt ℝ V 0 := analyticAt_id.mul hSa
  have hV0 : V 0 = 0 := by dsimp [V];ring
  have hVd : HasDerivAt V (Real.sqrt (B 0/xCritical)) 0 := by
    simpa only [V,id_eq,Pi.mul_apply,zero_mul,one_mul,add_zero] using!
      (hasDerivAt_id (0:ℝ)).mul hSa.differentiableAt.hasDerivAt
  have hVp : 0 < deriv V 0 := by rw [hVd.deriv];exact Real.sqrt_pos.mpr hs0
  let d : ℝ → ℝ := hV.hasStrictDerivAt.localInverse V (deriv V 0) 0 hVp.ne'
  have hda : AnalyticAt ℝ d 0 := by simpa only [hV0] using hV.analyticAt_localInverse hVp.ne'
  have hd0 : d 0 = 0 := by
    have he := (hV.hasStrictDerivAt.eventually_left_inverse hVp.ne').self_of_nhds
    simpa only [hV0] using he
  have hdd : HasDerivAt d (deriv V 0)⁻¹ 0 := by
    simpa only [hV0] using (hV.hasStrictDerivAt.to_localInverse hVp.ne').hasDerivAt
  have hdp : 0 < deriv d 0 := by rw [hdd.deriv];positivity
  obtain ⟨G,hG,hG0,hGf⟩ := analytic_factor_at_zero d hda hd0
  have hGp : 0 < G 0 := by rwa [hG0]
  have hGe : ∀ᶠ t in 𝓝 (0:ℝ),0 < G t := hG.continuousAt.tendsto.eventually (eventually_gt_nhds hGp)
  have hde : ∀ᶠ t in 𝓝 (0:ℝ),0 < t → 0 < d t := by
    filter_upwards [hGe,hGf] with t ht he hp
    rw [he]
    exact mul_pos hp ht
  have hdt : Tendsto d (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by simpa only [hd0] using hda.continuousAt.tendsto
  have hdlt : ∀ᶠ t in 𝓝 (0:ℝ),d t < y₀ := hdt.eventually (eventually_lt_nhds y₀_pos)
  have hVr : ∀ᶠ t in 𝓝 (0:ℝ),V (d t) = t := by
    simpa only [hV0] using hV.hasStrictDerivAt.eventually_right_inverse hVp.ne'
  have hDpos : ∀ᶠ δ in 𝓝 (0:ℝ),0 < D δ := by
    have hp : 0 < D 0 := by rw [hD0];norm_num
    exact hD.continuousAt.tendsto.eventually (eventually_gt_nhds hp)
  have hMpos : ∀ᶠ δ in 𝓝 (0:ℝ),0 < M δ := by
    have hp : 0 < M 0 := by rw [hM0];positivity
    exact hM.continuousAt.tendsto.eventually (eventually_gt_nhds hp)
  have hBpos : ∀ᶠ δ in 𝓝 (0:ℝ),0 < B δ := by
    have hp : 0 < B 0 := by rw [hB0];positivity
    exact hB.continuousAt.tendsto.eventually (eventually_gt_nhds hp)
  have hshift : Tendsto (fun δ : ℝ => y₀-δ) (𝓝[>] (0:ℝ)) (𝓝[<] y₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => y₀) (𝓝[>] (0:ℝ)) (𝓝 y₀)).sub hi
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact sub_lt_self y₀ (show (0:ℝ) < δ from hδ)
  have hTc : ∀ᶠ δ in 𝓝 (0:ℝ),0 < δ → WP.T (y₀-δ) = criticalStationaryBranch (y₀-δ) := by
    exact eventually_nhdsWithin_iff.mp (T_eventually_eq_criticalStationaryBranch.comp_tendsto hshift)
  let U : ℝ → ℝ := fun δ => XR (y₀-δ)/(2*D δ*M δ)
  have hUa : AnalyticAt ℝ U 0 := by
    have hXa : AnalyticAt ℝ (fun δ : ℝ => XR (y₀-δ)) 0 :=
      (XR_analyticAt (y₀-(0:ℝ))).comp (analyticAt_const.sub analyticAt_id)
    exact hXa.div ((analyticAt_const.mul hD).mul hM) (by rw [hD0,hM0];positivity)
  let f₀ : ℝ → ℝ := fun t => U (d t)*B (d t)/xCritical
  have hfa : AnalyticAt ℝ f₀ 0 := by
    have hUa' : AnalyticAt ℝ U (d 0) := by simpa only [hd0] using hUa
    have hBa' : AnalyticAt ℝ B (d 0) := by simpa only [hd0] using hB
    exact ((hUa'.comp hda).mul (hBa'.comp hda)).div_const
  have hf0 : f₀ 0 = 5/4 := by
    dsimp only [f₀,U]
    rw [hd0,sub_zero,hD0,hM0,hB0]
    change XR y₀/(2*(3/2)*((2/15)*criticalB))*(criticalB/2)/xCritical = 5/4
    change xCritical/(2*(3/2)*((2/15)*criticalB))*(criticalB/2)/xCritical = 5/4
    field_simp [hb.ne',hx.ne'] <;> ring
  have he : ∀ᶠ t in 𝓝 (0:ℝ),0 < t → WP.Psi (xCritical*(1-t^2))*t^2 = f₀ t := by
    filter_upwards [hde,hdlt,hVr,hdt.eventually hDf,hdt.eventually hMf,hdt.eventually hBf,
      hdt.eventually hDpos,hdt.eventually hMpos,hdt.eventually hBpos,hdt.eventually hTc]
      with t hdp' hdlt' hvr hdf hmf hbf hD' hM' hB' hT' ht
    let δ := d t
    let Y := y₀-δ
    have hδ : 0 < δ := hdp' ht
    have hY : Y ∈ Ico 0 y₀ := ⟨by dsimp [Y];linarith,by dsimp [Y];linarith⟩
    have hT : WP.T Y = criticalStationaryBranch Y := hT' hδ
    have hΔ : WP.Delta Y = δ*D δ := by
      unfold WP.Delta
      rw [hT]
      exact hdf
    have hMom : stationaryWeighted (fun s => s^2) (deriv X) Y (WP.T Y) = δ*M δ := by
      rw [hT]
      exact hmf
    have hsquare : t^2 = δ^2*(B δ/xCritical) := by
      rw [← hvr]
      dsimp only [V]
      rw [mul_pow,Real.sq_sqrt (div_pos hB' hx).le]
    have hsqmul : xCritical*t^2 = δ^2*B δ := by
      rw [hsquare]
      field_simp [hx.ne']
    have hX : XR Y = xCritical*(1-t^2) := by
      have hbf' : xCritical-XR Y = δ^2*B δ := hbf
      nlinarith
    have hi := inverseY_eq_of_root (xCritical*(1-t^2)) Y hY.2.le hX
    dsimp only [f₀,U]
    rw [WP.Psi,hi,density_weighted_identity Y hY,hΔ,hMom,hsquare]
    have hdne : d t ≠ 0 := hδ.ne'
    dsimp only [δ,Y]
    field_simp [hdne,hD'.ne',hM'.ne',hx.ne'] <;> ring
  obtain ⟨ε,hε,hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε,hε,f₀,hfa,hf0,?_⟩
  intro t ht
  apply hbound ?_ ht.1
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht.1] using ht.2
lemma Psi_critical_analytic_factors :
    ∃ ε : ℝ,0 < ε ∧ ∃ f₀ f₁ f₂ : ℝ → ℝ,
      AnalyticAt ℝ f₀ 0 ∧ AnalyticAt ℝ f₁ 0 ∧ AnalyticAt ℝ f₂ 0 ∧
      f₀ 0 = 5/4 ∧ f₁ 0 = 5/4 ∧ ∀ t ∈ Ioo 0 ε,
        WP.Psi (xCritical*(1-t^2))*t^2 = f₀ t ∧
        WP.euler WP.Psi (xCritical*(1-t^2))*t^4 = f₁ t ∧
        WP.euler (WP.euler WP.Psi) (xCritical*(1-t^2))*t^6 = f₂ t := by
  obtain ⟨ε,hε,f₀,hf₀,hf₀0,h₀⟩ := Psi_critical_first_analytic_factor
  let f₁ : ℝ → ℝ := fun t => (1-t^2)*(f₀ t-(t/2)*deriv f₀ t)
  let f₂ : ℝ → ℝ := fun t => (1-t^2)*(2*f₁ t-(t/2)*deriv f₁ t)
  have hdf₀ := hf₀.deriv
  have hf₁ : AnalyticAt ℝ f₁ 0 := by dsimp only [f₁];fun_prop
  have hdf₁ := hf₁.deriv
  have hf₂ : AnalyticAt ℝ f₂ 0 := by dsimp only [f₂];fun_prop
  have hf₁0 : f₁ 0 = 5/4 := by simp only [f₁,zero_pow (by norm_num : 2 ≠ 0),sub_zero,zero_div,zero_mul,one_mul,hf₀0]
  let η : ℝ := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hcurve (t : ℝ) : HasDerivAt (fun s : ℝ => xCritical*(1-s^2)) (-2*xCritical*t) t := by
    convert! (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).const_mul xCritical) using 1 <;> simp only [id_eq,Pi.pow_apply] <;> ring
  have harg (t : ℝ) (ht : t ∈ Ioo 0 η) : xCritical*(1-t^2) ∈ Ico 0 xCritical := by
    have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have hx := critical_x_pos
    constructor
    · have hp : 0 < 1-t^2 := by nlinarith [ht.1,ht1]
      exact (mul_pos hx hp).le
    · nlinarith [mul_pos hx (sq_pos_of_pos ht.1)]
  have hfirst (t : ℝ) (ht : t ∈ Ioo 0 η) :
      WP.euler WP.Psi (xCritical*(1-t^2))*t^4 = f₁ t := by
    have hP := (Psi_analyticAt_interior _ (harg t ht)).differentiableAt.hasDerivAt
    have hd := (hP.comp t (hcurve t)).mul ((hasDerivAt_id t).pow 2)
    have heq : (fun s => WP.Psi (xCritical*(1-s^2))*s^2) =ᶠ[𝓝 t] f₀ := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact h₀ s ⟨hs.1,lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have hder := (hd.congr_of_eventuallyEq heq.symm).deriv
    have hv := h₀ t ⟨ht.1,lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    dsimp only [f₁,WP.euler]
    rw [hder,← hv]
    simp only [Function.comp_def,Pi.pow_apply,id_eq]
    ring
  refine ⟨η,hη,f₀,f₁,f₂,hf₀,hf₁,hf₂,hf₀0,hf₁0,?_⟩
  intro t ht
  refine ⟨h₀ t ⟨ht.1,lt_of_lt_of_le ht.2 (min_le_left _ _)⟩,hfirst t ht,?_⟩
  have hE : AnalyticAt ℝ (WP.euler WP.Psi) (xCritical*(1-t^2)) :=
    analyticAt_id.mul (Psi_analyticAt_interior _ (harg t ht)).deriv
  have hd := (hE.differentiableAt.hasDerivAt.comp t (hcurve t)).mul ((hasDerivAt_id t).pow 4)
  have heq : (fun s => WP.euler WP.Psi (xCritical*(1-s^2))*s^4) =ᶠ[𝓝 t] f₁ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hfirst s hs
  have hder := (hd.congr_of_eventuallyEq heq.symm).deriv
  dsimp only [f₂,WP.euler]
  rw [hder,← hfirst t ht]
  simp only [Function.comp_def,Pi.pow_apply,id_eq]
  ring
theorem parameter_analytic_expansions_proof :
    AnalyticAt ℝ Psi 0 ∧ AnalyticAt ℝ (euler Psi) 0 ∧ AnalyticAt ℝ (euler (euler Psi)) 0 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ f₀ f₁ f₂ : ℝ → ℝ,
      AnalyticAt ℝ f₀ 0 ∧ AnalyticAt ℝ f₁ 0 ∧ AnalyticAt ℝ f₂ 0 ∧
      f₀ 0 = 5/4 ∧ f₁ 0 = 5/4 ∧ ∀ t ∈ Set.Ioo 0 δ,
        Psi (xCritical*(1-t^2))*t^2 = f₀ t ∧
        euler Psi (xCritical*(1-t^2))*t^4 = f₁ t ∧
        euler (euler Psi) (xCritical*(1-t^2))*t^6 = f₂ t := by
  exact ⟨Psi_origin_analytic.1,Psi_origin_analytic.2.1,Psi_origin_analytic.2.2,
    Psi_critical_analytic_factors⟩

end WP.Analysis
