import WPFormalization.Analysis.ParameterODE
import WPFormalization.Analysis.CriticalParameterCoordinates
import WPFormalization.Analysis.UniformKernelMoments
/-! Actual critical Lipschitz estimates for every normalized K coefficient.
Nonnegative canonical weights give 1 ≤ theta_l ≤ total mass. The exact
mass identity -2*T' and the genuine left analytic stationary germ give
mass = 1+O(y₀-Y), uniformly controlling every l. The actual compact moment
has a removable quotient by a with value 2/15, proving the A rate. The
closed endpoint uses its explicit normalized kernels; r(y₀) is never used.
Logarithmic rates are included for the actual normalized comparison model. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace WP.Analysis
lemma theta_le_total_weight (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (l : ℕ) :
    1 ≤ theta Y l ∧ theta Y l ≤ ∑' j : ℕ,weight Y j := by
  have hw : ∀ j : ℕ,0 ≤ weight Y j := weight_nonneg Y hY
  constructor
  · rw [←theta_zero_closed Y hY]
    exact theta_monotone_of_weight_nonneg Y hw (Nat.zero_le l)
  · rw [←weight_sum_range Y l]
    exact (weight_hasSum_at_one Y hY).summable.sum_le_tsum _ (fun j _ => hw j)

lemma total_weight_critical_value : (∑' l : ℕ,weight y₀ l) = 1 := by
  have he (l : ℕ) : weight y₀ l=if l=0 then 1 else 0 := by
    by_cases h:l=0 <;> simp [weight,critical_kernels.2,h]
  simp_rw [he]
  simp

lemma total_weight_critical_isBigO :
    (fun Y => (∑' l : ℕ,weight Y l)-1) =O[𝓝[<] y₀] (fun Y => Y-y₀) := by
  have hQ : AnalyticAt ℝ (fun Y => -2*deriv criticalStationaryBranch Y) y₀ :=
    analyticAt_const.mul criticalStationaryBranch_analyticAt.deriv
  have hO := hQ.differentiableAt.hasDerivAt.isBigO_sub.mono
    (show 𝓝[<] y₀ ≤ 𝓝 y₀ from nhdsWithin_le_nhds)
  simp only [criticalStationaryBranch_deriv_value] at hO
  have hd := T_eventually_eq_criticalStationaryBranch.derivWithin
  have he : (fun Y => -2*deriv criticalStationaryBranch Y-(-2*(-1/2:ℝ))) =ᶠ[𝓝[<] y₀]
      (fun Y => (∑' l : ℕ,weight Y l)-1) := by
    filter_upwards [hd,self_mem_nhdsWithin,
      (eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds] with Y hD hY hpos
    rw [derivWithin_of_isOpen isOpen_Iio hY,derivWithin_of_isOpen isOpen_Iio hY] at hD
    rw [Theta_eq_neg_two_T_deriv Y ⟨hpos.le,hY⟩,hD]
    ring
  exact hO.congr' he Filter.EventuallyEq.rfl

lemma closed_left_lipschitz_of_isBigO (f : ℝ → ℝ) (a c : ℝ) (hf : f a=c)
    (hO : (fun Y => f Y-c) =O[𝓝[<] a] (fun Y => Y-a)) :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ≤ a,a-Y ≤ δ₀ → |f Y-c| ≤ C*(a-Y) := by
  obtain ⟨C,hC,hbound⟩ := hO.exists_pos
  have he := hbound.bound
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C,ε/2,hC,by positivity,?_⟩
  intro Y hYa hδ
  by_cases hY : Y=a
  · subst Y
    simp [hf]
  · have hlt : Y < a := lt_of_le_of_ne hYa hY
    have hd : dist Y a < ε := by
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hYa)]
      linarith
    have hh := he hd hlt
    simpa only [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hYa),neg_sub] using hh

lemma total_weight_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |(∑' l : ℕ,weight Y l)-1| ≤ C*(y₀-Y) := by
  obtain ⟨C,δ,hC,hδ,hb⟩ := closed_left_lipschitz_of_isBigO
    (fun Y => ∑'l : ℕ,weight Y l) y₀ 1 total_weight_critical_value total_weight_critical_isBigO
  exact ⟨C,δ,hC,hδ,fun Y hY hsmall => hb Y hY.2 hsmall⟩

lemma theta_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      ∀ l : ℕ,1 ≤ theta Y l ∧ theta Y l ≤ 1+C*(y₀-Y) := by
  obtain ⟨C,δ,hC,hδ,hb⟩ := total_weight_critical_lipschitz
  refine ⟨C,δ,hC,hδ,?_⟩
  intro Y hY hsmall l
  have htotal := hb Y hY hsmall
  have hθ := theta_le_total_weight Y hY l
  exact ⟨hθ.1,by linarith [(le_abs_self ((∑'l : ℕ,weight Y l)-1))]⟩
end WP.Analysis
namespace WP.Analysis
lemma critical_a_coordinate_analyticAt : AnalyticAt ℝ (fun δ : ℝ => a (y₀-δ)) 0 := by
  have ha : AnalyticAt ℝ a y₀ := by
    change AnalyticAt ℝ (fun t : ℝ => (deriv X (t:ℂ)).re) y₀
    exact (X_differentiable.deriv.analyticAt (y₀:ℂ)).re_ofReal
  have hc : AnalyticAt ℝ a (y₀-(0:ℝ)) := by simpa only [sub_zero] using ha
  exact hc.comp (analyticAt_const.sub analyticAt_id)

lemma critical_a_coordinate_hasDerivAt :
    HasDerivAt (fun δ : ℝ => a (y₀-δ)) criticalB 0 := by
  have hc : HasDerivAt (fun δ : ℝ => y₀-δ) (-1) 0 := by
    simpa only [id_eq,Pi.sub_apply,zero_sub] using!
      (hasDerivAt_const (0:ℝ) y₀).sub (hasDerivAt_id 0)
  have hd := (a_hasDerivAt (y₀-0)).comp 0 hc
  convert! hd using 1 <;> simp only [criticalB,Function.comp_def,sub_zero,id_eq,zero_sub,mul_neg,mul_one,Pi.sub_apply]

lemma criticalMoment_over_a_factor :
    ∃ R : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ R 0=(2/15:ℝ) ∧
      ∀ᶠ δ in 𝓝 0,δ ≠ 0 → criticalMoment δ/a (y₀-δ)=R δ := by
  obtain ⟨R,hR,hR0,he⟩ := analytic_removable_ratio_at_zero criticalMoment (fun δ : ℝ => a (y₀-δ))
    criticalMoment_analyticAt_zero critical_a_coordinate_analyticAt criticalMoment_zero
    (by simp only [sub_zero,a_y₀_zero])
    (by rw [critical_a_coordinate_hasDerivAt.deriv];exact criticalB_pos.ne')
  refine ⟨R,hR,?_,he⟩
  rw [hR0,criticalMoment_hasDerivAt_zero.deriv,critical_a_coordinate_hasDerivAt.deriv]
  field_simp [criticalB_pos.ne']

lemma A_critical_isBigO : (fun Y => A Y-(2/15:ℝ)) =O[𝓝[<] y₀] (fun Y => Y-y₀) := by
  obtain ⟨R,hR,hR0,he⟩ := criticalMoment_over_a_factor
  have hO := hR.differentiableAt.hasDerivAt.isBigO_sub
  rw [hR0] at hO
  have ht := hO.comp_tendsto deltaCoordinate_tendsto
  have hEq : (fun Y => R (y₀-Y)-(2/15:ℝ)) =ᶠ[𝓝[<] y₀] (fun Y => A Y-(2/15:ℝ)) := by
    filter_upwards [criticalMoment_eq_actual,deltaCoordinate_tendsto.eventually he,
      self_mem_nhdsWithin,(eventually_gt_nhds y₀_pos).filter_mono nhdsWithin_le_nhds]
      with Y hM hR hlt hpos
    have heR := hR (sub_ne_zero.mpr (ne_of_gt hlt))
    rw [show y₀-(y₀-Y)=Y by ring,hM,stationary_first_moment_eq_Aa Y ⟨hpos.le,hlt⟩] at heR
    rw [mul_div_cancel_right₀ _ (a_pos Y ⟨hpos.le,hlt⟩).ne'] at heR
    rw [heR]
  have ht' := ht.congr' hEq Filter.EventuallyEq.rfl
  simpa only [Function.comp_def,sub_zero,neg_sub] using ht'.neg_right

lemma A_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |A Y-(2/15:ℝ)| ≤ C*(y₀-Y) := by
  have hA0 : A y₀=(2/15:ℝ) := by norm_num [A,barH]
  obtain ⟨C,δ,hC,hδ,hb⟩ := closed_left_lipschitz_of_isBigO A y₀ (2/15) hA0 A_critical_isBigO
  exact ⟨C,δ,hC,hδ,fun Y hY hsmall => hb Y hY.2 hsmall⟩
end WP.Analysis
namespace WP.Analysis
lemma log_difference_isBigO_left (f : ℝ → ℝ) (a c : ℝ) (hc : c ≠ 0)
    (hO : (fun Y => f Y-c) =O[𝓝[<] a] (fun Y => Y-a)) :
    (fun Y => Real.log (f Y)-Real.log c) =O[𝓝[<] a] (fun Y => Y-a) := by
  have ht0 : Tendsto (fun Y : ℝ => Y-a) (𝓝[<] a) (𝓝 0) := by
    simpa only [sub_self,id_eq] using
      (tendsto_id.mono_left (show 𝓝[<] a ≤ 𝓝 a from nhdsWithin_le_nhds)).sub_const a
  have hf0 := hO.trans_tendsto ht0
  have ht : Tendsto f (𝓝[<] a) (𝓝 c) := by
    simpa only [sub_add_cancel,zero_add] using hf0.add_const c
  exact ((Real.hasDerivAt_log hc).isBigO_sub.comp_tendsto ht).trans hO

lemma logA_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |Real.log (A Y)-Real.log (2/15:ℝ)| ≤ C*(y₀-Y) := by
  have hA0 : Real.log (A y₀)=Real.log (2/15:ℝ) := by congr 1;norm_num [A,barH]
  obtain ⟨C,δ,hC,hδ,hb⟩ := closed_left_lipschitz_of_isBigO (fun Y => Real.log (A Y)) y₀
    (Real.log (2/15:ℝ)) hA0 (log_difference_isBigO_left A y₀ (2/15) (by norm_num) A_critical_isBigO)
  exact ⟨C,δ,hC,hδ,fun Y hY hsmall => hb Y hY.2 hsmall⟩

lemma log_total_weight_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |Real.log (∑' l : ℕ,weight Y l)| ≤ C*(y₀-Y) := by
  have h0 : Real.log (∑' l : ℕ,weight y₀ l)=0 := by rw [total_weight_critical_value,Real.log_one]
  have hO := log_difference_isBigO_left (fun Y => ∑'l : ℕ,weight Y l) y₀ 1 one_ne_zero total_weight_critical_isBigO
  simp only [Real.log_one,sub_zero] at hO
  obtain ⟨C,δ,hC,hδ,hb⟩ := closed_left_lipschitz_of_isBigO
    (fun Y => Real.log (∑'l : ℕ,weight Y l)) y₀ 0 h0 (by simpa only [sub_zero] using hO)
  exact ⟨C,δ,hC,hδ,fun Y hY hsmall => by simpa only [sub_zero] using hb Y hY.2 hsmall⟩

lemma log_parameters_critical_lipschitz :
    ∃ C δ₀ : ℝ,0 < C ∧ 0 < δ₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀,y₀-Y ≤ δ₀ →
      |Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (∑' l : ℕ,weight Y l)| ≤ C*(y₀-Y) := by
  obtain ⟨CA,δA,hCA,hδA,hA⟩ := logA_critical_lipschitz
  obtain ⟨CT,δT,hCT,hδT,hT⟩ := log_total_weight_critical_lipschitz
  refine ⟨CA+CT,min δA δT,by positivity,lt_min hδA hδT,?_⟩
  intro Y hY hsmall
  have ha := hA Y hY (hsmall.trans (min_le_left _ _))
  have ht := hT Y hY (hsmall.trans (min_le_right _ _))
  calc
    _ ≤ CA*(y₀-Y)+CT*(y₀-Y) := add_le_add ha ht
    _ = _ := by ring
end WP.Analysis
