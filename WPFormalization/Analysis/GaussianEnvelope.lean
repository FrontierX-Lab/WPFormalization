import Mathlib
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
noncomputable def gaussianErrorEnvelope (C β γ:ℝ)(h:ℕ)(t:ℝ) : ℝ :=
  min (C*|t|^3/Real.sqrt (h:ℝ)) (Real.exp (-β*t^2)+Real.exp (-γ*t^2))
lemma gaussianErrorEnvelope_nonneg (C β γ:ℝ)(hC:0≤C)(h:ℕ)(t:ℝ) : 0≤gaussianErrorEnvelope C β γ h t := by
  dsimp [gaussianErrorEnvelope]
  apply le_min
  · exact div_nonneg (mul_nonneg hC (by positivity)) (Real.sqrt_nonneg _)
  · positivity
lemma gaussianErrorEnvelope_bound (C β γ:ℝ)(hC:0≤C)(h:ℕ)(t:ℝ) :
    ‖gaussianErrorEnvelope C β γ h t‖≤Real.exp (-β*t^2)+Real.exp (-γ*t^2) := by
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianErrorEnvelope_nonneg C β γ hC h t)]
  exact min_le_right _ _
lemma gaussianErrorEnvelope_integrable (C β γ:ℝ)(hC:0≤C)(hβ:0<β)(hγ:0<γ)(h:ℕ) :
    Integrable (gaussianErrorEnvelope C β γ h) volume := by
  apply ((integrable_exp_neg_mul_sq hβ).add (integrable_exp_neg_mul_sq hγ)).mono'
  · apply Continuous.aestronglyMeasurable
    change Continuous (fun t:ℝ=>min (C*|t|^3/Real.sqrt (h:ℝ)) (Real.exp (-β*t^2)+Real.exp (-γ*t^2)))
    fun_prop
  · exact ae_of_all _ (gaussianErrorEnvelope_bound C β γ hC h)
lemma gaussianErrorEnvelope_integral_tendsto (C β γ:ℝ)(hC:0≤C)(hβ:0<β)(hγ:0<γ) :
    Tendsto (fun h:ℕ=>∫t:ℝ,gaussianErrorEnvelope C β γ h t) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun h:ℕ=>Real.sqrt (h:ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim (t:ℝ) : Tendsto (fun h:ℕ=>gaussianErrorEnvelope C β γ h t) atTop (𝓝 0) := by
    have h := (hsqrt.const_div_atTop (C*|t|^3)).min (tendsto_const_nhds (x:=Real.exp (-β*t^2)+Real.exp (-γ*t^2)))
    have hg : 0≤Real.exp (-β*t^2)+Real.exp (-γ*t^2) := by positivity
    simpa only [gaussianErrorEnvelope,min_eq_left hg] using h
  have hi := tendsto_integral_of_dominated_convergence (fun t:ℝ=>Real.exp (-β*t^2)+Real.exp (-γ*t^2))
    (fun h=>(gaussianErrorEnvelope_integrable C β γ hC hβ hγ h).aestronglyMeasurable)
    ((integrable_exp_neg_mul_sq hβ).add (integrable_exp_neg_mul_sq hγ))
    (fun h=>ae_of_all _ (gaussianErrorEnvelope_bound C β γ hC h)) (ae_of_all _ hlim)
  simpa only [integral_zero] using hi
noncomputable def gaussianOuterTail (δ γ:ℝ)(h:ℕ)(t:ℝ) : ℝ :=
  if δ*Real.sqrt (h:ℝ)< |t| then Real.exp (-γ*t^2) else 0
lemma gaussianOuterTail_integrable (δ γ:ℝ)(hγ:0<γ)(h:ℕ) : Integrable (gaussianOuterTail δ γ h) volume := by
  apply (integrable_exp_neg_mul_sq hγ).mono'
  · have hc : AEStronglyMeasurable (fun t:ℝ=>Real.exp (-γ*t^2)) volume := by apply Continuous.aestronglyMeasurable; fun_prop
    exact hc.indicator (s := {t:ℝ | δ*Real.sqrt (h:ℝ)< |t|}) ((isOpen_lt continuous_const continuous_abs).measurableSet)
  · apply ae_of_all
    intro t
    dsimp [gaussianOuterTail]
    split_ifs <;> simp [Real.exp_nonneg]
lemma gaussianOuterTail_integral_tendsto (δ γ:ℝ)(hδ:0<δ)(hγ:0<γ) :
    Tendsto (fun h:ℕ=>∫t:ℝ,gaussianOuterTail δ γ h t) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun h:ℕ=>δ*Real.sqrt (h:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim (t:ℝ) : Tendsto (fun h:ℕ=>gaussianOuterTail δ γ h t) atTop (𝓝 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hsqrt.eventually (eventually_ge_atTop |t|)] with h hh
    simp only [gaussianOuterTail,not_lt.mpr hh,if_false]
  have hi := tendsto_integral_of_dominated_convergence (fun t:ℝ=>Real.exp (-γ*t^2))
    (fun h=>(gaussianOuterTail_integrable δ γ hγ h).aestronglyMeasurable)
    (integrable_exp_neg_mul_sq hγ)
    (fun h=>ae_of_all _ (fun t=>by
      dsimp [gaussianOuterTail]
      split_ifs <;> simp [Real.exp_nonneg])) (ae_of_all _ hlim)
  simpa only [integral_zero] using hi
lemma sqrt_mul_geometric_tendsto (ρ:ℝ)(hρ:0≤ρ)(hρ1:ρ<1) :
    Tendsto (fun h:ℕ=>Real.sqrt (h:ℝ)*ρ^h) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hρ hρ1).add (tendsto_pow_const_mul_const_pow_of_lt_one 0 hρ hρ1)
  have hlim' : Tendsto (fun h:ℕ=>((h:ℝ)+1)*ρ^h) atTop (𝓝 0) := by
    simpa only [pow_one,pow_zero,one_mul,add_mul,zero_add] using hlim
  apply squeeze_zero (fun h=>mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hρ h)) _ hlim'
  intro h
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ h)
  have hs := Real.sq_sqrt (show (0:ℝ)≤h by positivity)
  nlinarith [sq_nonneg (Real.sqrt (h:ℝ)-1/2)]
end WP.Analysis
