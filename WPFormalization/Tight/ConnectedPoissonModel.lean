import WPFormalization.Tight.ConnectedGenusRatio
import WPFormalization.Tight.ConnectedScale
import WPFormalization.Volumes.ExtractionPhaseOrigin
import WPFormalization.Volumes.ExtractionAmplitude
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_complexity_tendsto (gs : ℕ → ℕ) (hg : Tendsto gs atTop atTop) :
    Tendsto (fun j => (complexity (gs j) 0 : ℝ)) atTop atTop := by
  have he : (fun j => (complexity (gs j) 0 : ℝ)) =ᶠ[atTop]
      (fun j => 2 * (gs j : ℝ) - 2) := by
    filter_upwards [hg.eventually_ge_atTop 2] with j hj
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have ht := tendsto_atTop_add_const_right atTop (-2:ℝ)
    ((tendsto_natCast_atTop_atTop.comp hg).const_mul_atTop (by norm_num : (0:ℝ)<2))
  have ht' : Tendsto (fun j => 2*(gs j:ℝ)-2) atTop atTop := by
    simpa only [sub_eq_add_neg,Function.comp_def] using ht
  exact ht'.congr' he.symm

lemma connected_small_weight_tendsto (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop)
    (c : ℝ) : Tendsto (fun j => c / hs j) atTop (𝓝 0) :=
  hh.const_div_atTop c

lemma connected_small_weight_eventually (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop)
    (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ j in atTop, c / hs j ∈ Ico (0:ℝ) xCritical := by
  filter_upwards [hh.eventually_gt_atTop 0,
    (connected_small_weight_tendsto hs hh c).eventually
      (eventually_lt_nhds Analysis.xCritical_pos_parameter)] with j hj hsmall
  exact ⟨div_nonneg hc hj.le, hsmall⟩

lemma connected_scaled_differentiable_limit (f : ℝ → ℝ) (d : ℝ)
    (hf : HasDerivAt f d 0) (hf0 : f 0 = 0)
    (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun j => hs j * f (c / hs j)) atTop (𝓝 (c*d)) := by
  by_cases hcz : c = 0
  · subst c
    simpa [hf0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
  have hx : Tendsto (fun j => c / hs j) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨connected_small_weight_tendsto hs hh c, ?_⟩
    filter_upwards [hh.eventually_gt_atTop 0] with j hj
    exact div_pos hcpos hj
  have ht := (hf.tendsto_slope_zero_right.comp hx).const_mul c
  simp only [zero_add, hf0, sub_zero, smul_eq_mul] at ht
  apply ht.congr'
  filter_upwards [hh.eventually_gt_atTop 0] with j hj
  change c * ((c / hs j)⁻¹ * f (c / hs j)) = hs j * f (c / hs j)
  field_simp [hcz,hj.ne']

lemma connected_extraction_phase_poisson_limit (hs : ℕ → ℝ)
    (hh : Tendsto hs atTop atTop) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun j => hs j * extractionS (c / hs j)) atTop (𝓝 (2*c)) := by
  obtain ⟨S,hS,hS0,hSd,htrace⟩ := Analysis.exists_extractionS_origin_complex_extension
  let f : ℝ → ℝ := fun x => (S (x:ℂ)).re
  have hd : HasDerivAt f 2 0 := by
    simpa [f,hSd] using
      hS.differentiableAt.hasDerivAt.real_of_complex
  have hf0 : f 0 = 0 := by simp [f,hS0]
  have ht := connected_scaled_differentiable_limit f 2 hd hf0 hs hh c hc
  have hx := connected_small_weight_tendsto hs hh c
  have he : (fun j => hs j * f (c / hs j)) =ᶠ[atTop]
      (fun j => hs j * extractionS (c / hs j)) := by
    filter_upwards [hx.eventually htrace, hh.eventually_gt_atTop 0] with j hj hjpos
    congr 1
    exact congrArg Complex.re (hj (div_nonneg hc hjpos.le))
  simpa only [mul_comm c 2] using ht.congr' he

lemma connected_extraction_amplitude_poisson_limit (P : PsiTheory) (p : ℕ)
    (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun j => extractionB p (c / hs j)) atTop (𝓝 1) := by
  obtain ⟨B,hB0,hB⟩ := Analysis.extractionB_complex_extension P p
  have ha : AnalyticAt ℂ B 0 := by
    simpa only [Complex.ofReal_zero] using (hB 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩).1
  have hx := connected_small_weight_tendsto hs hh c
  have hz : Tendsto (fun j => ((c / hs j : ℝ):ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (ha.continuousAt.tendsto.comp hz)
  simp only [hB0,Complex.one_re] at ht
  apply ht.congr'
  filter_upwards [connected_small_weight_eventually hs hh c hc] with j hj
  change (B ((c / hs j:ℝ):ℂ)).re = extractionB p (c / hs j)
  rw [(hB _ hj).2,Complex.ofReal_re]

lemma connected_marked_model_poisson_limit (P : PsiTheory) (p : ℕ)
    (gs : ℕ → ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop)
    (hch : Tendsto (fun j => (complexity (gs j) p : ℝ) / hs j) atTop (𝓝 1))
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun j => markedModel (gs j) p (inverseY (c / hs j)) /
      markedModel (gs j) p 0) atTop (𝓝 (Real.exp (2*c))) := by
  have hphase := hch.mul (connected_extraction_phase_poisson_limit hs hh c hc)
  simp only [one_mul] at hphase
  have hexp : Tendsto (fun j => Real.exp ((complexity (gs j) p : ℝ) * extractionS (c / hs j)))
      atTop (𝓝 (Real.exp (2*c))) := by
    apply (Real.continuous_exp.continuousAt.tendsto.comp hphase).congr'
    filter_upwards [hh.eventually_gt_atTop 0] with j hj
    change Real.exp (((complexity (gs j) p:ℝ)/hs j)*(hs j*extractionS (c/hs j))) = _
    congr 1
    field_simp [hj.ne']
  have ht := hexp.mul (connected_extraction_amplitude_poisson_limit P p hs hh c hc)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hg.eventually_ge_atTop 2,
    connected_small_weight_eventually hs hh c hc] with j hj hx
  have hb := inverseY_branch _ hx
  have hm : markedModel (gs j) p 0 ≠ 0 :=
    (markedModel_pos_parameter _ _ (by unfold Stable;omega) 0 ⟨le_rfl,y₀_pos⟩).ne'
  rw [Analysis.extraction_factorization_proof (gs j) p _ hb.1,hb.2]
  field_simp

lemma connected_marked_leading_tendsto (P : PsiTheory) (p : ℕ)
    (gs : ℕ → ℕ) (hg : Tendsto gs atTop atTop) (Ys : ℕ → ℝ)
    (hY : ∀ᶠ j in atTop, Ys j ∈ Ico (0:ℝ) y₀) :
    Tendsto (fun j => Real.pi * markedF P (gs j) p (XR (Ys j)) /
      markedModel (gs j) p (Ys j)) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hbound⟩ := connected_marked_leading_relative_error P p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun j => norm_nonneg _)) _
    ((tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C)
  filter_upwards [hg.eventually_ge_atTop G,hY] with j hj hy
  simpa only [Real.norm_eq_abs,Function.comp_def] using hbound (gs j) hj (Ys j) hy

lemma connected_marked_normalized_poisson_limit (P : PsiTheory) (p : ℕ)
    (gs : ℕ → ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop)
    (hch : Tendsto (fun j => (complexity (gs j) p : ℝ) / hs j) atTop (𝓝 1))
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun j => markedF P (gs j) p (c / hs j) /
      markedF P (gs j) p 0) atTop (𝓝 (Real.exp (2*c))) := by
  have hY : ∀ᶠ j in atTop, inverseY (c / hs j) ∈ Ico (0:ℝ) y₀ :=
    (connected_small_weight_eventually hs hh c hc).mono (fun _ hj => (inverseY_branch _ hj).1)
  have hxroot : ∀ᶠ j in atTop, XR (inverseY (c / hs j)) = c / hs j :=
    (connected_small_weight_eventually hs hh c hc).mono (fun _ hj => (inverseY_branch _ hj).2)
  have ha := connected_marked_leading_tendsto P p gs hg (fun j => inverseY (c / hs j)) hY
  have hb := connected_marked_leading_tendsto P p gs hg (fun _ => 0)
    (Eventually.of_forall (fun _ => ⟨le_rfl,y₀_pos⟩))
  simp only [XR_zero] at hb
  have ht := (ha.div hb (by norm_num : (1:ℝ) ≠ 0)).mul
    (connected_marked_model_poisson_limit P p gs hg hs hh hch c hc)
  simp only [div_self (by norm_num : (1:ℝ)≠0),one_mul] at ht
  apply ht.congr'
  filter_upwards [hg.eventually_ge_atTop 2,hY,hxroot,
    hb.eventually_ne (by norm_num : (1:ℝ)≠0)] with j hj hy hx hbn
  have hM : markedModel (gs j) p (inverseY (c / hs j)) ≠ 0 :=
    (markedModel_pos_parameter _ _ (by unfold Stable;omega) _ hy).ne'
  have hM0 : markedModel (gs j) p 0 ≠ 0 :=
    (markedModel_pos_parameter _ _ (by unfold Stable;omega) 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hF0 : markedF P (gs j) p 0 ≠ 0 := by
    intro he
    simp only [he,mul_zero,zero_div] at hbn
    exact hbn rfl
  change ((Real.pi * markedF P (gs j) p (XR (inverseY (c/hs j))) /
    markedModel (gs j) p (inverseY (c/hs j))) /
    (Real.pi * markedF P (gs j) p 0 / markedModel (gs j) p 0)) *
    (markedModel (gs j) p (inverseY (c/hs j))/markedModel (gs j) p 0) = _
  rw [hx]
  field_simp [hM,hM0,hF0,Real.pi_ne_zero]

lemma connected_marked_poisson_pgf_limit (P : PsiTheory) (p : ℕ)
    (gs : ℕ → ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ → ℝ) (hh : Tendsto hs atTop atTop)
    (hch : Tendsto (fun j => (complexity (gs j) p : ℝ) / hs j) atTop (𝓝 1))
    (c : ℝ) (hc : 0 < c) (z : ℝ) (hz : 0 ≤ z) :
    Tendsto (fun j => markedF P (gs j) p ((c / hs j)*z) /
      markedF P (gs j) p (c / hs j)) atTop (𝓝 (Real.exp (2*c*(z-1)))) := by
  have ht := (connected_marked_normalized_poisson_limit P p gs hg hs hh hch (c*z)
    (mul_nonneg hc.le hz)).div
      (connected_marked_normalized_poisson_limit P p gs hg hs hh hch c hc.le)
      (Real.exp_pos _).ne'
  rw [←Real.exp_sub,show 2*(c*z)-2*c=2*c*(z-1) by ring] at ht
  apply ht.congr'
  filter_upwards [hg.eventually_ge_atTop 2,
    (connected_marked_leading_tendsto P p gs hg (fun _ => 0)
      (Eventually.of_forall (fun _ => ⟨le_rfl,y₀_pos⟩))).eventually_ne
        (by norm_num : (1:ℝ)≠0)] with j hj hf0
  have hF0 : markedF P (gs j) p 0 ≠ 0 := by
    intro he
    simp only [XR_zero,he,mul_zero,zero_div] at hf0
    exact hf0 rfl
  change (markedF P (gs j) p (c*z/hs j)/markedF P (gs j) p 0) /
    (markedF P (gs j) p (c/hs j)/markedF P (gs j) p 0) = _
  rw [show c*z/hs j=(c/hs j)*z by ring]
  exact div_div_div_cancel_right₀ hF0 _ _

end WP.TightConnected
