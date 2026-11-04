import WPFormalization.Analysis.ZCriticalScale
import WPFormalization.Analysis.CriticalCuspCoordinates
import WPFormalization.Volumes.CriticalKernelUnits

/-! Actual differentiable critical units for the cusp gap and full action.
The unit functions are obtained from proved X and kernel germs. No critical
remainder or action asymptotic is an input. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace WP.Analysis

lemma jt_critical_units :
    ∃ B F : ℝ → ℝ,
      DifferentiableAt ℝ B 0 ∧ DifferentiableAt ℝ F 0 ∧
      B 0 = criticalB/2 ∧
      F 0 = (2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ) ∧
      ∀ᶠ δ : ℝ in 𝓝 0, 0 < δ → δ < y₀ ∧
        xCritical-XR (y₀-δ) = δ^2*B δ ∧
        Z (y₀-δ) = Real.rpow δ (5/2:ℝ)*F δ := by
  obtain ⟨B,hB,hB0,hgap⟩ := criticalXDifference_factor
  obtain ⟨k⟩ := exists_criticalKernelUnits
  let F : ℝ → ℝ := fun δ => (k.A (δ:ℂ)).re * (k.a₁ (δ:ℂ)).re *
    Real.rpow (k.r₁ (δ:ℂ)).re (3/2:ℝ)
  have hA : DifferentiableAt ℝ (fun δ : ℝ => (k.A (δ:ℂ)).re) 0 :=
    k.A_analytic.re_ofReal.differentiableAt
  have ha : DifferentiableAt ℝ (fun δ : ℝ => (k.a₁ (δ:ℂ)).re) 0 :=
    k.a_analytic.re_ofReal.differentiableAt
  have hr : DifferentiableAt ℝ (fun δ : ℝ => (k.r₁ (δ:ℂ)).re) 0 :=
    k.r_analytic.re_ofReal.differentiableAt
  have hF : DifferentiableAt ℝ F 0 :=
    (hA.mul ha).mul (hr.rpow_const (Or.inl (by simp [k.r_zero])))
  refine ⟨B,F,hB.differentiableAt,hF,hB0,?_,?_⟩
  · simp [F,k.A_zero,k.a_zero,k.r_zero]
  filter_upwards [hgap,k.physical] with δ hgap hphys hδ
  obtain ⟨hδy,hA,ha,hr⟩ := hphys hδ
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  refine ⟨hδy,hgap,?_⟩
  have hAr : WP.A (y₀-δ) = (k.A (δ:ℂ)).re := by
    simpa only [Complex.ofReal_re] using (congrArg Complex.re hA).symm
  have har : WP.a (y₀-δ)/δ = (k.a₁ (δ:ℂ)).re := by
    have ht := congrArg Complex.re ha
    simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
    rw [ht]
    field_simp
  have hrr : WP.r (y₀-δ)/δ = (k.r₁ (δ:ℂ)).re := by
    have ht := congrArg Complex.re hr
    simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
    rw [ht]
    field_simp
  have he := normalized_action_scale_identity (WP.A (y₀-δ)) (WP.a (y₀-δ))
    (WP.r (y₀-δ)) δ hδ (r_pos _ hY)
  change Z (y₀-δ)/Real.rpow δ (5/2:ℝ) = _ at he
  rw [hAr,har,hrr] at he
  exact (div_eq_iff (Real.rpow_pos_of_pos hδ _).ne').mp he |>.trans (mul_comm _ _)

lemma jt_critical_units_left :
    ∃ B F : ℝ → ℝ,
      DifferentiableAt ℝ B 0 ∧ DifferentiableAt ℝ F 0 ∧
      B 0 = criticalB/2 ∧
      F 0 = (2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ) ∧
      ∀ᶠ Y : ℝ in 𝓝[<] y₀,
        xCritical-XR Y = (y₀-Y)^2*B (y₀-Y) ∧
        Z Y = Real.rpow (y₀-Y) (5/2:ℝ)*F (y₀-Y) := by
  obtain ⟨B,F,hB,hF,hB0,hF0,he⟩ := jt_critical_units
  refine ⟨B,F,hB,hF,hB0,hF0,?_⟩
  filter_upwards [deltaCoordinate_tendsto.eventually he,self_mem_nhdsWithin] with Y h hY
  have ht := h (sub_pos.mpr hY)
  simpa only [sub_sub_cancel] using ht.2

lemma jt_gap_relative_delta :
    (fun Y => (xCritical-XR Y)/((criticalB/2)*(y₀-Y)^2)-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y) := by
  obtain ⟨B,F,hB,hF,hB0,hF0,he⟩ := jt_critical_units_left
  have hb : criticalB/2 ≠ 0 := (div_pos criticalB_pos (by norm_num)).ne'
  have ho := (hB.div_const (criticalB/2)).hasDerivAt.isBigO_sub
  simp only [hB0,div_self hb] at ho
  have ht := ho.comp_tendsto deltaCoordinate_tendsto
  apply ht.congr' ?_ (by filter_upwards with Y; simp)
  filter_upwards [he,self_mem_nhdsWithin] with Y h hY
  dsimp only [Function.comp_def]
  rw [h.1]
  have hd : y₀-Y ≠ 0 := (sub_pos.mpr hY).ne'
  field_simp

lemma jt_action_relative_delta_unsimplified :
    (fun Y => Z Y/(((2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ))*
      Real.rpow (y₀-Y) (5/2:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y) := by
  obtain ⟨B,F,hB,hF,hB0,hF0,he⟩ := jt_critical_units_left
  let L : ℝ := (2/15:ℝ)*criticalB*Real.rpow 3 (3/2:ℝ)
  have hL : 0 < L := mul_pos (mul_pos (by norm_num) criticalB_pos)
    (Real.rpow_pos_of_pos (by norm_num) _)
  have ho := (hF.div_const L).hasDerivAt.isBigO_sub
  have hf : F 0/L=1 := by rw [hF0]; exact div_self hL.ne'
  rw [hf] at ho
  have ht := ho.comp_tendsto deltaCoordinate_tendsto
  apply ht.congr' ?_ (by filter_upwards with Y; simp)
  filter_upwards [he,self_mem_nhdsWithin] with Y h hY
  dsimp only [Function.comp_def]
  rw [h.2]
  have hd := (Real.rpow_pos_of_pos (sub_pos.mpr hY) (5/2:ℝ)).ne'
  change _ = (Real.rpow (y₀-Y) (5/2:ℝ)*F (y₀-Y))/(L*Real.rpow (y₀-Y) (5/2:ℝ))-1
  simp only [Real.rpow_eq_pow] at hd ⊢
  field_simp [hd,hL.ne']

end WP.Analysis
