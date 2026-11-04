import WPFormalization.Statements.Volumes
import WPFormalization.Analysis.ParameterInverse
import WPFormalization.Analysis.HarmonicProbability

/-! The exact extraction factorization of the actual marked model. Positivity of
the action, the normalized H kernel and the canonical weight mass justifies
the logarithms and the normalization at zero for every genus and marking. -/
noncomputable section
namespace WP.Analysis
open Set
lemma marked_Z_pos (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < Z Y := by
  rw [(kernel_action_moments Y hY).2.2]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (action_pos Y hY)
lemma marked_A_pos (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 < A Y := by
  unfold A
  exact div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
lemma marked_Theta_pos (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 < Theta Y := by
  have h := (Analysis.weight_hasSum_at_one Y hY).summable.le_tsum 0
    (fun j _ => weight_nonneg Y hY j)
  have h0 : weight Y 0 = 1 := by simp [weight,Analysis.theta_zero_closed Y hY]
  rw [h0] at h
  exact lt_of_lt_of_le zero_lt_one h
lemma marked_amplitude_pos (p : ℕ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    0 < Real.rpow (r Y) ((p : ℝ)/2)*Real.sqrt (A Y*Theta Y) := by
  exact mul_pos (Real.rpow_pos_of_pos (r_pos Y hY) _)
    (Real.sqrt_pos.mpr (mul_pos (marked_A_pos Y ⟨hY.1,hY.2.le⟩)
      (marked_Theta_pos Y ⟨hY.1,hY.2.le⟩)))
lemma nat_power_log_factorization (c z₀ z x₀ x : ℝ) (h : ℕ)
    (hz₀ : 0 < z₀) (hz : 0 < z) (hx₀ : x₀ ≠ 0) :
    c*z⁻¹^h*x = (c*z₀⁻¹^h*x₀)*Real.exp ((h:ℝ)*Real.log (z₀/z))*(x/x₀) := by
  rw [Real.exp_nat_mul,Real.exp_log (div_pos hz₀ hz),div_pow]
  simp only [inv_pow]
  field_simp [hz₀.ne',hz.ne',hx₀]
lemma extraction_factorization_proof (g p : ℕ) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    markedModel g p Y = markedModel g p 0 *
      Real.exp (complexity g p*extractionS (XR Y))*extractionB p (XR Y) := by
  have h0 : (0:ℝ) ∈ Ico 0 y₀ := ⟨le_rfl,y₀_pos⟩
  have hinv : inverseY (XR Y) = Y := Analysis.inverseY_eq_of_root _ _ hY.2.le rfl
  simp only [extractionS,extractionB,hinv]
  have he := nat_power_log_factorization
    (Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p))
    (Z 0) (Z Y)
    (Real.rpow (r 0) ((p:ℝ)/2)*Real.sqrt (A 0*Theta 0))
    (Real.rpow (r Y) ((p:ℝ)/2)*Real.sqrt (A Y*Theta Y))
    (complexity g p) (marked_Z_pos 0 h0) (marked_Z_pos Y hY) (marked_amplitude_pos p 0 h0).ne'
  simpa only [markedModel,mul_assoc] using he
end WP.Analysis
