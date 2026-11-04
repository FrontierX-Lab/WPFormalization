import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.Intersection.CriticalHomogeneity
import WPFormalization.Marked.NormalizedModel
noncomputable section
namespace WP
open Set
lemma homogeneous_log_ratio_bound (u v C δ : ℝ) (n : ℕ)
    (hv : 0 < v) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hlo : v ≤ u) (hup : u ≤ (1+C*δ)^n*v) :
    |Real.log (u/v)| ≤ (n:ℝ)*C*δ := by
  have hu : 0 < u := hv.trans_le hlo
  have hq : 1 ≤ u/v := (le_div_iff₀ hv).2 (by simpa using hlo)
  have hqup : u/v ≤ (1+C*δ)^n := (div_le_iff₀ hv).2 hup
  have hb : 0 < 1+C*δ := by positivity
  have hl0 : 0 ≤ Real.log (u/v) := Real.log_nonneg hq
  rw [abs_of_nonneg hl0]
  calc Real.log (u/v) ≤ Real.log ((1+C*δ)^n) := Real.log_le_log (div_pos hu hv) hqup
       _ = (n:ℝ)*Real.log (1+C*δ) := Real.log_pow _ _
       _ ≤ (n:ℝ)*(C*δ) := mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos hb]) (Nat.cast_nonneg _)
       _ = _ := by ring

lemma normalizedMarkedModel_log_critical_lipschitz :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ g p : ℕ, Stable g p →
      1 ≤ complexity g p → ∀ Y ∈ Icc (0:ℝ) y₀, y₀-Y ≤ δ →
      |Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)| ≤
        C*(complexity g p:ℝ)*(y₀-Y) := by
  obtain ⟨C,δ,hC,hδ,hLip⟩ := Analysis.log_parameters_critical_lipschitz
  refine ⟨C,δ,hC,hδ,?_⟩
  intro g p hs hhN Y hY hsmall
  have hh : (1:ℝ) ≤ complexity g p := by exact_mod_cast hhN
  have hhp : (0:ℝ) < complexity g p := by linarith
  have hb : |Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (Theta Y)| ≤ C*(y₀-Y) := by
    simpa only [Theta] using hLip Y hY hsmall
  rw [normalizedMarkedModel_log_difference g p hs Y hY]
  calc _ ≤ |(1/2-(complexity g p:ℝ))*(Real.log (A Y)-Real.log (2/15:ℝ))|+|(1/2:ℝ)*Real.log (Theta Y)| := abs_add_le _ _
       _ = ((complexity g p:ℝ)-1/2)*|Real.log (A Y)-Real.log (2/15:ℝ)|+(1/2:ℝ)*|Real.log (Theta Y)| := by
         rw [abs_mul,abs_of_neg (by linarith : 1/2-(complexity g p:ℝ)<0),abs_mul]
         norm_num
       _ ≤ (complexity g p:ℝ)*(|Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (Theta Y)|) := by
         have h₁ := mul_le_mul_of_nonneg_right (show (complexity g p:ℝ)-1/2 ≤ complexity g p by linarith)
           (abs_nonneg (Real.log (A Y)-Real.log (2/15:ℝ)))
         have h₂ := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ complexity g p by linarith) (abs_nonneg (Real.log (Theta Y)))
         nlinarith
       _ ≤ (complexity g p:ℝ)*(C*(y₀-Y)) := mul_le_mul_of_nonneg_left hb hhp.le
       _ = _ := by ring

lemma prefactorLogError_sub_endpoint_log_identity (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    prefactorLogError P g p Y-Real.log (HigherOrder.exactEndpoint P g p)=
      Real.log (normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀)-
        (Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)) := by
  have hUc : 0 < normalized P g (List.replicate p 0) y₀ := by
    have hw := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
    rw [W] at hw
    exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hw
  have hUy : 0 < normalized P g (List.replicate p 0) Y := by
    have hw := W_pos P g p hp hs Y ⟨hY.1,hY.2.le⟩
    rw [W] at hw
    exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hw
  have hNc := normalizedMarkedModel_pos g p hs y₀ ⟨y₀_pos.le,le_rfl⟩
  have hNy := normalizedMarkedModel_pos g p hs Y ⟨hY.1,hY.2.le⟩
  have hf : Real.pi*markedF P g p (XR Y)/markedModel g p Y=
      Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
    simpa only [←mul_div_assoc] using congrArg (fun x : ℝ => Real.pi*x) (markedF_div_model_eq_normalized P g p hs Y hY)
  rw [prefactorLogError,hf,exactEndpoint_eq_normalizedMarkedModel,
    Real.log_div (mul_pos Real.pi_pos hUy).ne' hNy.ne',
    Real.log_div (mul_pos Real.pi_pos hUc).ne' hNc.ne',
    Real.log_mul Real.pi_pos.ne' hUy.ne',Real.log_mul Real.pi_pos.ne' hUc.ne',
    Real.log_div hUy.ne' hUc.ne']
  ring

lemma prefactor_log_critical_uniform_anchor :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ P : PsiTheory, ∀ g p : ℕ,
      1 ≤ p → Stable g p → 1 ≤ complexity g p →
      ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ δ →
      |prefactorLogError P g p Y-Real.log (HigherOrder.exactEndpoint P g p)| ≤
        C*(complexity g p:ℝ)*(y₀-Y) := by
  obtain ⟨Cu,δu,hCu,hδu,hcomp⟩ := normalized_critical_neighborhood_comparison
  obtain ⟨Cn,δn,hCn,hδn,hmodel⟩ := normalizedMarkedModel_log_critical_lipschitz
  refine ⟨Cu+Cn,min δu δn,by positivity,lt_min hδu hδn,?_⟩
  intro P g p hp hs hhN Y hY hsmall
  have hYc : Y ∈ Icc (0:ℝ) y₀ := ⟨hY.1,hY.2.le⟩
  have hUc : 0 < normalized P g (List.replicate p 0) y₀ := by
    have hw := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
    rw [W] at hw
    exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hw
  have hc := hcomp P g (List.replicate p 0) (by simpa using hp) Y hYc (hsmall.trans (min_le_left _ _))
  have hlog := homogeneous_log_ratio_bound _ _ Cu (y₀-Y) (complexity g p) hUc hCu.le
    (sub_nonneg.mpr hY.2.le) hc.1 (by simpa only [List.length_replicate] using hc.2)
  have hm := hmodel g p hs hhN Y hYc (hsmall.trans (min_le_right _ _))
  rw [prefactorLogError_sub_endpoint_log_identity P g p hp hs Y hY]
  calc _ ≤ |Real.log (normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀)|+
      |Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)| := abs_sub _ _
       _ ≤ (complexity g p:ℝ)*Cu*(y₀-Y)+Cn*(complexity g p:ℝ)*(y₀-Y) := add_le_add hlog hm
       _ = _ := by ring
end WP
