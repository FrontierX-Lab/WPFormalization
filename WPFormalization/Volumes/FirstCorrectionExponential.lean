import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.HigherOrder.SecondProfile
/-! The actual first relative correction follows from a uniform corrected logarithmic error and a bounded true integral coefficient. -/
noncomputable section
namespace WP
open Set
lemma first_correction_of_log_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hL : ∃ M : ℝ, 0 < M ∧ ∀ Y ∈ Ico (0:ℝ) y₀,
      |HigherOrder.firstMarkedCorrection p Y| ≤ M)
    (hf : ∃ E : ℝ, 0 < E ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      |prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)| ≤
        E*Real.log ((g:ℝ)+1)/(g:ℝ)^2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
        (1+HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ))| ≤
        C*Real.log (g+1)/(g:ℝ)^2 := by
  obtain ⟨M,hM,hL⟩ := hL
  obtain ⟨E,hE,G,hf⟩ := hf
  obtain ⟨N,hN⟩ := exists_nat_gt (M+E)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : ℝ := E+(M+E)^2/Real.log 2
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨K,hK,G+N+2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := by omega
  have hg1R : (1:ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hg0 : 0 < (g:ℝ) := by linarith
  have hs : Stable g p := by unfold Stable;omega
  have hgh : (g:ℝ) ≤ complexity g p := by exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)
  have hh : 0 < (complexity g p:ℝ) := hg0.trans_le hgh
  have hlog : Real.log ((g:ℝ)+1) ≤ g := by
    have he := Real.log_le_sub_one_of_pos (by positivity : 0 < (g:ℝ)+1)
    linarith
  have hloglower : Real.log 2 ≤ Real.log ((g:ℝ)+1) := Real.log_le_log (by norm_num) (by linarith)
  have herror := hf g (by omega) Y hY
  have he1 : |prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)| ≤ E/g := by
    apply herror.trans
    calc
      _ ≤ E*(g:ℝ)/(g:ℝ)^2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hE.le) (sq_nonneg _)
      _ = _ := by field_simp
  have hL1 : |HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)| ≤ M/g := by
    rw [abs_div,abs_of_pos hh]
    exact (div_le_div_of_nonneg_right (hL Y hY) hh.le).trans
      (div_le_div_of_nonneg_left hM.le hg0 hgh)
  have hfb : |prefactorLogError P g p Y| ≤ (M+E)/g := by
    calc
      _ ≤ |prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)|+
          |HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)| := by
        simpa only [sub_zero] using
          (abs_sub_le (prefactorLogError P g p Y)
            (HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)) 0)
      _ ≤ E/g+M/g := add_le_add he1 hL1
      _ = _ := by ring
  have hsmall : |prefactorLogError P g p Y| ≤ 1 := hfb.trans
    ((div_le_one hg0).2 (hN.le.trans (by exact_mod_cast (show N ≤ g by omega))))
  have hexp : |Real.exp (prefactorLogError P g p Y)-1-prefactorLogError P g p Y| ≤
      (M+E)^2/(g:ℝ)^2 := by
    have he := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hsmall)
    have he' : |Real.exp (prefactorLogError P g p Y)-1-prefactorLogError P g p Y| ≤
        |prefactorLogError P g p Y|^2 := by simpa only [Real.norm_eq_abs] using he
    exact he'.trans (by simpa only [div_pow] using pow_le_pow_left₀ (abs_nonneg _) hfb 2)
  have hR : 0 < Real.pi*markedF P g p (XR Y)/markedModel g p Y :=
    div_pos (mul_pos Real.pi_pos (markedF_pos_parameter P g p hp hs Y hY))
      (markedModel_pos_parameter g p hs Y hY)
  have hEq : Real.exp (prefactorLogError P g p Y)=Real.pi*markedF P g p (XR Y)/markedModel g p Y :=
    Real.exp_log hR
  have hratio : |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
      (1+HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ))| ≤
      (M+E)^2/(g:ℝ)^2+E*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
    rw [←hEq]
    have heq : Real.exp (prefactorLogError P g p Y)-
        (1+HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ))=
        (Real.exp (prefactorLogError P g p Y)-1-prefactorLogError P g p Y)+
          (prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hexp herror)
  apply hratio.trans
  change (M+E)^2/(g:ℝ)^2+E*Real.log ((g:ℝ)+1)/(g:ℝ)^2 ≤
    K*Real.log ((g:ℝ)+1)/(g:ℝ)^2
  have hscale : (M+E)^2 ≤ ((M+E)^2/Real.log 2)*Real.log ((g:ℝ)+1) := by
    calc
      _ = ((M+E)^2/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hloglower (by positivity)
  have he := div_le_div_of_nonneg_right hscale (sq_nonneg (g:ℝ))
  calc
    _ ≤ (((M+E)^2/Real.log 2)*Real.log ((g:ℝ)+1))/(g:ℝ)^2+
        E*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := add_le_add he le_rfl
    _ = _ := by dsimp [K];ring
end WP
