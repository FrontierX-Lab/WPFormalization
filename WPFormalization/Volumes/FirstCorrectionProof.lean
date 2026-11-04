import WPFormalization.Volumes.SecondPrefactorIntegration
import WPFormalization.Marked.FirstCriticalAnchor
import WPFormalization.Volumes.FirstCorrectionExponential
import WPFormalization.Analysis.CubicWindowPatching

/-! The complete original first marked correction theorem.
The true bounded primitive, endpoint Lipschitz estimate, actual cubic-window
anchor and corrected long-interval variation are all instantiated. There are
no remaining transport, primitive, anchor or arbitrary-coefficient premises. -/
noncomputable section
namespace WP
open Set
lemma first_correction_of_primitive_bounds (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hL : ∃ M : ℝ, 0 < M ∧ ∀ Y ∈ Ico (0:ℝ) y₀,
      |HigherOrder.firstMarkedCorrection p Y| ≤ M)
    (hLip : ∃ M : ℝ, 0 < M ∧ ∀ Y ∈ Icc (0:ℝ) y₀,
      |HigherOrder.firstMarkedCorrection p Y-HigherOrder.firstEndpointConstant p| ≤ M*(y₀-Y))
    (hlong : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^3
      B ∈ Ico (0:ℝ) y₀ ∧ ∀ Y ∈ Ico (0:ℝ) y₀, Y ≤ B →
        |(prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/h)-
          (prefactorLogError P g p B-HigherOrder.firstMarkedCorrection p B/h)| ≤
          C*Real.log ((g:ℝ)+1)/(g:ℝ)^2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
        (1+HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ))| ≤
        C*Real.log (g+1)/(g:ℝ)^2 := by
  apply first_correction_of_log_error P p hp hL
  apply Analysis.cubic_window_patching p (fun g Y =>
    prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)) ?_ hlong
  obtain ⟨C,hC,G,hanchor⟩ := prefactor_log_critical_first_anchor P p hp
  obtain ⟨M,hM,hLip⟩ := hLip
  refine ⟨C+M,by positivity,G+2,?_⟩
  intro g hg Y hY hsmall
  have hg0 : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hgh : (g:ℝ) ≤ complexity g p := by exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)
  have hh1 : 1 ≤ (complexity g p:ℝ) := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hh : 0 < (complexity g p:ℝ) := by linarith
  have hpow : (complexity g p:ℝ) ≤ (complexity g p:ℝ)^3 := by
    nlinarith [sq_nonneg ((complexity g p:ℝ)-1),
      mul_nonneg (sub_nonneg.mpr hh1) (sq_nonneg (complexity g p:ℝ))]
  have hscale : y₀-Y ≤ 1/(complexity g p:ℝ) :=
    hsmall.trans (div_le_div_of_nonneg_left (by norm_num) hh hpow)
  have hcoeff : |(HigherOrder.firstEndpointConstant p-HigherOrder.firstMarkedCorrection p Y)/(complexity g p:ℝ)| ≤ M/(g:ℝ)^2 := by
    rw [abs_div,abs_of_pos hh,abs_sub_comm]
    calc
      _ ≤ (M*(y₀-Y))/(complexity g p:ℝ) :=
        div_le_div_of_nonneg_right (hLip Y ⟨hY.1,hY.2.le⟩) hh.le
      _ ≤ (M*(1/(complexity g p:ℝ)))/(complexity g p:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hM.le) hh.le
      _ = M/(complexity g p:ℝ)^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hM.le (sq_pos_of_pos hg0)
        (pow_le_pow_left₀ hg0.le hgh 2)
  have heq : prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)=
      (prefactorLogError P g p Y-HigherOrder.firstEndpointConstant p/(complexity g p:ℝ))+
      (HigherOrder.firstEndpointConstant p-HigherOrder.firstMarkedCorrection p Y)/(complexity g p:ℝ) := by ring
  rw [heq]
  calc
    _ ≤ |prefactorLogError P g p Y-HigherOrder.firstEndpointConstant p/(complexity g p:ℝ)|+
      |(HigherOrder.firstEndpointConstant p-HigherOrder.firstMarkedCorrection p Y)/(complexity g p:ℝ)| := abs_add_le _ _
    _ ≤ C/(g:ℝ)^2+M/(g:ℝ)^2 := add_le_add (hanchor g (by omega) Y hY hsmall) hcoeff
    _ = _ := by ring
end WP

namespace WP.HigherOrder
lemma first_correction_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
        (1+firstMarkedCorrection p Y/(complexity g p : ℝ))| ≤
      C*Real.log (g+1)/(g : ℝ)^2 := by
  apply WP.first_correction_of_primitive_bounds P p hp
  · obtain ⟨M,hM,hbound⟩ := firstMarkedCorrection_abs_uniform p
    exact ⟨M,hM,fun Y hY => hbound Y ⟨hY.1,hY.2.le⟩⟩
  · exact firstMarkedCorrection_endpoint_lipschitz p
  · simpa only [WP.correctedPrefactorLogError] using
      WP.corrected_prefactorLogError_long_interval P p hp
end WP.HigherOrder
