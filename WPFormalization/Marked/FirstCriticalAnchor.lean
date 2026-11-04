import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.HigherOrder.PureEndpointFirstOrder
import WPFormalization.Marked.CriticalCubicWindow

/-! The actual first endpoint correction anchors the cubic critical window.
All U/N comparison and endpoint inputs are instantiated in this proof. -/
noncomputable section
namespace WP
open Set
lemma normalized_critical_first_anchor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^3 →
      |Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y-
        (1+HigherOrder.firstEndpointConstant p/(complexity g p:ℝ))| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨Cu,δ,hCu,hδ,Gu,hU⟩ := normalized_zero_critical_cubic_window_error P p hp
  obtain ⟨Cn,hCn,Gn,hN⟩ := normalizedMarkedModel_cubic_critical_window p
  obtain ⟨Ce,hCe,Ge,hGe,hE⟩ := HigherOrder.exactEndpoint_first_error P p
  obtain ⟨N,hNδ⟩ := exists_nat_gt (1/δ)
  let t : ℝ := HigherOrder.firstEndpointConstant p
  let M : ℝ := (1+|t|+|(0:ℝ)|)^2+4*(1+|t|+|(0:ℝ)|)*(Ce+Cu)+(Ce+Cu)^2
  let K : ℝ := (1+|t|+|(0:ℝ)|)^2+4*(1+|t|+|(0:ℝ)|)*(M+Cn)+(M+Cn)^2
  have hM : 0 < M := by dsimp [M];positivity
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨K,hK,Gu+Gn+Ge+N+2,?_⟩
  intro g hg Y hY hsmall
  have hg2 : 2 ≤ g := by omega
  have hs : Stable g p := by unfold Stable;omega
  let h : ℝ := complexity g p
  have hgh : g ≤ complexity g p := by unfold complexity;omega
  have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1 ≤ complexity g p by omega)
  have hh : 0 < h := by linarith
  have hlarge : 1/δ ≤ h := hNδ.le.trans (by dsimp [h];exact_mod_cast (show N ≤ complexity g p by omega))
  have hscale : 1/h^3 ≤ δ := by
    have hpow : h ≤ h^3 := by nlinarith [sq_nonneg (h-1),mul_nonneg (sub_nonneg.mpr hh1) (sq_nonneg h)]
    have hinv : 1/h ≤ δ := by
      apply (div_le_iff₀ hh).2
      have hi := (div_le_iff₀ hδ).mp hlarge
      nlinarith
    exact (div_le_div_of_nonneg_left (by norm_num) hh hpow).trans hinv
  have hu := hU g (by omega) Y hY (hsmall.trans hscale) hsmall
  have hn := (hN g (by omega) Y hY hsmall).2
  have he := hE g (by omega)
  have hprod := Analysis.unit_first_order_product t 0
    (HigherOrder.exactEndpoint P g p)
    (normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀)
    Ce Cu h hCe.le hCu.le hh1 he (by simpa using hu)
  have hprod' : |HigherOrder.exactEndpoint P g p*
      (normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀)-
      (1+t/h)| ≤ M/h^2 := by simpa only [add_zero] using hprod
  have hall := Analysis.unit_first_order_product t 0
    (HigherOrder.exactEndpoint P g p*(normalized P g (List.replicate p 0) Y/
      normalized P g (List.replicate p 0) y₀))
    (normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y)
    M Cn h hM.le hCn.le hh1 hprod' (by simpa using hn)
  have hW := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
  have hUc : normalized P g (List.replicate p 0) y₀ ≠ 0 := by
    rw [W] at hW
    exact ((mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hW).ne'
  have hNc := (normalizedMarkedModel_pos g p hs y₀ ⟨y₀_pos.le,le_rfl⟩).ne'
  have hNy := (normalizedMarkedModel_pos g p hs Y hY).ne'
  have hid : HigherOrder.exactEndpoint P g p*(normalized P g (List.replicate p 0) Y/
      normalized P g (List.replicate p 0) y₀)*(normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y)=
      Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
    rw [HigherOrder.exactEndpoint,←normalizedMarkedModel_critical]
    field_simp [hUc,hNc,hNy]
  simpa only [hid,add_zero] using hall
end WP

namespace WP
open Set
lemma marked_prefactor_critical_first_relative (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^3 →
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
        (1+HigherOrder.firstEndpointConstant p/(complexity g p:ℝ))| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,G,hA⟩ := normalized_critical_first_anchor P p hp
  refine ⟨C,hC,G+2,?_⟩
  intro g hg Y hY hsmall
  have hs : Stable g p := by unfold Stable;omega
  have he : Real.pi*markedF P g p (XR Y)/markedModel g p Y=
      Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
    simpa only [←mul_div_assoc] using congrArg (fun x : ℝ => Real.pi*x)
      (markedF_div_model_eq_normalized P g p hs Y hY)
  rw [he]
  exact hA g (by omega) Y ⟨hY.1,hY.2.le⟩ hsmall
lemma prefactor_log_critical_first_anchor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^3 →
      |prefactorLogError P g p Y-HigherOrder.firstEndpointConstant p/(complexity g p:ℝ)| ≤ C/(g:ℝ)^2 := by
  obtain ⟨C,hC,G,hA⟩ := marked_prefactor_critical_first_relative P p hp
  let t : ℝ := HigherOrder.firstEndpointConstant p
  let D : ℝ := 2*(|t|+C)^2+C
  have hD : 0 < D := by dsimp [D];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(|t|+C))
  refine ⟨D,hD,G+N+2,?_⟩
  intro g hg Y hY hsmall
  have hh : 1 ≤ (complexity g p:ℝ) := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hlarge : 2*(|t|+C) ≤ (complexity g p:ℝ) :=
    hN.le.trans (by exact_mod_cast (show N ≤ complexity g p by unfold complexity;omega))
  have he := Analysis.log_unit_first_order_error
    (Real.pi*markedF P g p (XR Y)/markedModel g p Y) t C (complexity g p:ℝ)
    hC.le hh hlarge (hA g (by omega) Y hY hsmall)
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hgh : (g:ℝ) ≤ complexity g p := by exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)
  unfold prefactorLogError
  exact he.trans (div_le_div_of_nonneg_left hD.le (sq_pos_of_pos hgR)
    (pow_le_pow_left₀ hgR.le hgh 2))
end WP
