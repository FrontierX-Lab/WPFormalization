import WPFormalization.Marked.NormalizedModel
import WPFormalization.Intersection.CriticalHomogeneity
import WPFormalization.HigherOrder.PureEndpoint
import WPFormalization.Volumes.PrefactorIntegration
/-! The genuine critical anchor and the complete leading marked prefactor.
The actual homogeneous recursion, normalized model, fixed pure-psi endpoint
and transport variation are combined here. The final theorem has no
remaining window, transport or string-flow assumptions. -/
noncomputable section
open Set
namespace WP.Analysis
lemma log_relative_small_bound (x : ℝ) (hx : |x-1|≤1/2) : |Real.log x|≤2*|x-1| := by
  have hx0 : 0<x := by have := (abs_le.mp hx).1;linarith
  have hxhalf : 1/2≤x := by have := (abs_le.mp hx).1;linarith
  have hu := Real.log_le_sub_one_of_pos hx0
  have hl := Real.one_sub_inv_le_log_of_pos hx0
  have hlin : 1-x≤|x-1| := by linarith [neg_le_abs (x-1)]
  have hscale : |x-1|≤2*|x-1| * x := by
    nlinarith [mul_nonneg (abs_nonneg (x-1)) (show 0≤2*x-1 by linarith)]
  have hb : x⁻¹-1≤2*|x-1| := by
    have he : x⁻¹-1=(1-x)/x := by field_simp <;> ring
    rw [he]
    apply (div_le_iff₀ hx0).mpr
    exact hlin.trans hscale
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (x-1),abs_nonneg (x-1)]
end WP.Analysis

namespace WP
lemma normalized_critical_anchor_of_window (P : PsiTheory) (p : ℕ) (hp : 1≤p)
    (hN : ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Icc (0:ℝ) y₀,
      y₀-Y≤δ₀ → y₀-Y≤1/(complexity g p:ℝ)^2 →
      |normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y-1|≤C/(complexity g p:ℝ)) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Icc (0:ℝ) y₀,
      y₀-Y≤1/(complexity g p:ℝ)^2 →
      |Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y-1|≤C/g := by
  obtain ⟨Cu,δu,hCu,hδu,Gu,hU⟩ := normalized_zero_critical_window_error P p hp
  obtain ⟨Cn,δn,hCn,hδn,Gn,hN⟩ := hN
  obtain ⟨Ce,hCe,Ge,hGe,hE⟩ := HigherOrder.exactEndpoint_error P p
  let δ := min δu δn
  have hδ : 0<δ := lt_min hδu hδn
  obtain ⟨N,hNδ⟩ := exists_nat_gt (1/δ)
  let M := Ce+Cu+Ce*Cu
  refine ⟨M+Cn+M*Cn,by dsimp [M];positivity,Gu+Gn+Ge+N+2,?_⟩
  intro g hg Y hY hsmall
  have hg₂ : 2≤g := by omega
  have hgR : (1:ℝ)≤g := by exact_mod_cast (show 1≤g by omega)
  have hgp : 0<(g:ℝ) := by linarith
  have hs : Stable g p := by unfold Stable;omega
  have hgh : g≤complexity g p := by unfold complexity;omega
  have hhr : (g:ℝ)≤(complexity g p:ℝ) := by exact_mod_cast hgh
  have hh : 0<(complexity g p:ℝ) := hgp.trans_le hhr
  have hh1 : 1≤(complexity g p:ℝ) := hgR.trans hhr
  have hlarge : 1/δ≤(complexity g p:ℝ) :=
    hNδ.le.trans (by exact_mod_cast (show N≤complexity g p by omega))
  have hscale : 1/(complexity g p:ℝ)^2≤δ := by
    have hh2 : (complexity g p:ℝ)≤(complexity g p:ℝ)^2 := by nlinarith
    have hx : 1/(complexity g p:ℝ)≤δ := by
      apply (div_le_iff₀ hh).mpr
      have := (div_le_iff₀ hδ).mp hlarge
      nlinarith
    exact (div_le_div_of_nonneg_left (by norm_num) hh hh2).trans hx
  have hu := hU g (by omega) Y hY
    (hsmall.trans (hscale.trans (min_le_left _ _))) hsmall
  have hn := hN g (by omega) Y hY
    (hsmall.trans (hscale.trans (min_le_right _ _))) hsmall
  have hu' : |normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀-1|≤Cu/g :=
    hu.trans (div_le_div_of_nonneg_left hCu.le hgp hhr)
  have hn' : |normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y-1|≤Cn/g :=
    hn.trans (div_le_div_of_nonneg_left hCn.le hgp hhr)
  have he := hE g (by omega)
  have hprod := HigherOrder.product_relative_error
    (HigherOrder.exactEndpoint P g p)
    (normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀)
    Ce Cu g hgR hCe.le hCu.le he hu'
  have hM : 0≤M := by dsimp [M];positivity
  have hall := HigherOrder.product_relative_error
    (HigherOrder.exactEndpoint P g p*(normalized P g (List.replicate p 0) Y/
      normalized P g (List.replicate p 0) y₀))
    (normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y)
    M Cn g hgR hM hCn.le hprod hn'
  have hW := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
  have hUc : normalized P g (List.replicate p 0) y₀≠0 := by
    rw [W] at hW
    exact ((mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hW).ne'
  have hNc := (normalizedMarkedModel_pos g p hs y₀ ⟨y₀_pos.le,le_rfl⟩).ne'
  have hNy := (normalizedMarkedModel_pos g p hs Y hY).ne'
  have hid : HigherOrder.exactEndpoint P g p*(normalized P g (List.replicate p 0) Y/
        normalized P g (List.replicate p 0) y₀)*
        (normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y) =
      Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
    rw [HigherOrder.exactEndpoint,←normalizedMarkedModel_critical]
    field_simp [hUc,hNc,hNy]
  rwa [hid] at hall
lemma normalized_critical_anchor (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Icc (0:ℝ) y₀,
      y₀-Y≤1/(complexity g p:ℝ)^2 →
      |Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y-1|≤C/g := by
  apply normalized_critical_anchor_of_window P p hp
  obtain ⟨C,hC,G,hN⟩ := normalizedMarkedModel_critical_window p
  exact ⟨C,1,hC,by norm_num,G,fun g hg Y hY _ hsmall => (hN g hg Y hY hsmall).2⟩
lemma marked_prefactor_critical_relative (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Ico (0:ℝ) y₀,
      y₀-Y≤1/(complexity g p:ℝ)^2 →
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1|≤C/g := by
  obtain ⟨C,hC,G,hN⟩ := normalized_critical_anchor P p hp
  refine ⟨C,hC,G+2,?_⟩
  intro g hg Y hY hsmall
  have hs : Stable g p := by unfold Stable;omega
  have he : Real.pi*markedF P g p (XR Y)/markedModel g p Y=
      Real.pi*normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
    simpa only [←mul_div_assoc] using congrArg (fun x : ℝ => Real.pi*x)
      (markedF_div_model_eq_normalized P g p hs Y hY)
  rw [he]
  exact hN g (by omega) Y ⟨hY.1,hY.2.le⟩ hsmall
lemma prefactor_log_critical_anchor (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y∈Ico (0:ℝ) y₀,
      y₀-Y≤((complexity g p:ℝ)⁻¹)^2 → |prefactorLogError P g p Y|≤C/g := by
  obtain ⟨C,hC,G,hrel⟩ := marked_prefactor_critical_relative P p hp
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C)
  refine ⟨2*C,by positivity,G+N+2,?_⟩
  intro g hg Y hY hsmall
  have hgp : 0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
  have hscale : y₀-Y≤1/(complexity g p:ℝ)^2 := by
    simpa only [inv_pow,one_div] using hsmall
  have herr := hrel g (by omega) Y hY hscale
  have hn : 2*C<(g:ℝ) := hN.trans_le (by exact_mod_cast (show N≤g by omega))
  have hhalf : C/(g:ℝ)≤1/2 := (div_le_iff₀ hgp).mpr (by linarith)
  have hlog := Analysis.log_relative_small_bound
    (Real.pi*markedF P g p (XR Y)/markedModel g p Y) (herr.trans hhalf)
  unfold prefactorLogError
  calc _ ≤ 2*|Real.pi*markedF P g p (XR Y)/markedModel g p Y-1| := hlog
       _ ≤ 2*(C/(g:ℝ)) := mul_le_mul_of_nonneg_left herr (by norm_num)
       _ = (2*C)/(g:ℝ) := by ring
lemma absolute_prefactor_proof (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1| ≤ C*Real.log (g+1)/g := by
  exact absolute_prefactor_of_log_anchor P p hp (prefactor_log_critical_anchor P p hp)
end WP
