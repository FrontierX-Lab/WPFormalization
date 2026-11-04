import WPFormalization.Intersection.CriticalHomogeneity
import WPFormalization.Marked.NormalizedModel
/-! Actual homogeneous amplitudes and both normalized model ratios on a cubic critical window, with quadratic inverse-complexity errors. -/
noncomputable section
namespace WP
open Set
lemma small_homogeneous_power_second_error (C δ : ℝ) (h : ℕ)
    (hC : 0≤C) (hδ : 0≤δ) (hh : 0<(h:ℝ)) (hCh : C≤h)
    (hsmall : δ≤1/(h:ℝ)^3) : (1+C*δ)^h-1≤2*C/(h:ℝ)^2 := by
  let x : ℝ := (h:ℝ)*(C*δ)
  have hx0 : 0≤x := by dsimp [x];positivity
  have hx : x≤C/(h:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
    have hd := (le_div_iff₀ (pow_pos hh 3)).mp hsmall
    dsimp only [x]
    nlinarith [mul_le_mul_of_nonneg_left hd hC]
  have hx1 : |x|≤1 := by
    rw [abs_of_nonneg hx0]
    have hh1 : (1:ℝ)≤h := by exact_mod_cast (show 1≤h by exact_mod_cast hh)
    exact hx.trans ((div_le_one (sq_pos_of_pos hh)).mpr (hCh.trans (by nlinarith)))
  have he : (1+C*δ)^h≤Real.exp x := by
    have hb : 1+C*δ≤Real.exp (C*δ) := by linarith [Real.add_one_le_exp (C*δ)]
    have hp := pow_le_pow_left₀ (show 0≤1+C*δ by positivity) hb h
    simpa only [x,Real.exp_nat_mul] using hp
  calc _ ≤ Real.exp x-1 := sub_le_sub_right he 1
       _ ≤ |Real.exp x-1| := le_abs_self _
       _ ≤ 2*|x| := Real.abs_exp_sub_one_le hx1
       _ = 2*x := by rw [abs_of_nonneg hx0]
       _ ≤ 2*(C/(h:ℝ)^2) := mul_le_mul_of_nonneg_left hx (by norm_num)
       _ = 2*C/(h:ℝ)^2 := by ring
lemma normalized_zero_critical_cubic_window_error (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Icc (0:ℝ) y₀,
      y₀-Y≤δ₀ → y₀-Y≤1/(complexity g p:ℝ)^3 →
      |normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀-1|≤
        C/(complexity g p:ℝ)^2 := by
  obtain ⟨C,δ,hC,hδ,hcomp⟩ := normalized_critical_neighborhood_comparison
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨2*C,δ,by positivity,hδ,N+2,?_⟩
  intro g hg Y hY hsmall hscale
  have hg₂ : 2≤g := by omega
  have hg₁ : 1≤g := by omega
  have hs : Stable g p := by unfold Stable;omega
  have hW := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
  have hcrit : 0<normalized P g (List.replicate p 0) y₀ := by
    rw [W] at hW
    exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hW
  have hgh : g≤complexity g p := by unfold complexity;omega
  have hh : 0<(complexity g p:ℝ) := by exact_mod_cast (show 0<complexity g p by omega)
  have hCh : C≤(complexity g p:ℝ) :=
    hN.le.trans (by exact_mod_cast (show N≤complexity g p by omega))
  have hc := hcomp P g (List.replicate p 0) (by simpa using hp) Y hY hsmall
  have hlo : 1≤normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀ :=
    (le_div_iff₀ hcrit).mpr (by simpa using hc.1)
  have hup : normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀≤
      (1+C*(y₀-Y))^(complexity g p) := (div_le_iff₀ hcrit).mpr (by simpa only [List.length_replicate] using hc.2)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact (sub_le_sub_right hup 1).trans
    (small_homogeneous_power_second_error C (y₀-Y) (complexity g p) hC.le (by linarith [hY.2]) hh hCh hscale)
end WP
namespace WP
open Set
lemma normalizedMarkedModel_cubic_critical_window (p : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Icc (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^3 →
      |normalizedMarkedModel g p Y/normalizedMarkedModel g p y₀-1| ≤ C/(complexity g p:ℝ)^2 ∧
      |normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y-1| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨L,δ,hL,hδ,hLip⟩ := Analysis.log_parameters_critical_lipschitz
  obtain ⟨N,hN⟩ := exists_nat_gt (L+1/δ+2)
  refine ⟨2*L,by positivity,2+N,?_⟩
  intro g hg Y hY hsmall
  have hs : Stable g p := by unfold Stable;omega
  let h : ℝ := complexity g p
  have hh : (1:ℝ) ≤ h := by
    dsimp only [h]
    exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : 0 < h := by linarith
  have hNh : (N:ℝ) ≤ h := by
    dsimp only [h]
    exact_mod_cast (show N ≤ complexity g p by unfold complexity;omega)
  have hlarge : L+1/δ+2<h := hN.trans_le hNh
  have hinvδ : 0 < 1/δ := by positivity
  have hδh : 1 ≤ δ*h := by
    have hi : 1/δ ≤ h := by linarith
    have hj := (div_le_iff₀ hδ).mp hi
    nlinarith
  have hinv : 1/h^3 ≤ δ := by
    apply (div_le_iff₀ (pow_pos hhp 3)).2
    have hsq : h ≤ h^3 := by nlinarith [sq_nonneg (h-1),mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg h)]
    exact hδh.trans (mul_le_mul_of_nonneg_left hsq hδ.le)
  have hLip' : |Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (Theta Y)| ≤ L*(y₀-Y) := by
    simpa only [Theta] using hLip Y hY (hsmall.trans hinv)
  have hlog : |Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)| ≤ L/h^2 := by
    rw [normalizedMarkedModel_log_difference g p hs Y hY]
    change |(1/2-h)*(Real.log (A Y)-Real.log (2/15:ℝ))+(1/2:ℝ)*Real.log (Theta Y)| ≤ L/h^2
    calc _  ≤  |(1/2-h)*(Real.log (A Y)-Real.log (2/15:ℝ))|+|(1/2:ℝ)*Real.log (Theta Y)| := abs_add_le _ _
         _ = (h-1/2)* |Real.log (A Y)-Real.log (2/15:ℝ)|+(1/2:ℝ)* |Real.log (Theta Y)| := by
           rw [abs_mul,abs_of_neg (by linarith : 1/2-h<0),abs_mul]
           norm_num
         _  ≤  h*(|Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (Theta Y)|) := by
           have h₁ := mul_le_mul_of_nonneg_right (show h-1/2 ≤ h by linarith)
             (abs_nonneg (Real.log (A Y)-Real.log (2/15:ℝ)))
           have h₂ := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ h by linarith)
             (abs_nonneg (Real.log (Theta Y)))
           nlinarith
         _  ≤  h*(L*(y₀-Y)) := mul_le_mul_of_nonneg_left hLip' hhp.le
         _  ≤  h*(L*(1/h^3)) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left hsmall hL.le) hhp.le
         _ = _ := by field_simp <;> ring
  have hLh : L/h^2 ≤ 1 := (div_le_one (sq_pos_of_pos hhp)).2 (by nlinarith)
  have hrel (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
      (hloguv : |Real.log u-Real.log v| ≤ L/h^2) : |u/v-1| ≤ (2*L)/h^2 := by
    have hlogq : |Real.log (u/v)| ≤ L/h^2 := by rw [Real.log_div hu.ne' hv.ne'];exact hloguv
    calc _ = |Real.exp (Real.log (u/v))-1| := by rw [Real.exp_log (div_pos hu hv)]
         _  ≤  2* |Real.log (u/v)| := Real.abs_exp_sub_one_le (hlogq.trans hLh)
         _  ≤  2*(L/h^2) := mul_le_mul_of_nonneg_left hlogq (by norm_num)
         _ = _ := by ring
  have hNY := normalizedMarkedModel_pos g p hs Y hY
  have hNcrit := normalizedMarkedModel_pos g p hs y₀ ⟨y₀_pos.le,le_rfl⟩
  exact ⟨hrel _ _ hNY hNcrit hlog,hrel _ _ hNcrit hNY (by rw [abs_sub_comm];exact hlog)⟩
end WP
