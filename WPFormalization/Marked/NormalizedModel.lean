import WPFormalization.Volumes.StringFlowProof
import WPFormalization.HigherOrder.PureEndpoint
import WPFormalization.Analysis.ExtractionFactorization
import WPFormalization.Marked.ModelDifferential
import WPFormalization.Analysis.CriticalKernelLipschitz
/-! The normalized marked comparison model and its genuine critical window.
Multiplying the original marked model by the physical a and r powers removes
the apparent critical degeneracy. Logarithmic kernel Lipschitz bounds give
uniform forward and reverse ratios on windows of width h^(-2). -/
noncomputable section
open Set
namespace WP
def normalizedMarkedModel (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.Gamma (complexity g p)/(4:ℝ)^g*(A Y)⁻¹^(complexity g p)*
    Real.sqrt (A Y*Theta Y/(Real.pi*(complexity g p)))
lemma normalizedMarkedModel_pos (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    0 < normalizedMarkedModel g p Y := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold complexity Stable at *;omega)
  have hA := Analysis.marked_A_pos Y hY
  have hΘ := Analysis.marked_Theta_pos Y hY
  unfold normalizedMarkedModel
  exact mul_pos (mul_pos (div_pos (Real.Gamma_pos_of_pos hh) (by positivity))
    (pow_pos (inv_pos.mpr hA) _))
    (Real.sqrt_pos.mpr (div_pos (mul_pos hA hΘ) (mul_pos Real.pi_pos hh)))
lemma normalizedMarkedModel_log (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    Real.log (normalizedMarkedModel g p Y)=
      Real.log (Real.Gamma (complexity g p)/(4:ℝ)^g)-
        (complexity g p:ℝ)*Real.log (A Y)+
          (Real.log (A Y)+Real.log (Theta Y)-Real.log (Real.pi*(complexity g p)))/2 := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold complexity Stable at *;omega)
  have hA := Analysis.marked_A_pos Y hY
  have hΘ := Analysis.marked_Theta_pos Y hY
  have hC : 0 < Real.Gamma (complexity g p)/(4:ℝ)^g := div_pos (Real.Gamma_pos_of_pos hh) (by positivity)
  have hS : 0 < Real.sqrt (A Y*Theta Y/(Real.pi*(complexity g p))) :=
    Real.sqrt_pos.mpr (div_pos (mul_pos hA hΘ) (mul_pos Real.pi_pos hh))
  rw [normalizedMarkedModel,Real.log_mul
    (mul_ne_zero hC.ne' (pow_ne_zero _ (inv_ne_zero hA.ne'))) hS.ne',
    Real.log_mul hC.ne' (pow_ne_zero _ (inv_ne_zero hA.ne')),Real.log_pow,Real.log_inv,
    Real.log_sqrt (div_pos (mul_pos hA hΘ) (mul_pos Real.pi_pos hh)).le,
    Real.log_div (mul_ne_zero hA.ne' hΘ.ne') (mul_ne_zero Real.pi_pos.ne' hh.ne'),
    Real.log_mul hA.ne' hΘ.ne']
  ring
lemma normalizedMarkedModel_critical (g p : ℕ) :
    normalizedMarkedModel g p y₀=
      Real.Gamma (complexity g p)/(4:ℝ)^g*(15/2:ℝ)^(complexity g p)*
        Real.sqrt ((2/15:ℝ)/(Real.pi*(complexity g p))) := by
  have hA : A y₀=(2/15:ℝ) := by norm_num [A,barH]
  have hΘ : Theta y₀=1 := Analysis.total_weight_critical_value
  simp only [normalizedMarkedModel,hA,hΘ,mul_one,show (2/15:ℝ)⁻¹=15/2 by norm_num]
lemma normalizedMarkedModel_scaling (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    a Y^(complexity g p)*r Y^(dimension g p)*markedModel g p Y=normalizedMarkedModel g p Y := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold complexity Stable at *;omega)
  have ha := a_pos Y hY
  have hr := r_pos Y hY
  have hA := Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩
  have hΘ := Analysis.marked_Theta_pos Y ⟨hY.1,hY.2.le⟩
  have hZ := Analysis.marked_Z_pos Y hY
  have hG := Real.Gamma_pos_of_pos hh
  have hP := Real.rpow_pos_of_pos hr ((p:ℝ)/2)
  have hS := Real.sqrt_pos.mpr (mul_pos hA hΘ)
  have hD := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hh)
  have hM : 0 < markedModel g p Y := by unfold markedModel;positivity
  have hN := normalizedMarkedModel_pos g p hs Y ⟨hY.1,hY.2.le⟩
  have hL : 0 < a Y^(complexity g p)*r Y^(dimension g p)*markedModel g p Y := by positivity
  apply Real.log_injOn_pos hL hN
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hr.ne')) hM.ne',
    Real.log_mul (pow_ne_zero _ ha.ne') (pow_ne_zero _ hr.ne'),Real.log_pow,Real.log_pow,
    Analysis.markedModel_log_decomposition g p hs Y hY,
    normalizedMarkedModel_log g p hs Y ⟨hY.1,hY.2.le⟩]
  have hc : Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p)=
      (Real.Gamma (complexity g p)/(4:ℝ)^g)/Real.sqrt (Real.pi*complexity g p) := by
    rw [inv_pow]
    ring
  rw [hc,Real.log_div (div_pos hG (by positivity)).ne' hD.ne',
    Real.log_sqrt (mul_pos Real.pi_pos hh).le,Real.log_mul hA.ne' hΘ.ne']
  have hlogZ : Real.log (Z Y)=Real.log (A Y)+Real.log (a Y)+(3/2:ℝ)*Real.log (r Y) := by
    unfold Z
    rw [Real.rpow_eq_pow,Real.log_mul (mul_ne_zero hA.ne' ha.ne') (Real.rpow_pos_of_pos hr (3/2:ℝ)).ne',
      Real.log_mul hA.ne' ha.ne',Real.log_rpow hr]
  rw [hlogZ]
  have hd : 2*(dimension g p:ℝ)+(p:ℝ)=3*(complexity g p:ℝ) := by
    have hm : 3 ≤ 3*g+p := by unfold Stable at hs;omega
    have hc : 2 ≤ 2*g+p := by unfold Stable at hs;omega
    simp only [dimension,complexity,Nat.cast_sub hm,Nat.cast_sub hc,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  linear_combination (Real.log (r Y)/2)*hd
end WP
namespace WP
lemma normalizedMarkedModel_log_difference (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)=
      (1/2-(complexity g p:ℝ))*(Real.log (A Y)-Real.log (2/15:ℝ))+(1/2:ℝ)*Real.log (Theta Y) := by
  rw [normalizedMarkedModel_log g p hs Y hY,
    normalizedMarkedModel_log g p hs y₀ ⟨y₀_pos.le,le_rfl⟩]
  have hA : A y₀=(2/15:ℝ) := by norm_num [A,barH]
  have hΘ : Theta y₀=1 := Analysis.total_weight_critical_value
  rw [hA,hΘ,Real.log_one]
  ring
lemma normalizedMarkedModel_critical_window (p : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Icc (0:ℝ) y₀,
      y₀-Y ≤ 1/(complexity g p:ℝ)^2 →
      |normalizedMarkedModel g p Y/normalizedMarkedModel g p y₀-1| ≤ C/(complexity g p:ℝ) ∧
      |normalizedMarkedModel g p y₀/normalizedMarkedModel g p Y-1| ≤ C/(complexity g p:ℝ) := by
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
  have hinv : 1/h^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hhp)).2
    have hsq : h ≤ h^2 := by nlinarith
    exact hδh.trans (mul_le_mul_of_nonneg_left hsq hδ.le)
  have hLip' : |Real.log (A Y)-Real.log (2/15:ℝ)|+|Real.log (Theta Y)| ≤ L*(y₀-Y) := by
    simpa only [Theta] using hLip Y hY (hsmall.trans hinv)
  have hlog : |Real.log (normalizedMarkedModel g p Y)-Real.log (normalizedMarkedModel g p y₀)| ≤ L/h := by
    rw [normalizedMarkedModel_log_difference g p hs Y hY]
    change |(1/2-h)*(Real.log (A Y)-Real.log (2/15:ℝ))+(1/2:ℝ)*Real.log (Theta Y)| ≤ L/h
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
         _  ≤  h*(L*(1/h^2)) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left hsmall hL.le) hhp.le
         _ = _ := by field_simp <;> ring
  have hLh : L/h ≤ 1 := (div_le_one hhp).2 (by linarith)
  have hrel (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
      (hloguv : |Real.log u-Real.log v| ≤ L/h) : |u/v-1| ≤ (2*L)/h := by
    have hlogq : |Real.log (u/v)| ≤ L/h := by rw [Real.log_div hu.ne' hv.ne'];exact hloguv
    calc _ = |Real.exp (Real.log (u/v))-1| := by rw [Real.exp_log (div_pos hu hv)]
         _  ≤  2* |Real.log (u/v)| := Real.abs_exp_sub_one_le (hlogq.trans hLh)
         _  ≤  2*(L/h) := mul_le_mul_of_nonneg_left hlogq (by norm_num)
         _ = _ := by ring
  have hNY := normalizedMarkedModel_pos g p hs Y hY
  have hNcrit := normalizedMarkedModel_pos g p hs y₀ ⟨y₀_pos.le,le_rfl⟩
  exact ⟨hrel _ _ hNY hNcrit hlog,hrel _ _ hNcrit hNY (by rw [abs_sub_comm];exact hlog)⟩
end WP

namespace WP
lemma markedF_div_model_eq_normalized (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Set.Ico (0:ℝ) y₀) :
    markedF P g p (XR Y)/markedModel g p Y=
      normalized P g (List.replicate p 0) Y/normalizedMarkedModel g p Y := by
  have hn : normalized P g (List.replicate p 0) Y=
      (a Y^(complexity g p)*r Y^(dimension g p))*shifted P g (List.replicate p 0) Y := by
    rw [normalized,if_neg (ne_of_lt hY.2)]
    simp [deficit]
  have hf : a Y^(complexity g p)*r Y^(dimension g p)≠0 :=
    mul_ne_zero (pow_ne_zero _ (a_pos Y hY).ne') (pow_ne_zero _ (r_pos Y hY).ne')
  rw [←string_flow_proof P g p hs Y hY,hn,←normalizedMarkedModel_scaling g p hs Y hY,
    mul_div_mul_left _ _ hf]
lemma exactEndpoint_eq_normalizedMarkedModel (P : PsiTheory) (g p : ℕ) :
    HigherOrder.exactEndpoint P g p=
      Real.pi*normalized P g (List.replicate p 0) y₀/normalizedMarkedModel g p y₀ := by
  rw [HigherOrder.exactEndpoint,normalizedMarkedModel_critical]
end WP
