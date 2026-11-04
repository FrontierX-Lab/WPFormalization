import WPFormalization.Analysis.RatioSaddleRegularity
import WPFormalization.Volumes.RatioModelIdentities

/-! The actual cusp saddle displacement used in Theorem 1.3. Integrating the logarithmic model and logarithmic variance derivatives against log Psi proves C/h bounds at the two exact saddles, uniformly over positive k. The zero saddle is handled separately in the coefficient-ratio assembly. -/

noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioSaddle_mean_parameter_hasDerivAt (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun t=>Psi (XR t))
      (euler Psi (XR Y)/(A Y*r Y*Psi (XR Y))) Y := by
  have hx : XR Y ∈ Ico (0:ℝ) xCritical :=
    ⟨XR_nonneg_interior Y ⟨hY.1.le,hY.2⟩,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hd := (Psi_analyticAt_interior _ hx).differentiableAt.hasDerivAt.comp Y (XR_hasDerivAt Y)
  convert! hd using 1
  have he := ratioSaddle_x_over_a Y ⟨hY.1.le,hY.2⟩
  have he' : XR Y=A Y*r Y*Psi (XR Y)*a Y := by
    exact (div_eq_iff (a_pos Y ⟨hY.1.le,hY.2⟩).ne').mp he
  rw [euler]
  field_simp [(marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',
    (r_pos Y ⟨hY.1.le,hY.2⟩).ne',(ratioSaddle_mean_pos Y hY).ne']
  linear_combination (deriv Psi (XR Y))*he'

lemma ratioSaddle_logMean_hasDerivAt (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun t=>Real.log (Psi (XR t)))
      (euler Psi (XR Y)/(A Y*r Y*Psi (XR Y)^2)) Y := by
  convert (ratioSaddle_mean_parameter_hasDerivAt Y hY).log (ratioSaddle_mean_pos Y hY).ne' using 1
  ring

lemma ratioModel_tilted_log_hasDerivAt (g p k : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun t=>Real.log (markedModel g p t)-(k:ℝ)*Real.log (XR t))
      (((complexity g p:ℝ)+transportBeta p Y-(k:ℝ)/Psi (XR Y))/(A Y*r Y)) Y := by
  have hxp : 0 < XR Y := by
    simpa only [XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
  have hd := (markedModel_log_hasDerivAt_open_parameter g p hs Y hY).sub
    (((XR_hasDerivAt Y).log hxp.ne').const_mul (k:ℝ))
  convert! hd using 1
  change _ = _
  unfold transportBeta
  have hpsi := Psi_XR_eq_kernel_ratio Y ⟨hY.1.le,hY.2⟩
  rw [hpsi]
  field_simp [(marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',
    (r_pos Y ⟨hY.1.le,hY.2⟩).ne',hxp.ne',
    (a_pos Y ⟨hY.1.le,hY.2⟩).ne']
  <;> ring

lemma ratioSaddle_tilted_derivative_comparison (g p k : ℕ) (hs : Stable g p)
    (B : ℝ) (hB : 0 ≤ B) (Y : ℝ) (hY : Y ∈ Ioo 0 y₀)
    (hbeta : |transportBeta p Y| ≤ B)
    (hl : (complexity g p:ℝ)-1 ≤ (k:ℝ)/Psi (XR Y))
    (hu : (k:ℝ)/Psi (XR Y) ≤ (complexity g p:ℝ)) :
    |deriv (fun t=>Real.log (markedModel g p t)-(k:ℝ)*Real.log (XR t)) Y| ≤
      3*(1+B)*deriv (fun t=>Real.log (Psi (XR t))) Y := by
  have hAr : 0 < A Y*r Y := mul_pos (marked_A_pos Y ⟨hY.1.le,hY.2.le⟩)
    (r_pos Y ⟨hY.1.le,hY.2⟩)
  have hp := ratioSaddle_mean_pos Y hY
  have hv := ratioSaddle_variance_pos Y hY
  have hb := ratioSaddle_mean_square_over_variance Y hY
  have hn : |(complexity g p:ℝ)+transportBeta p Y-(k:ℝ)/Psi (XR Y)| ≤ 1+B := by
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hbeta).1],by linarith [(abs_le.mp hbeta).2]⟩
  rw [(ratioModel_tilted_log_hasDerivAt g p k hs Y hY).deriv,
    (ratioSaddle_logMean_hasDerivAt Y hY).deriv,abs_div,abs_of_pos hAr]
  apply (div_le_div_of_nonneg_right hn hAr.le).trans
  have ht : Psi (XR Y)^2 ≤ 3*euler Psi (XR Y) := (div_le_iff₀ hv).mp hb
  apply (div_le_iff₀ hAr).mpr
  have hden : 0 < A Y*r Y*Psi (XR Y)^2 := mul_pos hAr (sq_pos_of_pos hp)
  have he : (3*(1+B)*(euler Psi (XR Y)/(A Y*r Y*Psi (XR Y)^2)))*(A Y*r Y) =
      3*(1+B)*euler Psi (XR Y)/(Psi (XR Y)^2) := by
    field_simp [hAr.ne',hp.ne',(marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',
      (r_pos Y ⟨hY.1.le,hY.2⟩).ne']
    <;> ring
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  nlinarith [mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ 1+B)]

end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioSaddle_variance_parameter_hasDerivAt (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun t=>euler Psi (XR t))
      ((euler Psi (XR Y)/(A Y*r Y*Psi (XR Y)))*(1+2*ratioSaddleDefect Y*Psi (XR Y))+
        deriv ratioSaddleDefect Y*Psi (XR Y)^2) Y := by
  have hψ := ratioSaddle_mean_parameter_hasDerivAt Y hY
  have hb := (ratioSaddleDefect_differentiableAt Y hY).hasDerivAt
  have hd := hψ.mul ((hasDerivAt_const Y 1).add (hb.mul hψ))
  have heq : (fun t=>euler Psi (XR t))=ᶠ[𝓝 Y]
      (fun t=>Psi (XR t)*(1+ratioSaddleDefect t*Psi (XR t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
    exact ratioSaddle_variance_formula t ⟨ht.1.le,ht.2⟩
  convert! hd.congr_of_eventuallyEq heq using 1 <;>
    simp only [Pi.add_apply,Pi.mul_apply] <;> ring

lemma ratioSaddle_variance_log_derivative_identity (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    deriv (fun t=>Real.log (euler Psi (XR t))) Y =
      deriv (fun t=>Real.log (Psi (XR t))) Y *
        ((1+2*ratioSaddleDefect Y*Psi (XR Y))/(1+ratioSaddleDefect Y*Psi (XR Y))+
          (A Y*r Y*deriv ratioSaddleDefect Y)*Psi (XR Y)^2/
            (1+ratioSaddleDefect Y*Psi (XR Y))^2) := by
  rw [((ratioSaddle_variance_parameter_hasDerivAt Y hY).log (ratioSaddle_variance_pos Y hY).ne').deriv,
    (ratioSaddle_logMean_hasDerivAt Y hY).deriv,
    ratioSaddle_variance_formula Y ⟨hY.1.le,hY.2⟩]
  have hp := ratioSaddle_mean_pos Y hY
  have hb := ratioSaddleDefect_lower Y ⟨hY.1.le,hY.2⟩
  have hw : 0 < 1+ratioSaddleDefect Y*Psi (XR Y) := by nlinarith
  field_simp [hp.ne',hw.ne',(marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',
    (r_pos Y ⟨hY.1.le,hY.2⟩).ne']
  <;> ring

lemma ratioSaddle_variance_log_derivative_bound :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Ioo (0:ℝ) y₀,
      |deriv (fun t=>Real.log (euler Psi (XR t))) Y| ≤
        C*deriv (fun t=>Real.log (Psi (XR t))) Y := by
  obtain ⟨B,hB,hbound⟩ := ratioSaddleDefect_weighted_derivative_bound
  refine ⟨2+9*B,by positivity,?_⟩
  intro Y hY
  have hp := ratioSaddle_mean_pos Y hY
  have hb := ratioSaddleDefect_lower Y ⟨hY.1.le,hY.2⟩
  have hw : 0 < 1+ratioSaddleDefect Y*Psi (XR Y) := by nlinarith
  have hratio : 0 ≤ (1+2*ratioSaddleDefect Y*Psi (XR Y))/(1+ratioSaddleDefect Y*Psi (XR Y)) ∧
      (1+2*ratioSaddleDefect Y*Psi (XR Y))/(1+ratioSaddleDefect Y*Psi (XR Y)) ≤ 2 := by
    constructor
    · exact div_nonneg (by nlinarith) hw.le
    · apply (div_le_iff₀ hw).mpr
      linarith
  have hsq : Psi (XR Y)^2/(1+ratioSaddleDefect Y*Psi (XR Y))^2 ≤ 9 := by
    apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
    have hlin : Psi (XR Y) ≤ 3*(1+ratioSaddleDefect Y*Psi (XR Y)) := by nlinarith
    have hsq := (sq_le_sq₀ hp.le (by positivity : 0≤3*(1+ratioSaddleDefect Y*Psi (XR Y)))).mpr hlin
    nlinarith only [hsq]
  have ht : |(A Y*r Y*deriv ratioSaddleDefect Y)*Psi (XR Y)^2/
            (1+ratioSaddleDefect Y*Psi (XR Y))^2| ≤ 9*B := by
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (Psi (XR Y))),
      abs_of_nonneg (sq_nonneg (1+ratioSaddleDefect Y*Psi (XR Y)))]
    calc
      _ ≤ B*Psi (XR Y)^2/(1+ratioSaddleDefect Y*Psi (XR Y))^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound Y hY) (sq_nonneg _)) (sq_nonneg _)
      _ = B*(Psi (XR Y)^2/(1+ratioSaddleDefect Y*Psi (XR Y))^2) := by ring
      _ ≤ B*9 := mul_le_mul_of_nonneg_left hsq hB.le
      _ = 9*B := by ring
  have hD : 0 < deriv (fun t=>Real.log (Psi (XR t))) Y := by
    rw [(ratioSaddle_logMean_hasDerivAt Y hY).deriv]
    exact div_pos (ratioSaddle_variance_pos Y hY)
      (mul_pos (mul_pos (marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (r_pos Y ⟨hY.1.le,hY.2⟩)) (sq_pos_of_pos hp))
  rw [ratioSaddle_variance_log_derivative_identity Y hY,abs_mul,abs_of_pos hD]
  rw [mul_comm (2+9*B)]
  apply mul_le_mul_of_nonneg_left _ hD.le
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hratio.1]; linarith [hratio.2,ht])
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioSaddle_mean_mono {Y Z : ℝ} (hY : Y ∈ Ico 0 y₀) (hZ : Z ∈ Ico 0 y₀)
    (hYZ : Y ≤ Z) : Psi (XR Y) ≤ Psi (XR Z) := by
  unfold Psi
  rw [inverseY_eq_of_root (XR Y) Y hY.2.le rfl,inverseY_eq_of_root (XR Z) Z hZ.2.le rfl]
  exact div_le_div_of_nonneg_right (density_strictMonoOn.monotoneOn hY hZ hYZ) (by norm_num)

lemma ratioSaddle_log_mean_gap (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (u u' : ℝ) (hu : h*u=k) (hu' : (h+1)*u'=k) :
    Real.log u-Real.log u' ≤ 1/h := by
  have hup : 0 < u := (mul_pos_iff_of_pos_left hh).mp (by rwa [hu])
  have hu'p : 0 < u' := (mul_pos_iff_of_pos_left (by linarith : 0<h+1)).mp (by rwa [hu'])
  rw [←Real.log_div hup.ne' hu'p.ne']
  have he : u/u'=(h+1)/h := by
    apply (div_eq_div_iff hu'p.ne' hh.ne').mpr
    nlinarith only [hu,hu']
  rw [he]
  calc
    _ ≤ (h+1)/h-1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) hh)
    _ = 1/h := by field_simp; ring

lemma ratioModel_saddle_log_variation (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ g k : ℕ,Stable g p → 1 ≤ k →
      ∀ Y' ∈ Ioo (0:ℝ) y₀,∀ Y ∈ Ioo (0:ℝ) y₀,Y'≤Y →
      0 < (complexity g p:ℝ)-1 →
      ((complexity g p:ℝ)-1)*Psi (XR Y)=(k:ℝ) →
      (complexity g p:ℝ)*Psi (XR Y')=(k:ℝ) →
      |(Real.log (markedModel g p Y)-(k:ℝ)*Real.log (XR Y))-
        (Real.log (markedModel g p Y')-(k:ℝ)*Real.log (XR Y'))| ≤
          C/((complexity g p:ℝ)-1) := by
  obtain ⟨B,hB,hbeta⟩ := ratioSaddle_transportBeta_bound p
  refine ⟨3*(1+B),by positivity,?_⟩
  intro g k hs hk Y' hY' Y hY hYY hpos hmean hmean'
  let F : ℝ → ℝ := fun t=>Real.log (markedModel g p t)-(k:ℝ)*Real.log (XR t)
  let Z : ℝ → ℝ := fun t=>-Real.log (Psi (XR t))
  have hmem (t:ℝ) (ht:t∈Icc Y' Y) : t∈Ioo (0:ℝ) y₀ :=
    ⟨hY'.1.trans_le ht.1,ht.2.trans_lt hY.2⟩
  have hcomp (t:ℝ) (ht:t∈Ioo Y' Y) :
      |deriv F t|≤3*(1+B)*(-deriv Z t) := by
    have htI := hmem t ⟨ht.1.le,ht.2.le⟩
    have hp := ratioSaddle_mean_pos t htI
    have hl : (complexity g p:ℝ)-1 ≤ (k:ℝ)/Psi (XR t) := by
      apply (le_div_iff₀ hp).mpr
      calc
        _ ≤ ((complexity g p:ℝ)-1)*Psi (XR Y) :=
          mul_le_mul_of_nonneg_left (ratioSaddle_mean_mono ⟨htI.1.le,htI.2⟩
            ⟨hY.1.le,hY.2⟩ ht.2.le) hpos.le
        _ = (k:ℝ) := hmean
    have hu : (k:ℝ)/Psi (XR t) ≤ (complexity g p:ℝ) := by
      apply (div_le_iff₀ hp).mpr
      calc
        (k:ℝ) = (complexity g p:ℝ)*Psi (XR Y') := hmean'.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (ratioSaddle_mean_mono ⟨hY'.1.le,hY'.2⟩ ⟨htI.1.le,htI.2⟩ ht.1.le) (by linarith)
    have hz : deriv Z t = -deriv (fun t=>Real.log (Psi (XR t))) t := by
      exact deriv.neg
    rw [hz,neg_neg]
    exact ratioSaddle_tilted_derivative_comparison g p k hs B hB.le t htI
      (hbeta t ⟨htI.1.le,htI.2.le⟩) hl hu
  have hv := log_scale_variation_bound F Z Y' Y (3*(1+B)) hYY
    (fun t ht=>(ratioModel_tilted_log_hasDerivAt g p k hs t (hmem t ht)).continuousAt.continuousWithinAt)
    (fun t ht=>(ratioSaddle_logMean_hasDerivAt t (hmem t ht)).neg.continuousAt.continuousWithinAt)
    (fun t ht=>(ratioModel_tilted_log_hasDerivAt g p k hs t (hmem t ⟨ht.1.le,ht.2.le⟩)).differentiableAt)
    (fun t ht=>(ratioSaddle_logMean_hasDerivAt t (hmem t ⟨ht.1.le,ht.2.le⟩)).neg.differentiableAt)
    hcomp
  have hgap := ratioSaddle_log_mean_gap ((complexity g p:ℝ)-1) k hpos
    (by exact_mod_cast (show 0<k by omega)) (Psi (XR Y)) (Psi (XR Y')) hmean
    (by simpa only [sub_add_cancel] using hmean')
  change |F Y-F Y'|≤_
  apply hv.trans
  dsimp only [Z]
  have he : -Real.log (Psi (XR Y'))- -Real.log (Psi (XR Y)) =
      Real.log (Psi (XR Y))-Real.log (Psi (XR Y')) := by ring
  rw [he,div_eq_mul_inv]
  simpa only [one_div] using mul_le_mul_of_nonneg_left hgap (by positivity : 0≤3*(1+B))

end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioSaddle_variance_log_variation :
    ∃ C : ℝ,0<C ∧ ∀ h k : ℝ,0<h → 0<k →
      ∀ Y' ∈ Ioo (0:ℝ) y₀,∀ Y ∈ Ioo (0:ℝ) y₀,Y'≤Y →
      h*Psi (XR Y)=k → (h+1)*Psi (XR Y')=k →
      |Real.log (euler Psi (XR Y))-Real.log (euler Psi (XR Y'))|≤C/h := by
  obtain ⟨C,hC,hbound⟩ := ratioSaddle_variance_log_derivative_bound
  refine ⟨C,hC,?_⟩
  intro h k hh hk Y' hY' Y hY hYY hmean hmean'
  let F : ℝ → ℝ := fun t=>Real.log (euler Psi (XR t))
  let Z : ℝ → ℝ := fun t=>-Real.log (Psi (XR t))
  have hmem (t:ℝ) (ht:t∈Icc Y' Y) : t∈Ioo (0:ℝ) y₀ :=
    ⟨hY'.1.trans_le ht.1,ht.2.trans_lt hY.2⟩
  have hf (t:ℝ) (ht:t∈Icc Y' Y) : HasDerivAt F
      (((euler Psi (XR t)/(A t*r t*Psi (XR t)))*(1+2*ratioSaddleDefect t*Psi (XR t))+
        deriv ratioSaddleDefect t*Psi (XR t)^2)/euler Psi (XR t)) t :=
    (ratioSaddle_variance_parameter_hasDerivAt t (hmem t ht)).log (ratioSaddle_variance_pos t (hmem t ht)).ne'
  have hv := log_scale_variation_bound F Z Y' Y C hYY
    (fun t ht=>(hf t ht).continuousAt.continuousWithinAt)
    (fun t ht=>(ratioSaddle_logMean_hasDerivAt t (hmem t ht)).neg.continuousAt.continuousWithinAt)
    (fun t ht=>(hf t ⟨ht.1.le,ht.2.le⟩).differentiableAt)
    (fun t ht=>(ratioSaddle_logMean_hasDerivAt t (hmem t ⟨ht.1.le,ht.2.le⟩)).neg.differentiableAt)
    (by
      intro t ht
      have htI := hmem t ⟨ht.1.le,ht.2.le⟩
      have hz : deriv Z t = -deriv (fun t=>Real.log (Psi (XR t))) t := by exact deriv.neg
      rw [hz,neg_neg]
      exact hbound t htI)
  change |F Y-F Y'|≤_
  apply hv.trans
  dsimp only [Z]
  have he : -Real.log (Psi (XR Y'))- -Real.log (Psi (XR Y)) =
      Real.log (Psi (XR Y))-Real.log (Psi (XR Y')) := by ring
  rw [he,div_eq_mul_inv]
  simpa only [one_div] using mul_le_mul_of_nonneg_left (ratioSaddle_log_mean_gap h k hh hk
    (Psi (XR Y)) (Psi (XR Y')) hmean hmean') hC.le

end WP.Analysis
