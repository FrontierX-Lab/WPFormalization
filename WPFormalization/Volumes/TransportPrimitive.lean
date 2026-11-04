import WPFormalization.Volumes.StringFlowProof
import WPFormalization.Marked.ModelDifferential
import WPFormalization.Analysis.ExtractionFactorization
/-! The exact logarithmic residual underlying Eq. (7.11).
Actual positivity permits log division; the genuine marked generating function
and comparison model have the proved ordinary derivatives. Their difference
is exactly the transport residual divided by A*r. The inequality corollary
only rescales a supplied numerical residual bound and does not assume or
invoke the paper's transport theorem. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP
lemma markedModel_pos_parameter (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : 0 < markedModel g p Y := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  unfold markedModel
  exact mul_pos (mul_pos
    (mul_pos (div_pos
      (mul_pos (Real.Gamma_pos_of_pos hh) (pow_pos (by norm_num) _))
      (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hh)))
      (pow_pos (inv_pos.mpr (Analysis.marked_Z_pos Y hY)) _))
    (Real.rpow_pos_of_pos (r_pos Y hY) _))
    (Real.sqrt_pos.mpr (mul_pos (Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩)
      (Analysis.marked_Theta_pos Y ⟨hY.1,hY.2.le⟩)))

lemma markedF_model_log_deriv_exact (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    deriv (fun t => Real.log (markedF P g p (XR t)/markedModel g p t)) Y =
      (A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y))/(A Y*r Y) := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have hF := markedF_parameter_log_hasDerivAt P g p hp hs Y hYi
  have hM := Analysis.markedModel_log_hasDerivAt_open_parameter g p hs Y hY
  have hd := hF.sub hM
  have he : (fun t => Real.log (markedF P g p (XR t)/markedModel g p t)) =ᶠ[𝓝 Y]
      (fun t => Real.log (markedF P g p (XR t))-Real.log (markedModel g p t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
    exact Real.log_div (markedF_pos_parameter P g p hp hs t ⟨ht.1.le,ht.2⟩).ne'
      (markedModel_pos_parameter g p hs t ⟨ht.1.le,ht.2⟩).ne'
  rw [(hd.congr_of_eventuallyEq he).deriv,hF.deriv]
  unfold transportBeta
  field_simp [(Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',(r_pos Y hYi).ne']

lemma markedF_model_log_deriv_bound (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) (C : ℝ)
    (he : |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y)| ≤ C/(complexity g p:ℝ)) :
    |deriv (fun t => Real.log (markedF P g p (XR t)/markedModel g p t)) Y| ≤
      C/((complexity g p:ℝ)*A Y*r Y) := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have hAr := mul_pos (Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (r_pos Y hYi)
  rw [markedF_model_log_deriv_exact P g p hp hs Y hY,abs_div,abs_of_pos hAr]
  calc
    _ ≤ (C/(complexity g p:ℝ))/(A Y*r Y) := div_le_div_of_nonneg_right he hAr.le
    _ = _ := by ring
end WP
