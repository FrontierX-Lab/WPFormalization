import WPFormalization.Analysis.ThetaDifferential
import WPFormalization.Statements.Marked

/-! Exact logarithmic differentiation of the actual marked comparison model.
The prefactor and every parameter factor are the original definitions. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma markedModel_log_decomposition (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    Real.log (markedModel g p Y) =
      Real.log (Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p))-
      (complexity g p:ℝ)*Real.log (Z Y)+
      ((1/2:ℝ)*Real.log (A Y*Theta Y)+((p:ℝ)/2)*Real.log (r Y)) := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hr := r_pos Y hY
  have ha := a_pos Y hY
  have hA : 0 < A Y := by
    unfold A
    exact div_pos (barH_one_re_pos Y ⟨hY.1,hY.2.le⟩) (by norm_num)
  have ht : 0 < Theta Y := by
    rw [Theta,Theta_eq_neg_two_T_deriv Y hY]
    have hh := T_deriv_neg_interior Y hY
    linarith
  have hC : 0 < Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p) := by
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos hh) (pow_pos (by norm_num) _))
      (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hh))
  have hZ : 0 < Z Y := by
    unfold Z
    exact mul_pos (mul_pos hA ha) (Real.rpow_pos_of_pos hr _)
  have hP : 0 < Real.rpow (r Y) ((p:ℝ)/2) := Real.rpow_pos_of_pos hr _
  have hS : 0 < Real.sqrt (A Y*Theta Y) := Real.sqrt_pos.mpr (mul_pos hA ht)
  rw [markedModel,Real.log_mul (mul_ne_zero (mul_ne_zero hC.ne' (pow_ne_zero _ (inv_ne_zero hZ.ne'))) hP.ne') hS.ne',
    Real.log_mul (mul_ne_zero hC.ne' (pow_ne_zero _ (inv_ne_zero hZ.ne'))) hP.ne',
    Real.log_mul hC.ne' (pow_ne_zero _ (inv_ne_zero hZ.ne')),Real.log_pow,Real.log_inv,
    Real.rpow_eq_pow,Real.log_rpow hr,Real.log_sqrt (mul_pos hA ht).le]
  ring

lemma markedModel_log_hasDerivAt_open_parameter (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun x => Real.log (markedModel g p x))
      (((complexity g p:ℝ)+
        (A Y*((7-2*(p:ℝ))/4*Theta Y-moment₁ Y+2-p)-1/2))/(A Y*r Y)) Y := by
  have hd := ((hasDerivAt_const Y
      (Real.log (Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p)))).sub
      ((logNormalizedAction_hasDerivAt_open_parameter Y hY).const_mul (complexity g p:ℝ))).add
        (transportPrimitive_hasDerivAt_open_parameter p Y hY)
  have he : (fun x => Real.log (markedModel g p x)) =ᶠ[𝓝 Y]
      (fun x => Real.log (Real.Gamma (complexity g p)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g p))-
        (complexity g p:ℝ)*Real.log (A x*a x*Real.rpow (r x) (3/2:ℝ))+
        ((1/2:ℝ)*Real.log (A x*(∑' l : ℕ,weight x l))+((p:ℝ)/2)*Real.log (r x))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    exact markedModel_log_decomposition g p hs x ⟨hx.1.le,hx.2⟩
  convert hd.congr_of_eventuallyEq he using 1
  dsimp only [Theta,moment₁]
  ring
end WP.Analysis
