import WPFormalization.Volumes.TransportPrimitive
import WPFormalization.Marked.VolumeRatios
import WPFormalization.Analysis.HarmonicSumProbability
import WPFormalization.Analysis.KernelMomentComplexification

/-! Global mean-variance identities for the actual physical saddle. The exact J derivative gives the defect b >= 1/3 and v = Psi * (1 + b * Psi), hence Psi^2 / v <= 3 uniformly between the two endpoints. -/

noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def ratioSaddleDefect (Y : ℝ) : ℝ := 1-A Y*(1+Theta Y/2)

lemma ratioSaddle_J_derivative (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    deriv J Y = a Y*A Y*(1+Theta Y/2) := by
  rw [J_deriv_interior Y hY,stationary_first_moment_eq_Aa Y hY,
    Theta,Theta_eq_neg_two_T_deriv Y hY]
  ring

lemma ratioSaddleDefect_lower (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    1/3 ≤ ratioSaddleDefect Y := by
  have hd := J_deriv_upper_interior Y hY
  rw [ratioSaddle_J_derivative Y hY] at hd
  have ha := a_pos Y hY
  dsimp [ratioSaddleDefect]
  have he : A Y*(1+Theta Y/2) ≤ 2/3 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith only [hd]
  linarith

lemma ratioSaddle_variance_formula (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    euler Psi (XR Y) = Psi (XR Y)*(1+ratioSaddleDefect Y*Psi (XR Y)) := by
  have hx : XR Y ∈ Ico (0:ℝ) xCritical :=
    ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hinv := inverseY_eq_of_root (XR Y) Y hY.2.le rfl
  rw [euler,(Psi_hasDerivAt_interior _ hx).deriv,hinv,
    (density_hasDerivAt_interior Y hY).deriv,Psi_XR_eq_kernel_ratio Y hY,
    J_sub_XR_eq_Aar Y hY,ratioSaddle_J_derivative Y hY]
  dsimp only [ratioSaddleDefect]
  have hJ : J Y=XR Y+A Y*a Y*r Y := by linarith [J_sub_XR_eq_Aar Y hY]
  rw [hJ]
  field_simp [(a_pos Y hY).ne',(r_pos Y hY).ne',
    (marked_A_pos Y ⟨hY.1,hY.2.le⟩).ne']
  <;> ring

lemma ratioSaddle_x_over_a (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    XR Y/a Y = A Y*r Y*Psi (XR Y) := by
  rw [Psi_XR_eq_kernel_ratio Y hY]
  field_simp [(a_pos Y hY).ne',(r_pos Y hY).ne',
    (marked_A_pos Y ⟨hY.1,hY.2.le⟩).ne']

lemma ratioSaddle_mean_pos (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    0 < Psi (XR Y) := by
  rw [Psi_XR_eq_kernel_ratio Y ⟨hY.1.le,hY.2⟩]
  have hx : 0 < XR Y := by
    simpa only [XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
  exact div_pos hx (mul_pos (mul_pos
    (marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (a_pos Y ⟨hY.1.le,hY.2⟩))
    (r_pos Y ⟨hY.1.le,hY.2⟩))

lemma ratioSaddle_variance_pos (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    0 < euler Psi (XR Y) := by
  rw [ratioSaddle_variance_formula Y ⟨hY.1.le,hY.2⟩]
  have hp := ratioSaddle_mean_pos Y hY
  have hb := ratioSaddleDefect_lower Y ⟨hY.1.le,hY.2⟩
  exact mul_pos hp (by nlinarith)

lemma ratioSaddle_mean_square_over_variance (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    Psi (XR Y)^2/euler Psi (XR Y) ≤ 3 := by
  have hp := ratioSaddle_mean_pos Y hY
  have hb := ratioSaddleDefect_lower Y ⟨hY.1.le,hY.2⟩
  rw [ratioSaddle_variance_formula Y ⟨hY.1.le,hY.2⟩]
  apply (div_le_iff₀ (mul_pos hp (by nlinarith))).mpr
  nlinarith [mul_nonneg (show 0≤ratioSaddleDefect Y-1/3 by linarith) (sq_nonneg (Psi (XR Y)))]

end WP.Analysis
