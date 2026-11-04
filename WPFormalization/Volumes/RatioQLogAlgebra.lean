import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
noncomputable section
namespace WP.Analysis

lemma ratioQ_log_scalar (M x P h v : ℝ) (k : ℕ)
    (hM : 0 < M) (hx : 0 < x) (hP : 0 < P)
    (hh : 0 < h) (hv : 0 < v) (hk : 0 < (k:ℝ)) :
    Real.log (M/Real.pi*(x⁻¹^k*P*Real.sqrt ((k:ℝ)/(h*v)))) =
      Real.log M-Real.log Real.pi-(k:ℝ)*Real.log x+Real.log P+
        (1/2)*(Real.log (k:ℝ)-Real.log h-Real.log v) := by
  have hi : 0 < x⁻¹^k := pow_pos (inv_pos.mpr hx) k
  have hs : 0 < Real.sqrt ((k:ℝ)/(h*v)) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.log_mul (div_pos hM Real.pi_pos).ne' (mul_pos (mul_pos hi hP) hs).ne',
    Real.log_div hM.ne' Real.pi_ne_zero,
    Real.log_mul (mul_pos hi hP).ne' hs.ne',Real.log_mul hi.ne' hP.ne',
    Real.log_pow,Real.log_inv,Real.log_sqrt (by positivity),
    Real.log_div hk.ne' (mul_pos hh hv).ne',Real.log_mul hh.ne' hv.ne']
  ring

lemma ratioQ_model_log_scalar (M T h D : ℝ) (hM : 0 < M) (hh : 0 < h) (hD : 0 < D)
    (he : T = M*(h/D)*Real.sqrt (h/(h+1))) :
    Real.log T = Real.log M+Real.log (h/D)+(1/2)*Real.log (h/(h+1)) := by
  rw [he,Real.log_mul (mul_pos hM (div_pos hh hD)).ne'
    (Real.sqrt_pos.mpr (by positivity)).ne',
    Real.log_mul hM.ne' (div_pos hh hD).ne',Real.log_sqrt (by positivity)]
  ring

lemma ratioQ_cusp_log_scalar (M T U x x' P h v v' D : ℝ) (k : ℕ)
    (hM : 0 < M) (hT : 0 < T) (hU : 0 < U)
    (hx : 0 < x) (hx' : 0 < x') (hP : 0 < P)
    (hh : 0 < h) (hv : 0 < v) (hv' : 0 < v') (hD : 0 < D)
    (hk : 0 < (k:ℝ)) (he : T=M*(h/D)*Real.sqrt (h/(h+1))) :
    Real.log ((U/Real.pi*(x'⁻¹^k*P*Real.sqrt ((k:ℝ)/((h+1)*v')))) /
      (M/Real.pi*(x⁻¹^k*P*Real.sqrt ((k:ℝ)/(h*v)))) / (h/D)) =
      Real.log (h/(h+1))+
        ((Real.log U-(k:ℝ)*Real.log x')-(Real.log T-(k:ℝ)*Real.log x))+
        (1/2)*(Real.log v-Real.log v') := by
  have hq : 0 < M/Real.pi*(x⁻¹^k*P*Real.sqrt ((k:ℝ)/(h*v))) := by positivity
  have hq' : 0 < U/Real.pi*(x'⁻¹^k*P*Real.sqrt ((k:ℝ)/((h+1)*v'))) := by positivity
  rw [Real.log_div (div_pos hq' hq).ne' (div_pos hh hD).ne',
    Real.log_div hq'.ne' hq.ne',
    ratioQ_log_scalar U x' P (h+1) v' k hU hx' hP (by positivity) hv' hk,
    ratioQ_log_scalar M x P h v k hM hx hP hh hv hk,
    ratioQ_model_log_scalar M T h D hM hh hD he,
    Real.log_div hh.ne' hD.ne']
  simp only [Real.log_div hh.ne' (show h+1 ≠ 0 by positivity)]
  ring

end WP.Analysis
