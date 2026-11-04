import WPFormalization.Coefficients.UniformSaddleProbability
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Reduction. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma log_probability_bound_of_polynomial_lower (c:ℝ)(hc:0<c):
    ∃C:ℝ,0<C∧∀h m:ℕ,1≤ h→2*m≤3*h→∀p:ℝ,c/((m:ℝ)+1)≤ p→p≤1→
      |Real.log p|≤ C*Real.log ((h:ℝ)+1):=by
  let c₀:ℝ:=min c 1
  have hc₀:0<c₀:=lt_min hc zero_lt_one
  have hc₀1:c₀≤1:=min_le_right _ _
  have hlog2:0<Real.log 2:=Real.log_pos (by norm_num)
  let L:ℝ:=-Real.log c₀+Real.log 2
  have hLc:0≤-Real.log c₀:=neg_nonneg.mpr (Real.log_nonpos hc₀.le hc₀1)
  have hL:0<L:=by dsimp[L];linarith
  let C:ℝ:=L/Real.log 2+1
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro h m hh hm p hp hp1
  have hp₀:c₀/((m:ℝ)+1)≤ p:=
    (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)).trans hp
  have hpp:0<p:=(div_pos hc₀ (by positivity)).trans_le hp₀
  have hlp:Real.log (c₀/((m:ℝ)+1))≤ Real.log p:=Real.log_le_log (by positivity) hp₀
  rw[Real.log_div hc₀.ne' (by positivity:((m:ℝ)+1)≠0)] at hlp
  have hmi:(m:ℝ)+1≤2*((h:ℝ)+1):=by
    have hmR:(2:ℝ)*m≤3*h:=by exact_mod_cast hm
    nlinarith
  have hlm:Real.log ((m:ℝ)+1)≤ Real.log 2+Real.log ((h:ℝ)+1):=by
    rw[←Real.log_mul (by norm_num:(2:ℝ)≠0) (by positivity:((h:ℝ)+1)≠0)]
    exact Real.log_le_log (by positivity) hmi
  have hhr:(1:ℝ)≤ h:=by exact_mod_cast hh
  have hlogh:Real.log 2≤ Real.log ((h:ℝ)+1):=Real.log_le_log (by norm_num) (by linarith)
  have hmL:=mul_le_mul_of_nonneg_left hlogh (div_nonneg hL.le hlog2.le)
  have hcancel:L/Real.log 2*Real.log 2=L:=by field_simp
  rw[hcancel] at hmL
  rw[abs_of_nonpos (Real.log_nonpos hpp.le hp1)]
  dsimp[C,L] at *
  nlinarith
lemma tiltedKernelMass_log_identity (z:ℝ)(hz:0<z)(hzr:z≤ r 0)(h m:ℕ)(hh:0<h):
    Real.log (tiltedKernelMass z h m)=Real.log (unscaledCoeff h m)+
      (h:ℝ)*Real.log (H 0 z).re+(m:ℝ)*Real.log z:=by
  have hH:=H_zero_re_pos z ⟨hz.le,hzr⟩
  have hA:=unscaledCoeff_pos h m hh
  rw[tiltedKernelMass_eq_unscaled,Real.log_mul (mul_pos (pow_pos hH h) (pow_pos hz m)).ne' hA.ne',
    Real.log_mul (pow_pos hH h).ne' (pow_pos hz m).ne',Real.log_pow,Real.log_pow]
  ring
end WP.Coefficients
