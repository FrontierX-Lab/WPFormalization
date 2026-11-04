import WPFormalization.Analysis.CharacteristicL1Split
/-! Uniform convergence on every fixed central interval, together with a
uniform Gaussian tail for the actual characteristic function, implies
L1 convergence to the Gaussian. Both inputs remain explicit and must be
proved for a concrete probability generating function. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology

lemma gaussian_characteristic_l1_tendsto_of_core_tails (χ:ℕ→ℝ→ℂ)
    (hχ:∀n,Integrable (χ n))(c C:ℝ)(hc:0<c)
    (hcore:∀T:ℝ,1≤T→∀ε:ℝ,0<ε→∀ᶠn:ℕ in atTop,
      ∀t:ℝ,|t|≤T→‖χ n t-Complex.exp (-(t:ℂ)^2/2)‖≤ε)
    (htail:∀T:ℝ,1≤T→∀ᶠn:ℕ in atTop,
      (∫t:ℝ in {t:ℝ|T≤|t|},‖χ n t‖)≤C*Real.exp (-c*T^2)):
    Tendsto (fun n:ℕ=>∫t:ℝ,‖χ n t-Complex.exp (-(t:ℂ)^2/2)‖) atTop (𝓝 0):=by
  have hpow:Tendsto (fun T:ℝ=>T^2) atTop atTop:=tendsto_pow_atTop (by norm_num)
  have he₁:Tendsto (fun T:ℝ=>C*Real.exp (-c*T^2)) atTop (𝓝 0):=by
    have ht:=(Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop hc)).const_mul C
    simpa only[Function.comp_def,mul_zero,neg_mul] using ht
  have he₂:Tendsto (fun T:ℝ=>Real.sqrt (8*Real.pi)*Real.exp (-T^2/4)) atTop (𝓝 0):=by
    have ht:=(Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hpow.const_mul_atTop (by norm_num:(0:ℝ)<1/4))).const_mul (Real.sqrt (8*Real.pi))
    have ht':Tendsto (fun T:ℝ=>Real.sqrt (8*Real.pi)*Real.exp (-((1/4:ℝ)*T^2))) atTop (𝓝 0):=by
      simpa only[Function.comp_def,mul_zero] using ht
    convert ht' using 1
    funext T
    congr 2
    ring
  have he:Tendsto (fun T:ℝ=>C*Real.exp (-c*T^2)+Real.sqrt (8*Real.pi)*Real.exp (-T^2/4)) atTop (𝓝 0):=by
    simpa only[add_zero] using he₁.add he₂
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨T,hT,hcut⟩:=((eventually_ge_atTop (1:ℝ)).and
    (he.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hTp:0<T:=zero_lt_one.trans_le hT
  have hεc:0<ε/(4*T):=by positivity
  have hev:∀ᶠn:ℕ in atTop,
      dist (∫t:ℝ,‖χ n t-Complex.exp (-(t:ℂ)^2/2)‖) 0<ε:=by
    filter_upwards[hcore T hT (ε/(4*T)) hεc,htail T hT] with n hcn htn
    have hb:=l1_error_from_core_and_tails (χ n) (fun t:ℝ=>Complex.exp (-(t:ℂ)^2/2))
      (hχ n) gaussian_characteristic_integrable T (ε/(4*T)) _ _ hTp.le hcn htn
      (gaussian_characteristic_uniform_tail T hTp.le)
    have hfactor:2*T*(ε/(4*T))=ε/2:=by field_simp;ring
    rw[hfactor] at hb
    rw[Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun t=>norm_nonneg _))]
    linarith
  exact eventually_atTop.mp hev
end WP.Analysis
