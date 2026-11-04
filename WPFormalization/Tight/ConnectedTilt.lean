import WPFormalization.Tight.ConnectedScale
import WPFormalization.Tight.ConnectedVariance
/-! Relative tight-length scale control under actual Gaussian real tilts.
The reciprocal mean compactification retains both physical endpoints and
places no upper bound on the cusp density. -/
noncomputable section

namespace WP.TightConnected
open Set Filter
open scoped Topology
lemma reciprocal_mean_relative_density (a b η : ℝ) (ha : 0<a) (hb : 0<b)
    (hη : 0 ≤ η) (hηh : η ≤ 1/2)
    (hd : |(1+b)⁻¹-(1+a)⁻¹| *(1+a) ≤ η) :
    |2*b-2*a|/(1+min (2*a) (2*b)) ≤ 4*η := by
  have hda : 0<1+a := by linarith
  have hdb : 0<1+b := by linarith
  have he : |(1+b)⁻¹-(1+a)⁻¹| *(1+a)=|b-a|/(1+b) := by
    rw [show (1+b)⁻¹-(1+a)⁻¹= -(b-a)/((1+b)*(1+a)) by field_simp <;>ring,
      abs_div,abs_neg,abs_mul,abs_of_pos hda,abs_of_pos hdb]
    field_simp
  rw [he] at hd
  have hdiff : |b-a| ≤ η*(1+b) := (div_le_iff₀ hdb).mp hd
  by_cases hab : a ≤ b
  · rw [min_eq_left (by linarith : 2*a ≤ 2*b),abs_of_nonneg (by linarith : 0 ≤ 2*b-2*a)]
    apply (div_le_iff₀ (by linarith : 0<1+2*a)).mpr
    rw [abs_of_nonneg (by linarith : 0 ≤ b-a)] at hdiff
    have hsmall := mul_le_mul_of_nonneg_right hηh (by linarith : 0 ≤ b-a)
    have hδ : b-a ≤ 2*η*(1+a) := by nlinarith
    nlinarith
  · rw [min_eq_right (by linarith : 2*b ≤ 2*a),abs_of_nonpos (by linarith : 2*b-2*a ≤ 0)]
    apply (div_le_iff₀ (by linarith : 0<1+2*b)).mpr
    rw [abs_of_nonpos (by linarith : b-a ≤ 0)] at hdiff
    nlinarith

lemma tightParameterScale_eq_density (x : ℝ) (hx : x∈Ioo 0 xCritical) :
    tightParameterScale (inverseY x)=tightScale (2*Psi x) := by
  unfold tightScale
  rw [show 2*Psi x=density (inverseY x) by unfold Psi;ring,
    Analysis.volume_profile_inverse_density _ (inverseY_branch x ⟨hx.1.le,hx.2⟩).1]
  rfl

lemma connected_tilt_reciprocal_bound (h x u : ℝ) (hh : 0<h)
    (hx : x∈Ioo 0 xCritical)
    (hxt : x*Real.exp (u/Real.sqrt (h*euler Psi x))∈Ioo 0 xCritical) :
    |(1+Psi (x*Real.exp (u/Real.sqrt (h*euler Psi x))))⁻¹-(1+Psi x)⁻¹| *
      (1+Psi x)  ≤  4*|u|/Real.sqrt (min h (h*Psi x)) := by
  have hp := (connected_variance_formula x hx).1
  have hv : 0<euler Psi x := hp.trans_le (BoundaryConvolution.boundary_variance_ge_mean x hx)
  have hm : 0 < min h (h*Psi x) := lt_min hh (mul_pos hh hp)
  have hσ : 0<Real.sqrt (h*euler Psi x) := Real.sqrt_pos.mpr (mul_pos hh hv)
  have hsm : 0<Real.sqrt (min h (h*Psi x)) := Real.sqrt_pos.mpr hm
  have hscale : Real.sqrt (min h (h*Psi x))*(1+Psi x) ≤ 4*Real.sqrt (h*euler Psi x) := by
    have hs := connected_variance_scale_bound h x hh hx
    have hsq := Real.sq_sqrt hm.le
    have hσsq := Real.sq_sqrt (mul_pos hh hv).le
    have hleft : 0 ≤ Real.sqrt (min h (h*Psi x))*(1+Psi x) := by positivity
    nlinarith [sq_nonneg (Real.sqrt (min h (h*Psi x))*(1+Psi x)-4*Real.sqrt (h*euler Psi x))]
  have hd := connected_reciprocal_mean_log_lipschitz x _ hx hxt
  have hlog : Real.log (x*Real.exp (u/Real.sqrt (h*euler Psi x)))-Real.log x=
      u/Real.sqrt (h*euler Psi x) := by rw [Real.log_mul hx.1.ne' (Real.exp_pos _).ne',Real.log_exp];ring
  rw [hlog,abs_div,abs_of_pos hσ] at hd
  calc
    _  ≤  |u|/Real.sqrt (h*euler Psi x)*(1+Psi x) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _  ≤  4*|u|/Real.sqrt (min h (h*Psi x)) := by
      calc
        _ = |u| *(Real.sqrt (min h (h*Psi x))*(1+Psi x))/
            (Real.sqrt (min h (h*Psi x))*Real.sqrt (h*euler Psi x)) := by field_simp
        _  ≤  |u| *(4*Real.sqrt (h*euler Psi x))/
            (Real.sqrt (min h (h*Psi x))*Real.sqrt (h*euler Psi x)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (abs_nonneg u)) (by positivity)
        _ = _ := by field_simp


lemma connected_tight_scale_tilt_uniform (R ε : ℝ) (hR : 0<R) (hε : 0<ε) :
    ∃ M : ℝ, 0<M ∧ ∀ h : ℝ, 0<h → ∀ x∈Ioo (0:ℝ) xCritical,
      M ≤ min h (h*Psi x) → ∀ u : ℝ, |u| ≤ R →
      x*Real.exp (u/Real.sqrt (h*euler Psi x))∈Ioo (0:ℝ) xCritical →
      |tightParameterScale (inverseY (x*Real.exp (u/Real.sqrt (h*euler Psi x))))/
        tightParameterScale (inverseY x)-1| ≤ ε := by
  let η : ℝ := min (1/8) (ε/16)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1/8 := min_le_left _ _
  have hηε : η ≤ ε/16 := min_le_right _ _
  let S : ℝ := 4*R/η+1
  have hS : 0<S := by dsimp [S];positivity
  refine ⟨S^2,sq_pos_of_pos hS,?_⟩
  intro h hh x hx hm u hu hxt
  have hp := (connected_variance_formula x hx).1
  have hpt := (connected_variance_formula _ hxt).1
  have hm0 : 0 < min h (h*Psi x) := lt_min hh (mul_pos hh hp)
  have hsm : 0<Real.sqrt (min h (h*Psi x)) := Real.sqrt_pos.mpr hm0
  have hSsm : S ≤ Real.sqrt (min h (h*Psi x)) := by
    nlinarith [Real.sq_sqrt hm0.le]
  have hR : 4*R/Real.sqrt (min h (h*Psi x)) ≤ η := by
    apply (div_le_iff₀ hsm).mpr
    have hs : 4*R ≤ η*S := by dsimp [S];field_simp;nlinarith
    exact hs.trans (mul_le_mul_of_nonneg_left hSsm hη.le)
  have hd := (connected_tilt_reciprocal_bound h x u hh hx hxt).trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num : 0 ≤ (4:ℝ))) hsm.le).trans hR)
  have hdensity := reciprocal_mean_relative_density (Psi x) (Psi (x*Real.exp (u/Real.sqrt (h*euler Psi x))))
    η hp hpt hη.le (by linarith) hd
  have hlog := tightScale_log_comparison (2*Psi (x*Real.exp (u/Real.sqrt (h*euler Psi x))))
    (2*Psi x) (by positivity) (by positivity)
  rw [←tightParameterScale_eq_density _ hxt,←tightParameterScale_eq_density _ hx] at hlog
  have hlog' : |Real.log (tightParameterScale (inverseY (x*Real.exp (u/Real.sqrt (h*euler Psi x)))))-
      Real.log (tightParameterScale (inverseY x))| ≤ 8*η := by
    apply hlog.trans
    rw [min_comm] at hdensity
    have ht := mul_le_mul_of_nonneg_left hdensity (by norm_num : 0 ≤ (2:ℝ))
    convert ht using 1 <;>ring_nf
  have hlog1 := hlog'.trans (by linarith : 8*η ≤ 1)
  have he := (Real.abs_exp_sub_one_le hlog1).trans (mul_le_mul_of_nonneg_left hlog' (by norm_num : 0 ≤ (2:ℝ)))
  have ha := tightParameterScale_pos _ (inverseY_branch _ ⟨hxt.1.le,hxt.2⟩).1
  have hb := tightParameterScale_pos _ (inverseY_branch _ ⟨hx.1.le,hx.2⟩).1
  rw [Real.exp_sub,Real.exp_log ha,Real.exp_log hb] at he
  exact he.trans (by linarith)

end WP.TightConnected
