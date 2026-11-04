import Mathlib
/-! Uniform quadratic upper control for the logarithmic Legendre defect, including the origin. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis
open Set

def logarithmicLegendreDefect (F μ:ℝ→ℝ)(R z:ℝ):ℝ:=
  F R-F z-μ z*(Real.log R-Real.log z)

lemma logarithmicLegendreDefect_uniform_quadratic (F μ:ℝ→ℝ)(R C:ℝ)
    (hR:0 < R)(hC:0 < C)
    (hF:∀t∈Icc (0:ℝ) R,DifferentiableAt ℝ F t)
    (hμ:∀t∈Icc (0:ℝ) R,DifferentiableAt ℝ μ t)
    (hμeq:∀t∈Icc (0:ℝ) R,μ t=t*deriv F t)
    (hdμ:∀t∈Icc (0:ℝ) R,1/5 ≤ deriv μ t∧deriv μ t ≤ C)
    (hc:ContinuousOn (logarithmicLegendreDefect F μ R) (Icc (0:ℝ) R)):
    ∃B:ℝ,0 < B∧∀z∈Icc (0:ℝ) R,
      logarithmicLegendreDefect F μ R z ≤ B*(μ R-μ z)^2:=by
  obtain ⟨zmax,hzmax,hmax⟩:=isCompact_Icc.exists_isMaxOn (f:=logarithmicLegendreDefect F μ R)
    ⟨0,le_rfl,hR.le⟩ hc
  let M:ℝ:=|logarithmicLegendreDefect F μ R zmax|+1
  have hM:0 < M:=by dsimp[M];positivity
  have hbound:∀z∈Icc (0:ℝ) R,logarithmicLegendreDefect F μ R z ≤ M:=by
    intro z hz
    have ht:=(isMaxOn_iff.mp hmax) z hz
    dsimp[M]
    linarith only[ht,le_abs_self (logarithmicLegendreDefect F μ R zmax)]
  let B:ℝ:=max (50*C/R) (100*M/R^2)
  have hB:0 < B:=lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro z hz
  have hcont:ContinuousOn μ (Icc (0:ℝ) R):=fun t ht=>(hμ t ht).continuousAt.continuousWithinAt
  have hdiff:DifferentiableOn ℝ μ (interior (Icc (0:ℝ) R)):=
    fun t ht=>(hμ t (interior_subset ht)).differentiableWithinAt
  have hlo:1/5*(R-z) ≤ μ R-μ z:=
    (convex_Icc (0:ℝ) R).mul_sub_le_image_sub_of_le_deriv hcont hdiff
      (fun t ht=>(hdμ t (interior_subset ht)).1) z hz R ⟨hR.le,le_rfl⟩ hz.2
  have hΔ:0 ≤ R-z:=sub_nonneg.mpr hz.2
  have hδ:0 ≤ μ R-μ z:=by nlinarith only[hlo,hΔ]
  have hscale:R-z ≤ 5*(μ R-μ z):=by nlinarith only[hlo]
  by_cases hnear:R/2 ≤ z
  · have hzpos:0 < z:=(half_pos hR).trans_le hnear
    let G:ℝ→ℝ:=fun t=>F t-μ z*Real.log t
    have hder:∀t∈Icc z R,HasDerivAt G ((μ t-μ z)/t) t:=by
      intro t ht
      have htpos:0 < t:=hzpos.trans_le ht.1
      have htfull:t∈Icc (0:ℝ) R:=⟨htpos.le,ht.2⟩
      have H:HasDerivAt G (deriv F t-μ z*t⁻¹) t:=
        (hF t htfull).hasDerivAt.sub ((Real.hasDerivAt_log htpos.ne').const_mul (μ z))
      convert H using 1
      have he:=hμeq t htfull
      field_simp
      nlinarith only[he]
    have hdu:∀t∈Icc z R,deriv G t ≤ (2*C/R)*(R-z):=by
      intro t ht
      have htpos:0 < t:=hzpos.trans_le ht.1
      have htfull:t∈Icc (0:ℝ) R:=⟨htpos.le,ht.2⟩
      have hi:μ t-μ z ≤ C*(t-z):=
        (convex_Icc (0:ℝ) R).image_sub_le_mul_sub_of_deriv_le hcont hdiff
          (fun t ht=>(hdμ t (interior_subset ht)).2) z hz t htfull ht.1
      rw[(hder t ht).deriv]
      calc
        _ ≤ C*(R-z)/t:=div_le_div_of_nonneg_right
          (hi.trans (mul_le_mul_of_nonneg_left (by linarith only[ht.2]) hC.le)) htpos.le
        _ ≤ C*(R-z)/(R/2):=div_le_div_of_nonneg_left (mul_nonneg hC.le hΔ) (half_pos hR) (hnear.trans ht.1)
        _ = _:=by ring
    have hG:ContinuousOn G (Icc z R):=fun t ht=>(hder t ht).continuousAt.continuousWithinAt
    have hGd:DifferentiableOn ℝ G (interior (Icc z R)):=
      fun t ht=>(hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    have ht: G R-G z ≤ ((2*C/R)*(R-z))*(R-z):=
      (convex_Icc z R).image_sub_le_mul_sub_of_deriv_le hG hGd
        (fun t ht=>hdu t (interior_subset ht)) z ⟨le_rfl,hz.2⟩ R ⟨hz.2,le_rfl⟩ hz.2
    have hs:(R-z)^2 ≤ 25*(μ R-μ z)^2:=by
      have H: (R-z)^2 ≤ (5*(μ R-μ z))^2:=
        (sq_le_sq₀ hΔ (mul_nonneg (by norm_num) hδ)).mpr hscale
      nlinarith only[H]
    calc
      _ = G R-G z:=by dsimp[logarithmicLegendreDefect,G];ring
      _ ≤ (2*C/R)*(R-z)^2:=by nlinarith only[ht]
      _ ≤ (2*C/R)*(25*(μ R-μ z)^2):=mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (50*C/R)*(μ R-μ z)^2:=by ring
      _ ≤ B*(μ R-μ z)^2:=mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hfar:z ≤ R/2:=le_of_not_ge hnear
    have hd:R/10 ≤ μ R-μ z:=by nlinarith only[hlo,hfar]
    have hs:R^2/100 ≤ (μ R-μ z)^2:=by
      have H:(R/10)^2 ≤ (μ R-μ z)^2:=
        (sq_le_sq₀ (div_nonneg hR.le (by norm_num)) hδ).mpr hd
      nlinarith only[H]
    calc
      _ ≤ M:=hbound z hz
      _ = (100*M/R^2)*(R^2/100):=by field_simp
      _ ≤ (100*M/R^2)*(μ R-μ z)^2:=mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ B*(μ R-μ z)^2:=mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
end WP.Analysis
