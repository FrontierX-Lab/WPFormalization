import WPFormalization.Analysis.ThetaParameter
/-! Actual first-moment and logarithmic parameter identities.
The finite integral moment gives J-X = A*a*r. Together with the actual
stationary and root derivatives it proves the logarithmic derivatives of
A and the normalized action A*a*r^(3/2). Derivatives are stated on the open
physical interval; no value of the totalized first-root definition at y₀
or unproved continuation across an endpoint is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma stationary_first_moment_eq_Aa (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    stationaryWeighted (fun s => s^2) (deriv X) Y (T Y) = A Y*a Y := by
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  have hH : (H Y (r Y)).re = 3*stationaryWeighted (fun s => s^2) (deriv X) Y (T Y) := by
    rw [stationaryWeighted_kernel_path,hr]
    simp [H,Complex.ofReal_pow,Complex.mul_re]
  have hb : (barH Y 1).re=(H Y (r Y)).re/a Y := by
    rw [barH,if_neg (ne_of_lt hY.2),mul_one,Complex.div_ofReal_re]
  unfold A
  rw [hb,hH]
  field_simp [(a_pos Y hY).ne']

lemma J_sub_XR_eq_Aar (Y : ℝ) (hY : Y ∈ Ico 0 y₀) : J Y-XR Y=A Y*a Y*r Y := by
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  have hJ : (∫ s : ℝ in (0)..1,X ((Y:ℂ)+(r Y:ℂ)/2*(1-(s:ℂ)^2))).re=J Y := by
    rw [←stationaryWeighted_one_X Y,stationaryWeighted_kernel_path,hr]
    simp
  have hM : (∫ s : ℝ in (0)..1,(s:ℂ)^2*deriv X ((Y:ℂ)+(r Y:ℂ)/2*(1-(s:ℂ)^2))).re=
      stationaryWeighted (fun s => s^2) (deriv X) Y (T Y) := by
    rw [stationaryWeighted_kernel_path,hr]
    simp [Complex.ofReal_pow]
  have he := congrArg Complex.re (kernelIntegral_first_moment X X_differentiable
    (Y:ℂ) ((2*(T Y-Y):ℝ):ℂ))
  rw [hr] at he
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at he
  rw [hJ,hM,stationary_first_moment_eq_Aa Y hY] at he
  change J Y-r Y*(A Y*a Y)=XR Y at he
  nlinarith
end WP.Analysis
namespace WP.Analysis
lemma logA_hasDerivAt_open_parameter (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun x => Real.log (A x))
      (((3/2:ℝ)*(∑' l : ℕ, weight Y l)+3-1/A Y)/r Y-deriv a Y/a Y) Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have ha := a_pos Y hYi
  have hr := r_pos Y hYi
  have hA : 0 < A Y := by unfold A;exact div_pos (barH_one_re_pos Y ⟨hY.1.le,hY.2.le⟩) (by norm_num)
  have hdF := (J_hasDerivAt_interior Y hYi).sub (XR_hasDerivAt Y)
  have hda : HasDerivAt a (deriv a Y) Y := (a_hasDerivAt Y).differentiableAt.hasDerivAt
  have hdDen := hda.mul (r_hasDerivAt_open_parameter Y hY)
  have hd := hdF.div hdDen (mul_pos ha hr).ne'
  have he : A =ᶠ[𝓝 Y] (fun x => (J x-XR x)/(a x*r x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    rw [J_sub_XR_eq_Aar x ⟨hx.1.le,hx.2⟩]
    field_simp [(a_pos x ⟨hx.1.le,hx.2⟩).ne',(r_pos x ⟨hx.1.le,hx.2⟩).ne']
  have hactual := hd.congr_of_eventuallyEq he
  have hlog := hactual.log hA.ne'
  convert hlog using 1
  dsimp only [Pi.mul_apply,Pi.sub_apply]
  rw [stationary_first_moment_eq_Aa Y hYi,J_sub_XR_eq_Aar Y hYi,Theta_eq_neg_two_T_deriv Y hYi]
  field_simp [ha.ne',hr.ne',hA.ne']
  ring
end WP.Analysis
namespace WP.Analysis
lemma logNormalizedAction_hasDerivAt_open_parameter (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun x => Real.log (A x*a x*Real.rpow (r x) (3/2:ℝ)))
      (-1/(A Y*r Y)) Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have ha := a_pos Y hYi
  have hr := r_pos Y hYi
  have hA : 0 < A Y := by unfold A;exact div_pos (barH_one_re_pos Y ⟨hY.1.le,hY.2.le⟩) (by norm_num)
  have hda : HasDerivAt a (deriv a Y) Y := (a_hasDerivAt Y).differentiableAt.hasDerivAt
  have hd := ((logA_hasDerivAt_open_parameter Y hY).add (hda.log ha.ne')).add
    (((r_hasDerivAt_open_parameter Y hY).log hr.ne').const_mul (3/2:ℝ))
  have he : (fun x => Real.log (A x*a x*Real.rpow (r x) (3/2:ℝ))) =ᶠ[𝓝 Y]
      (fun x => Real.log (A x)+Real.log (a x)+(3/2:ℝ)*Real.log (r x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    have hax := a_pos x ⟨hx.1.le,hx.2⟩
    have hrx := r_pos x ⟨hx.1.le,hx.2⟩
    have hAx : 0 < A x := by unfold A;exact div_pos (barH_one_re_pos x ⟨hx.1.le,hx.2.le⟩) (by norm_num)
    rw [Real.rpow_eq_pow]
    rw [Real.log_mul (mul_ne_zero hAx.ne' hax.ne') (Real.rpow_pos_of_pos hrx (3/2:ℝ)).ne',
      Real.log_mul hAx.ne' hax.ne',Real.log_rpow hrx]
  have hd' := hd.congr_of_eventuallyEq he
  convert hd' using 1
  field_simp [ha.ne',hr.ne',hA.ne']
  ring
end WP.Analysis
