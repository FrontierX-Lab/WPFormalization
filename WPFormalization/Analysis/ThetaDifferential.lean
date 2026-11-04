import WPFormalization.Analysis.ParameterODE
import WPFormalization.Analysis.StationaryHigherMoments
/-! The actual parameter derivative of the canonical mass Theta and the exact
transport primitive from PF10-PF11. Derivatives are taken only for 0 < Y < y₀;
no value of the total first-root definition at y₀ is used. The proof differentiates
the exact stationary equation and its finite integral moments. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WP.Analysis
lemma theta_moment_algebra (r a t D m₀ m₂ d₀ d₂ d₄ ap t₂ M : ℝ)
    (hr : r ≠ 0) (ha : a ≠ 0) (ht : t ≠ 0) (hD : D ≠ 0)
    (hm : -r*m₂=a) (hs : m₂+t*D=0) (hdef : D=m₀-m₂)
    (hf : m₀-r*d₂=ap) (htm : 3*m₂-r*d₄=ap)
    (hM : M=(r^2/(4*a)*(d₀-2*d₂+d₄))/(2*(r/(2*a)*D)^2))
    (hsecond : t^2*d₀+2*t*(1-t)*d₂+(1-t)^2*d₄+t₂*D=0) :
    t₂/t=ap/a+(-4*t+1-2*M)/r := by
  have htd : r*t*D=a := by linear_combination r*hs+hm
  have hM' : 2*M*D^2=a*(d₀-2*d₂+d₄) := by
    field_simp [hr,ha,hD] at hM
    nlinarith only [hM]
  have hTC : r^2*t^2*(d₀-2*d₂+d₄)=2*a*M := by
    apply (mul_left_cancel₀ ha)
    calc
      a*(r^2*t^2*(d₀-2*d₂+d₄)) = r^2*t^2*(2*M*D^2) := by rw [hM'];ring
      _ = 2*M*(r*t*D)^2 := by ring
      _ = a*(2*a*M) := by rw [htd];ring
  have hsec : r^2*t^2*(d₀-2*d₂+d₄)+(4*t-1)*a-r*ap+r^2*t₂*D=0 := by
    linear_combination r^2*hsecond + (r*(1-2*t))*htm + (2*r*t)*hf +
      (2*r*t)*hdef + (3-4*t)*hm - 2*htd
  have hfinal : a*r*t₂=r*t*ap+a*t*(-4*t+1-2*M) := by
    rw [hTC] at hsec
    linear_combination t*hsec - (r*t₂)*htd
  field_simp [ha,hr,ht]
  linear_combination hfinal
end WP.Analysis
namespace WP.Analysis
lemma T_second_logarithmic_deriv (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    iteratedDeriv 2 T Y/deriv T Y = deriv a Y/a Y+
      (-4*deriv T Y+1-2*(∑' l : ℕ,(l:ℝ)*weight Y l))/r Y := by
  let m₀ := stationaryWeighted (fun _ => 1) (deriv (deriv X)) Y (T Y)
  let m₂ := stationaryWeighted (fun s => s^2) (deriv (deriv X)) Y (T Y)
  let D := stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) Y (T Y)
  let d₀ := stationaryWeighted (fun _ => 1) (deriv (deriv (deriv X))) Y (T Y)
  let d₂ := stationaryWeighted (fun s => s^2) (deriv (deriv (deriv X))) Y (T Y)
  let d₄ := stationaryWeighted (fun s => s^4) (deriv (deriv (deriv X))) Y (T Y)
  have hg := X_differentiable.deriv.deriv.deriv.continuous
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  have hD : D=m₀-m₂ := by
    dsimp [D,m₀,m₂]
    have he : (fun s : ℝ => 1-s^2) = (fun s => 1+(-1)*s^2+0*s^4) := by funext s;ring
    rw [he,stationaryWeighted_evenQuartic 1 (-1) 0 _ X_differentiable.deriv.deriv.continuous]
    ring
  have hC : stationaryWeighted (fun s => (1-s^2)^2) (deriv (deriv (deriv X))) Y (T Y) =
      d₀-2*d₂+d₄ := by
    have he : (fun s : ℝ => (1-s^2)^2) = (fun s => 1+(-2)*s^2+1*s^4) := by funext s;ring
    rw [he,stationaryWeighted_evenQuartic 1 (-2) 1 _ hg]
    dsimp [d₀,d₂,d₄]
    ring
  have hm := stationary_second_moment_identity Y (T Y)
  rw [(T_root_on_stationaryParameterDomain Y (stationaryParameterDomain_contains Y hY)).2,hr] at hm
  have hs := T_deriv_stationary_equation_on_domain Y (stationaryParameterDomain_contains Y hY)
  have hap : deriv a Y=(deriv (deriv X) (Y:ℂ)).re := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using (a_hasDerivAt Y).deriv
  have hf := stationaryWeighted_first_moment_real (deriv (deriv X)) X_differentiable.deriv.deriv Y (T Y)
  have htm := stationaryWeighted_third_moment_real (deriv (deriv X)) X_differentiable.deriv.deriv Y (T Y)
  rw [hr,←hap] at hf htm
  have hM := first_weight_moment_kernel_deriv Y ⟨hY.1,hY.2.le⟩
  rw [barK_second_weighted_T Y hY,barK_first_weighted_T Y hY,hC] at hM
  have hsecond := T_second_deriv_stationary_equation_on_domain Y (stationaryParameterDomain_contains Y hY)
  have he : (fun s : ℝ => (s^2+deriv T Y*(1-s^2))^2) =
      (fun s => (deriv T Y)^2+ (2*deriv T Y*(1-deriv T Y))*s^2+(1-deriv T Y)^2*s^4) := by funext s;ring
  rw [he,stationaryWeighted_evenQuartic _ _ _ _ hg] at hsecond
  have hDn : D ≠ 0 := by
    have hd := stationary_second_moment_T Y (T Y)
    rw [hr] at hd
    change D=_ at hd
    rw [hd]
    exact mul_ne_zero (by norm_num) (K_deriv_at_r_re_neg Y hY).ne
  exact theta_moment_algebra (r Y) (a Y) (deriv T Y) D m₀ m₂ d₀ d₂ d₄
    (deriv a Y) (iteratedDeriv 2 T Y) _ (r_pos Y hY).ne' (a_pos Y hY).ne'
    (T_deriv_neg_interior Y hY).ne hDn (by simpa using hm) hs hD hf htm hM hsecond
end WP.Analysis
namespace WP.Analysis
lemma logTheta_hasDerivAt_open_parameter (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun x => Real.log (∑' l : ℕ,weight x l))
      (deriv a Y/a Y+(2*(∑' l : ℕ,weight Y l)+1-
        2*(∑' l : ℕ,(l:ℝ)*weight Y l))/r Y) Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have ht := T_deriv_neg_interior Y hYi
  have hd₂ : HasDerivAt (deriv T) (iteratedDeriv 2 T Y) Y := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one] using
      (T_analyticAt_interior Y hYi).deriv.differentiableAt.hasDerivAt
  have he : (fun x => ∑' l : ℕ,weight x l) =ᶠ[𝓝 Y] (fun x => -2*deriv T x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    exact Theta_eq_neg_two_T_deriv x ⟨hx.1.le,hx.2⟩
  have hd := (hd₂.const_mul (-2:ℝ)).congr_of_eventuallyEq he
  have hpos : 0 < ∑' l : ℕ,weight Y l := by
    rw [Theta_eq_neg_two_T_deriv Y hYi]
    linarith
  have hq : (-2*iteratedDeriv 2 T Y)/(∑' l : ℕ,weight Y l) =
      iteratedDeriv 2 T Y/deriv T Y := by
    rw [Theta_eq_neg_two_T_deriv Y hYi]
    field_simp [ht.ne]
  have hlog := hd.log hpos.ne'
  rw [hq,T_second_logarithmic_deriv Y hYi] at hlog
  convert hlog using 1
  rw [Theta_eq_neg_two_T_deriv Y hYi]
  ring
end WP.Analysis
namespace WP.Analysis
lemma transportPrimitive_hasDerivAt_open_parameter (p : ℕ) (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt (fun x => (1/2:ℝ)*Real.log (A x*(∑' l : ℕ,weight x l))+
        ((p:ℝ)/2)*Real.log (r x))
      ((A Y*((7-2*(p:ℝ))/4*(∑' l : ℕ,weight Y l)-
          (∑' l : ℕ,(l:ℝ)*weight Y l)+2-p)-1/2)/(A Y*r Y)) Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have hr := r_pos Y hYi
  have hA : 0 < A Y := by
    unfold A
    exact div_pos (barH_one_re_pos Y ⟨hY.1.le,hY.2.le⟩) (by norm_num)
  have hd := (((logA_hasDerivAt_open_parameter Y hY).add
      (logTheta_hasDerivAt_open_parameter Y hY)).const_mul (1/2:ℝ)).add
    (((r_hasDerivAt_open_parameter Y hY).log hr.ne').const_mul ((p:ℝ)/2))
  have he : (fun x => (1/2:ℝ)*Real.log (A x*(∑' l : ℕ,weight x l))+
        ((p:ℝ)/2)*Real.log (r x)) =ᶠ[𝓝 Y]
      (fun x => (1/2:ℝ)*(Real.log (A x)+Real.log (∑' l : ℕ,weight x l))+
        ((p:ℝ)/2)*Real.log (r x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    have hAx : 0 < A x := by
      unfold A
      exact div_pos (barH_one_re_pos x ⟨hx.1.le,hx.2.le⟩) (by norm_num)
    have htx : 0 < ∑' l : ℕ,weight x l := by
      rw [Theta_eq_neg_two_T_deriv x ⟨hx.1.le,hx.2⟩]
      have ht := T_deriv_neg_interior x ⟨hx.1.le,hx.2⟩
      linarith
    rw [Real.log_mul hAx.ne' htx.ne']
  convert hd.congr_of_eventuallyEq he using 1
  field_simp [hA.ne',hr.ne',(a_pos Y hYi).ne']
  ring
end WP.Analysis
