import WPFormalization.Analysis.ThetaParameter
/-! Exact quartic stationary moments and second derivatives of the actual K kernel.
These are finite integral identities and use only standard Lean axioms. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WP.Analysis
lemma stationaryWeighted_evenQuartic (c₀ c₂ c₄ : ℝ) (g : ℂ → ℂ) (hg : Continuous g) (Y T : ℝ) :
    stationaryWeighted (fun s => c₀+c₂*s^2+c₄*s^4) g Y T =
      c₀*stationaryWeighted (fun _ => 1) g Y T +
      c₂*stationaryWeighted (fun s => s^2) g Y T +
      c₄*stationaryWeighted (fun s => s^4) g Y T := by
  calc
    _ = stationaryWeighted (fun s => (c₀*1+c₂*s^2)+c₄*s^4) g Y T := by congr 1;funext s;ring
    _ = _ := by
      rw [stationaryWeighted_add (fun s => c₀*1+c₂*s^2) (fun s => c₄*s^4)
        (by fun_prop) (by fun_prop) g hg Y T,
        stationaryWeighted_add (fun _ => c₀*1) (fun s => c₂*s^2)
          (by fun_prop) (by fun_prop) g hg Y T,
        stationaryWeighted_smul c₀ (fun _ => 1) continuous_const g hg Y T,
        stationaryWeighted_smul c₂ (fun s => s^2) (by fun_prop) g hg Y T,
        stationaryWeighted_smul c₄ (fun s => s^4) (by fun_prop) g hg Y T]

lemma stationaryWeighted_first_moment_real (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y T : ℝ) :
    stationaryWeighted (fun _ => 1) g Y T -
      2*(T-Y)*stationaryWeighted (fun s => s^2) (deriv g) Y T = (g Y).re := by
  have he := congrArg Complex.re (kernelIntegral_first_moment g hg (Y:ℂ) ((2*(T-Y):ℝ):ℂ))
  rw [stationaryWeighted_kernel_path,stationaryWeighted_kernel_path]
  simpa [Complex.sub_re,Complex.mul_re,Complex.ofReal_pow] using he

lemma stationaryWeighted_relation_real (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y T : ℝ) :
    stationaryWeighted (fun _ => 1) g Y T =
      3*stationaryWeighted (fun s => s^2) g Y T +
      2*(2*(T-Y))*stationaryWeighted (fun s => s^2*(1-s^2)/2) (deriv g) Y T := by
  have he := congrArg Complex.re (kernelIntegral_relation g hg (Y:ℂ) ((2*(T-Y):ℝ):ℂ))
  rw [stationaryWeighted_kernel_path,stationaryWeighted_kernel_path,stationaryWeighted_kernel_path]
  simpa [Complex.add_re,Complex.mul_re,Complex.ofReal_pow] using he

lemma stationaryWeighted_third_moment_real (g : ℂ → ℂ) (hg : Differentiable ℂ g) (Y T : ℝ) :
    3*stationaryWeighted (fun s => s^2) g Y T -
      2*(T-Y)*stationaryWeighted (fun s => s^4) (deriv g) Y T = (g Y).re := by
  have hfirst := stationaryWeighted_first_moment_real g hg Y T
  have hrel := stationaryWeighted_relation_real g hg Y T
  have he : (fun s : ℝ => s^2*(1-s^2)/2) = (fun s => 0+(1/2:ℝ)*s^2+(-1/2:ℝ)*s^4) := by funext s;ring
  rw [he,stationaryWeighted_evenQuartic 0 (1/2) (-1/2) _ hg.deriv.continuous] at hrel
  nlinarith
end WP.Analysis
namespace WP.Analysis
lemma K_second_deriv_integral (Y z : ℂ) :
    iteratedDeriv 2 (K Y) z = ∫ s : ℝ in (0)..1,
      ((1-(s:ℂ)^2)/2)^2*deriv (deriv (deriv X)) (Y+z/2*(1-(s:ℂ)^2)) := by
  have hi : iteratedDeriv 2 (K Y) z = deriv (deriv (K Y)) z := by
    simp only [show 2=Nat.succ (Nat.succ 0) from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  have he : deriv (K Y) = fun w => ∫ s : ℝ in (0)..1,
      ((1-(s:ℂ)^2)/2)*deriv (deriv X) (Y+w/2*(1-(s:ℂ)^2)) :=
    funext (K_deriv_integral Y)
  rw [hi,he,(hasDerivAt_kernelIntegral (fun s : ℝ => (1-(s:ℂ)^2)/2)
    (by fun_prop) (deriv (deriv X)) X_differentiable.deriv.deriv Y z).deriv]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

lemma barK_second_deriv_interior (Y : ℝ) (hY : Y ∈ Ico 0 y₀) (w : ℂ) :
    iteratedDeriv 2 (barK Y) w = (r Y:ℂ)^2*iteratedDeriv 2 (K Y) ((r Y:ℂ)*w)/(a Y:ℂ) := by
  have hb : iteratedDeriv 2 (barK Y) w = deriv (deriv (barK Y)) w := by
    simp only [show 2=Nat.succ (Nat.succ 0) from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  have hk : iteratedDeriv 2 (K Y) ((r Y:ℂ)*w) = deriv (deriv (K Y)) ((r Y:ℂ)*w) := by
    simp only [show 2=Nat.succ (Nat.succ 0) from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  have he : deriv (barK Y) = fun z => (r Y:ℂ)*deriv (K Y) ((r Y:ℂ)*z)/(a Y:ℂ) :=
    funext (barK_deriv_interior Y hY)
  have hd := (((((K_differentiable Y).deriv ((r Y:ℂ)*w)).hasDerivAt.comp w
    ((hasDerivAt_id w).const_mul (r Y:ℂ))).const_mul (r Y:ℂ)).div_const (a Y:ℂ)).deriv
  rw [hb,hk,he]
  simpa only [Function.comp_def, mul_one] using hd.trans (by ring)

lemma barK_second_weighted_T (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (iteratedDeriv 2 (barK Y) 1).re = r Y^2/(4*a Y)*
      stationaryWeighted (fun s => (1-s^2)^2) (deriv (deriv (deriv X))) Y (T Y) := by
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  have hC : stationaryWeighted (fun s => (1-s^2)^2) (deriv (deriv (deriv X))) Y (T Y) =
      4*(iteratedDeriv 2 (K Y) (r Y)).re := by
    rw [stationaryWeighted_kernel_path,hr,K_second_deriv_integral]
    have he : (∫ s : ℝ in (0)..1,((1-s^2)^2:ℝ)*deriv (deriv (deriv X))
        ((Y:ℂ)+(r Y:ℂ)/2*(1-(s:ℂ)^2))) =
        (4:ℂ)*(∫ s : ℝ in (0)..1,((1-(s:ℂ)^2)/2)^2*deriv (deriv (deriv X))
        ((Y:ℂ)+(r Y:ℂ)/2*(1-(s:ℂ)^2))) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      push_cast
      ring
    rw [he]
    norm_num [Complex.mul_re]
  rw [barK_second_deriv_interior Y hY 1,mul_one,Complex.div_ofReal_re,←Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hC]
  ring

lemma barK_first_weighted_T (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (deriv (barK Y) 1).re = r Y/(2*a Y)*
      stationaryWeighted (fun s => 1-s^2) (deriv (deriv X)) Y (T Y) := by
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  rw [stationary_second_moment_T,hr,barK_deriv_interior Y hY 1,mul_one,Complex.div_ofReal_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
end WP.Analysis
