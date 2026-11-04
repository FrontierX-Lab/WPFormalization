import WPFormalization.Analysis.StationaryQ

/-! Actual weighted affine integrals and differentiation along a real path.
All integral substitutions and finite linearity identities use the original
complex entire function, with no model or coefficient interface. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
/-- An actual weighted compact integral along the stationary affine path. -/
def stationaryWeighted (q : ℝ → ℝ) (g : ℂ → ℂ) (Y T : ℝ) : ℝ :=
  (∫ s : ℝ in (0)..1,(q s : ℂ)*g (stationaryQLinear s ((Y : ℂ),(T : ℂ)))).re
lemma stationaryWeighted_hasDerivAt_comp (q : ℝ → ℝ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (b : ℝ → ℝ) (Y b' : ℝ)
    (hb : HasDerivAt b b' Y) :
    HasDerivAt (fun x : ℝ => stationaryWeighted q g x (b x))
      (stationaryWeighted (fun s => q s*(s^2+b'*(1-s^2))) (deriv g) Y (b Y)) Y := by
  let p : ComplexPair := ((Y : ℂ),(b Y : ℂ))
  let v : ComplexPair := (1,(b' : ℂ))
  have hqC : Continuous (fun s : ℝ => (q s : ℂ)) := Complex.continuous_ofReal.comp hq
  have hf : HasFDerivAt
      (fun w : ComplexPair => ∫ s : ℝ in (0)..1,(q s : ℂ)*g (stationaryQLinear s w))
      (∫ s : ℝ in (0)..1,((q s : ℂ)*deriv g (stationaryQLinear s p)) • stationaryQLinear s) p := by
    simpa only [zero_add] using hasFDerivAt_affineIntegral_prod
      (fun s => (q s : ℂ)) (fun _ => 0) stationaryQLinear hqC continuous_const stationaryQLinear_continuous g hg p
  have hbC : HasDerivAt (fun x : ℝ => (b x : ℂ)) (b' : ℂ) Y :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt Y hb
  have hpair : HasDerivAt (fun x : ℝ => ((x : ℂ),(b x : ℂ))) v Y :=
    Complex.ofRealCLM.hasDerivAt.prodMk hbC
  have hcomp := (hf.restrictScalars ℝ).comp_hasDerivAt Y hpair
  have hout := Complex.reCLM.hasFDerivAt.comp_hasDerivAt Y hcomp
  have hc : Continuous (deriv g) := continuous_iff_continuousAt.mpr
    (fun z => ((hg.analyticAt z).deriv).continuousAt)
  have hi : IntervalIntegrable
      (fun s : ℝ => ((q s : ℂ)*deriv g (stationaryQLinear s p)) • stationaryQLinear s) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hL := stationaryQLinear_continuous
    fun_prop
  have heval : (∫ s : ℝ in (0)..1,((q s : ℂ)*deriv g (stationaryQLinear s p)) • stationaryQLinear s) v =
      ∫ s : ℝ in (0)..1,((q s*(s^2+b'*(1-s^2)) : ℝ) : ℂ)*deriv g (stationaryQLinear s p) := by
    rw [ContinuousLinearMap.intervalIntegral_apply hi]
    apply intervalIntegral.integral_congr
    intro s hs
    have hlin : stationaryQLinear s v = (s : ℂ)^2+(1-(s : ℂ)^2)*(b' : ℂ) := by
      change (s : ℂ)^2*1+(1-(s : ℂ)^2)*(b' : ℂ) = _
      rw [mul_one]
    change (((q s : ℂ)*deriv g (stationaryQLinear s p)) • stationaryQLinear s) v =
      ((q s*(s^2+b'*(1-s^2)) : ℝ) : ℂ)*deriv g (stationaryQLinear s p)
    rw [ContinuousLinearMap.smul_apply,hlin]
    simp only [smul_eq_mul]
    push_cast
    ring
  change HasDerivAt (fun x : ℝ => stationaryWeighted q g x (b x))
    ((∫ s : ℝ in (0)..1,((q s : ℂ)*deriv g (stationaryQLinear s p)) • stationaryQLinear s) v).re Y at hout
  rw [heval] at hout
  exact hout
lemma stationaryWeighted_real_integral (q : ℝ → ℝ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Continuous g) (Y T : ℝ) :
    stationaryWeighted q g Y T =
      ∫ s : ℝ in (0)..1,q s*(g ((T-(T-Y)*s^2 : ℝ) : ℂ)).re := by
  have hL := stationaryQLinear_continuous
  have hi : IntervalIntegrable
      (fun s : ℝ => (q s : ℂ)*g (stationaryQLinear s ((Y : ℂ),(T : ℂ)))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold stationaryWeighted
  change Complex.reCLM (∫ s : ℝ in (0)..1,(q s : ℂ)*g (stationaryQLinear s ((Y : ℂ),(T : ℂ)))) = _
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s hs
  have he : stationaryQLinear s ((Y : ℂ),(T : ℂ)) = ((T-(T-Y)*s^2 : ℝ) : ℂ) := by
    change (s : ℂ)^2*(Y : ℂ)+(1-(s : ℂ)^2)*(T : ℂ) = _
    push_cast
    ring
  change ((q s : ℂ)*g (stationaryQLinear s ((Y : ℂ),(T : ℂ)))).re = _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
lemma stationaryWeighted_add (q₁ q₂ : ℝ → ℝ) (hq₁ : Continuous q₁) (hq₂ : Continuous q₂)
    (g : ℂ → ℂ) (hg : Continuous g) (Y T : ℝ) :
    stationaryWeighted (fun s => q₁ s+q₂ s) g Y T =
      stationaryWeighted q₁ g Y T+stationaryWeighted q₂ g Y T := by
  rw [stationaryWeighted_real_integral (fun s => q₁ s+q₂ s) (by fun_prop) _ hg,
    stationaryWeighted_real_integral q₁ hq₁ _ hg,stationaryWeighted_real_integral q₂ hq₂ _ hg]
  have hi₁ : IntervalIntegrable (fun s : ℝ => q₁ s*(g ((T-(T-Y)*s^2 : ℝ) : ℂ)).re) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi₂ : IntervalIntegrable (fun s : ℝ => q₂ s*(g ((T-(T-Y)*s^2 : ℝ) : ℂ)).re) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_add hi₁ hi₂]
  apply intervalIntegral.integral_congr
  intro s hs
  ring
lemma stationaryWeighted_smul (c : ℝ) (q : ℝ → ℝ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Continuous g) (Y T : ℝ) :
    stationaryWeighted (fun s => c*q s) g Y T = c*stationaryWeighted q g Y T := by
  rw [stationaryWeighted_real_integral (fun s => c*q s) (by fun_prop) _ hg,
    stationaryWeighted_real_integral q hq _ hg,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  ring
lemma stationaryWeighted_one_derivX (Y T : ℝ) :
    stationaryWeighted (fun _ => 1) (deriv X) Y T = stationaryQReal Y T := by
  unfold stationaryWeighted stationaryQReal stationaryQProd
  simp only [Complex.ofReal_one,one_mul]


end WP.Analysis
