import WPFormalization.Analysis.ParameterHadamard
import WPFormalization.Analysis.AnalyticImplicitScalar
import WPFormalization.Volumes.CriticalPhaseCalculus
/-! A common analytic Morse inverse for a genuinely jointly analytic normalized phase.
Parameter Hadamard division and Mathlib analytic implicit functions prove the
coordinate and exact quadratic identity without any additional classical input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma exists_joint_normalized_morse_inverse (F : ℂ × ℂ → ℂ)
    (hF : AnalyticAt ℂ F (0,0))
    (haxis : ∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0)
    (hderiv : ∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=0)
    (hsecond : iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0=-1) :
    ∃ U:ℂ × ℂ→ℂ,AnalyticAt ℂ U (0,0) ∧ U (0,0)=0 ∧
      (∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0) ∧
      deriv (fun w:ℂ=>U (0,w)) 0=1 ∧
      ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),F (p.1,U p)=-(p.2)^2/2 := by
  obtain ⟨G,hG,hG0,hfac⟩ := exists_analytic_parameter_square_factor_with_value F hF haxis hderiv
  have hGv : G (0,0)=-(1/2:ℂ) := by
    change G 0=-(1/2:ℂ)
    rw [hG0,hsecond]
    ring
  have hunit : -2*G (0,0)=1 := by rw [hGv];ring
  let W:ℂ × ℂ→ℂ := fun p=>p.2*Complex.sqrt (-2*G p)
  have hS : AnalyticAt ℂ (fun p:ℂ × ℂ=>Complex.sqrt (-2*G p)) (0,0) := by
    have hs : AnalyticAt ℂ Complex.sqrt (-2*G (0,0)) :=
      complex_sqrt_analyticAt (by rw [hunit];exact Or.inl (by norm_num))
    exact AnalyticAt.comp (f:=fun p:ℂ × ℂ=>-2*G p) (x:=(0,0)) hs (analyticAt_const.mul hG)
  have hW : AnalyticAt ℂ W (0,0) := analyticAt_snd.mul hS
  have hW0 : W (0,0)=0 := by simp [W]
  have hWd : HasDerivAt (fun u:ℂ=>W (0,u)) 1 0 := by
    have hs := hS.curry_right.differentiableAt.hasDerivAt
    convert! (hasDerivAt_id (0:ℂ)).mul hs using 1
    simp only [id_eq,zero_mul,one_mul,add_zero,hunit,Complex.sqrt_one]
  let T:(ℂ × ℂ) × ℂ→ℂ := fun p=>W (p.1.1,p.2)-p.1.2
  have hf1 := (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ).analyticAt (((0,0),0):(ℂ × ℂ) × ℂ)
  have hff : AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>p.1.1) ((0,0),0) :=
    AnalyticAt.comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) (x:=(((0,0),0):(ℂ × ℂ) × ℂ))
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt ((0,0):ℂ × ℂ)) hf1
  have hfs : AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>p.1.2) ((0,0),0) :=
    AnalyticAt.comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) (x:=(((0,0),0):(ℂ × ℂ) × ℂ))
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt ((0,0):ℂ × ℂ)) hf1
  have hinner : AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>(p.1.1,p.2)) ((0,0),0) :=
    hff.prod analyticAt_snd
  have hTa : AnalyticAt ℂ T ((0,0),0) :=
    (AnalyticAt.comp (f:=fun p:(ℂ × ℂ) × ℂ=>(p.1.1,p.2))
      (x:=(((0,0),0):(ℂ × ℂ) × ℂ)) hW hinner).sub hfs
  have hT0 : T ((0,0),0)=0 := by simp [T,hW0]
  have hTd : HasDerivAt (fun u:ℂ=>T ((0,0),u)) 1 0 := by
    convert! hWd.sub_const (0:ℂ) using 1
  have hcurve : HasDerivAt (fun u:ℂ=>(((0,0):ℂ × ℂ),u))
      (((0,0),1):(ℂ × ℂ) × ℂ) 0 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hDf := hTa.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hDval := hTd.unique hDf
  have hInv : (fderiv ℂ T ((0,0),0) ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible := by
    apply complex_clm_isInvertible_of_apply_one_ne_zero
    change fderiv ℂ T ((0,0),0) ((0,0),1)≠0
    rw [←hDval]
    norm_num
  obtain ⟨U,hU,hU0,hUeq,hUunique,hUD⟩ :=
    exists_analytic_implicit_scalar T ((0,0),0) hTa hInv
  have hUzero : U (0,0)=0 := hU0
  have hWeq : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),W (p.1,U p)=p.2 := by
    filter_upwards [hUeq] with p hp
    simpa only [T,hT0,sub_eq_zero] using hp
  have hUaxis : ∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0 := by
    have hc : ContinuousAt (fun δ:ℂ=>(((δ,0):ℂ × ℂ),(0:ℂ))) 0 := by fun_prop
    filter_upwards [hc.tendsto.eventually hUunique] with δ hδ
    apply hδ.mp
    simp [T,W,hT0]
  have hDU : deriv (fun w:ℂ=>U (0,w)) 0=1 := by
    have hs : HasDerivAt (fun w:ℂ=>U (0,w)) (deriv (fun w:ℂ=>U (0,w)) 0) 0 := by
      simpa using hU.curry_right.differentiableAt.hasDerivAt
    have hw : HasDerivAt (fun w:ℂ=>W (0,U (0,w))) (deriv (fun w:ℂ=>U (0,w)) 0) 0 := by
      have hWd' : HasDerivAt (fun u:ℂ=>W (0,u)) 1 (U (0,0)) := by simpa only [hUzero] using hWd
      convert! hWd'.comp (h:=fun w:ℂ=>U (0,w)) 0 hs using 1 <;> simp only [one_mul]
    have hc : ContinuousAt (fun w:ℂ=>((0:ℂ),w)) 0 := by fun_prop
    have he : (fun w:ℂ=>W (0,U (0,w))) =ᶠ[𝓝 0] (fun w:ℂ=>w) := hc.tendsto.eventually hWeq
    exact (hw.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id 0)
  refine ⟨U,hU,hUzero,hUaxis,hDU,?_⟩
  have hct : Tendsto (fun p:ℂ × ℂ=>(p.1,U p)) (𝓝 (0,0)) (𝓝 ((0,0):ℂ × ℂ)) := by
    simpa only [hUzero] using (continuous_fst.continuousAt.prodMk hU.continuousAt).tendsto
  filter_upwards [hWeq,hct.eventually hfac] with p hwp hfp
  have hs : W (p.1,U p)^2=-2*F (p.1,U p) := by
    dsimp only [W]
    rw [mul_pow,complex_sqrt_sq,hfp]
    ring
  rw [hwp] at hs
  linear_combination hs/2
end WP.Analysis
