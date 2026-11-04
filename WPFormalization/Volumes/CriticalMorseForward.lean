import WPFormalization.Volumes.CriticalMorseNormalization
/-! The actual critical Morse inverse has a common jointly analytic forward coordinate. Both inverse identities, the exact quadratic phase and a uniform quadratic displacement are proved from the existing constructed coordinate data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma analytic_joint_normalized_axis_inverse (F : ℂ × ℂ → ℂ)
    (hF : AnalyticAt ℂ F (0,0)) (hF0 : F (0,0)=0)
    (haxis : ∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0)
    (hFD : ∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=1) :
    ∃G : ℂ × ℂ → ℂ,AnalyticAt ℂ G (0,0) ∧ G (0,0)=0 ∧
      (∀ᶠδ:ℂ in 𝓝 0,G (δ,0)=0) ∧
      (∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>G (δ,u)) 0=1) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),F (z.1,G z)=z.2) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),G (z.1,F z)=z.2) := by
  let T:(ℂ × ℂ) × ℂ → ℂ := fun p=>F (p.1.1,p.2)-p.1.2
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
      (x:=(((0,0),0):(ℂ × ℂ) × ℂ)) hF hinner).sub hfs
  have hT0 : T ((0,0),0)=0 := by simp [T,hF0]
  have hTd : HasDerivAt (fun u:ℂ=>T ((0,0),u)) 1 0 := by
    have hd:=hF.curry_right.differentiableAt.hasDerivAt
    rw [hFD.self_of_nhds] at hd
    convert! hd.sub_const (0:ℂ) using 1
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
  obtain ⟨G,hG,hG0,hGeq,hGunique,hGD⟩ :=
    exists_analytic_implicit_scalar T ((0,0),0) hTa hInv
  have hGzero : G (0,0)=0 := hG0
  have hFG : ∀ᶠz:ℂ × ℂ in 𝓝 (0,0),F (z.1,G z)=z.2 := by
    filter_upwards [hGeq] with z hz
    simpa only [T,hT0,sub_eq_zero] using hz
  have hGaxis : ∀ᶠδ:ℂ in 𝓝 0,G (δ,0)=0 := by
    have hc : ContinuousAt (fun δ:ℂ=>(((δ,0):ℂ × ℂ),(0:ℂ))) 0 := by fun_prop
    filter_upwards [hc.tendsto.eventually hGunique,haxis] with δ hδ hFδ
    apply hδ.mp
    simp [T,hT0,hFδ]
  have hGF : ∀ᶠz:ℂ × ℂ in 𝓝 (0,0),G (z.1,F z)=z.2 := by
    have hc : Tendsto (fun z:ℂ × ℂ=>((z.1,F z),z.2)) (𝓝 (0,0)) (𝓝 (((0,0),0):(ℂ × ℂ) × ℂ)) := by
      simpa only [hF0] using
        ((continuous_fst.continuousAt.prodMk hF.continuousAt).prodMk continuous_snd.continuousAt).tendsto
    filter_upwards [hc.eventually hGunique] with z hz
    apply hz.mp
    simp [T,hT0]
  have hGDaxis : ∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>G (δ,u)) 0=1 := by
    have ht : Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
      (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
    filter_upwards [hGaxis,hFD,ht.eventually hF.eventually_analyticAt,
      ht.eventually hG.eventually_analyticAt,ht.eventually hFG.eventually_nhds]
      with δ hGδ0 hFDδ hFδ hGδ hFGδ
    have hEq : (fun u:ℂ=>F (δ,G (δ,u)))=ᶠ[𝓝 0] (fun u:ℂ=>u) :=
      (show ContinuousAt (fun u:ℂ=>(δ,u)) 0 by fun_prop).tendsto.eventually hFGδ
    have hFd:HasDerivAt (fun u:ℂ=>F (δ,u)) 1 (G (δ,0)) := by
      rw [hGδ0]
      convert! hFδ.curry_right.differentiableAt.hasDerivAt using 1
      exact hFDδ.symm
    have hd:=hFd.comp (h:=fun u:ℂ=>G (δ,u)) 0 hGδ.curry_right.differentiableAt.hasDerivAt
    simpa only [one_mul] using (hd.congr_of_eventuallyEq hEq.symm).unique (hasDerivAt_id 0)
  exact ⟨G,hG,hGzero,hGaxis,hGDaxis,hFG,hGF⟩
lemma CriticalGaussianCoordinateData.exists_forward_morse_coordinate
    (d:CriticalGaussianCoordinateData) :
    ∃ W:ℂ × ℂ → ℂ,AnalyticAt ℂ W (0,0) ∧ W (0,0)=0 ∧
      (∀ᶠδ:ℂ in 𝓝 0,W (δ,0)=0) ∧
      (∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>W (δ,u)) 0=1) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),d.U (z.1,W z)=z.2) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),W (z.1,d.U z)=z.2) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),d.kernel.centeredPhase d.L d.q z=-(W z)^2/2) ∧
      ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ u:ℂ,‖δ‖<ρ → ‖u‖<ρ → ‖W (δ,u)-u‖ ≤ C*‖u‖^2 := by
  obtain ⟨W,hW,hW0,haxis,hderiv,hUW,hWU⟩:=analytic_joint_normalized_axis_inverse
    d.U d.U_analytic d.U_zero d.U_axis d.U_axis_deriv
  have hphase:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),d.kernel.centeredPhase d.L d.q z=-(W z)^2/2 := by
    have ht:Tendsto (fun z:ℂ × ℂ=>(z.1,W z)) (𝓝 (0,0)) (𝓝 ((0,0):ℂ × ℂ)) := by
      simpa only[hW0] using (continuous_fst.continuousAt.prodMk hW.continuousAt).tendsto
    filter_upwards [hUW,ht.eventually d.phase_identity] with z h1 h2
    rw [h1] at h2
    exact h2
  let H:ℂ × ℂ → ℂ:=fun z=>W z-z.2
  have hH:AnalyticAt ℂ H (0,0):=hW.sub analyticAt_snd
  have hHz:∀ᶠδ:ℂ in 𝓝 0,H (δ,0)=0 := by
    filter_upwards[haxis] with δ hδ
    simp[H,hδ]
  have hHD:∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>H (δ,u)) 0=0 := by
    have ht:Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
      (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
    filter_upwards [hderiv,ht.eventually hW.eventually_analyticAt] with δ hd hw
    have hu:=hw.curry_right.differentiableAt.hasDerivAt
    have hsub:HasDerivAt (fun u:ℂ=>H (δ,u)) (0:ℂ) 0 := by
      convert! hu.sub (hasDerivAt_id (0:ℂ)) using 1
      rw[hd]
      ring
    exact hsub.deriv
  exact ⟨W,hW,hW0,haxis,hderiv,hUW,hWU,hphase,analytic_parameter_quadratic_bound H hH hHz hHD⟩
end WP.Analysis
