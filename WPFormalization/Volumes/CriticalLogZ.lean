import WPFormalization.Volumes.CriticalVariance

/-! The actual logarithm of Z separates its critical (5/2) log(delta) singularity.
The remaining unit is jointly usable holomorphically, and its differential
identity is deduced from the genuine action equation by the identity principle. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
def CriticalKernelUnits.logZUnit (k : CriticalKernelUnits) (δ : ℂ) : ℂ :=
  Complex.log (k.A δ)+Complex.log (k.a₁ δ)+(3/2:ℂ)*Complex.log (k.r₁ δ)
lemma CriticalKernelUnits.logZUnit_analytic (k : CriticalKernelUnits) :
    AnalyticAt ℂ k.logZUnit 0 := by
  have hA : k.A 0 ∈ Complex.slitPlane := by rw [k.A_zero];norm_num [Complex.slitPlane]
  have ha : k.a₁ 0 ∈ Complex.slitPlane := by
    rw [k.a_zero]
    exact Or.inl (by simpa only [Complex.ofReal_re] using criticalB_pos)
  have hr : k.r₁ 0 ∈ Complex.slitPlane := by rw [k.r_zero];norm_num [Complex.slitPlane]
  exact (((analyticAt_clog hA).comp k.A_analytic).add
    ((analyticAt_clog ha).comp k.a_analytic)).add
    (analyticAt_const.mul ((analyticAt_clog hr).comp k.r_analytic))

lemma CriticalKernelUnits.logZUnit_physical (k : CriticalKernelUnits) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.logZUnit (δ:ℂ)=((Real.log (WP.Z (y₀-δ))-(5/2:ℝ)*Real.log δ:ℝ):ℂ) := by
  filter_upwards [k.physical] with δ hphys hδ
  obtain ⟨hδlt,hA,ha,hr⟩ := hphys hδ
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hApos := marked_A_pos (y₀-δ) ⟨hY.1,hY.2.le⟩
  have hapos := a_pos _ hY
  have hrpos := r_pos _ hY
  have hdn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hae : k.a₁ (δ:ℂ)=((WP.a (y₀-δ)/δ:ℝ):ℂ) := by
    push_cast
    exact (eq_div_iff hdn).mpr (by simpa only [mul_comm] using ha.symm)
  have hre : k.r₁ (δ:ℂ)=((WP.r (y₀-δ)/δ:ℝ):ℂ) := by
    push_cast
    exact (eq_div_iff hdn).mpr (by simpa only [mul_comm] using hr.symm)
  rw [CriticalKernelUnits.logZUnit,hA,hae,hre,
    ←Complex.ofReal_log hApos.le,←Complex.ofReal_log (div_pos hapos hδ).le,
    ←Complex.ofReal_log (div_pos hrpos hδ).le]
  have he : Real.log (WP.Z (y₀-δ))=
      Real.log (WP.A (y₀-δ))+Real.log (WP.a (y₀-δ))+(3/2:ℝ)*Real.log (WP.r (y₀-δ)) := by
    simp only [WP.Z,Real.rpow_eq_pow]
    rw [Real.log_mul (mul_pos hApos hapos).ne' (Real.rpow_pos_of_pos hrpos _).ne',
      Real.log_mul hApos.ne' hapos.ne',Real.log_rpow hrpos]
  rw [he,Real.log_div hapos.ne' hδ.ne',Real.log_div hrpos.ne' hδ.ne']
  push_cast
  ring
end WP.Analysis

namespace WP.Analysis
lemma complex_germ_identity_of_real_right (f g : ℂ→ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠδ:ℝ in 𝓝 0,0<δ→f (δ:ℂ)=g (δ:ℂ)) : f =ᶠ[𝓝 0] g := by
  apply (hf.frequently_eq_iff_eventually_eq hg).mp
  have ht : Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝[>] 0) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [mem_compl_iff,mem_singleton_iff]
    exact_mod_cast (show 0<δ from hδ).ne'
  have he' : ∀ᶠδ:ℝ in 𝓝[>] 0,f (δ:ℂ)=g (δ:ℂ) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with δ hδ hpos
    exact hδ hpos
  exact ht.frequently he'.frequently

lemma CriticalKernelUnits.derivX_factor (k : CriticalKernelUnits) :
    ∀ᶠδ:ℂ in 𝓝 0,deriv X ((y₀:ℂ)-δ)=δ*k.a₁ δ := by
  apply complex_germ_identity_of_real_right _ _
    (((X_differentiable.analyticAt _).deriv).comp (analyticAt_const.sub analyticAt_id))
    (analyticAt_id.mul k.a_analytic)
  filter_upwards [k.physical] with δ hδ hpos
  change deriv X ((y₀:ℂ)-(δ:ℂ))=(δ:ℂ)*k.a₁ (δ:ℂ)
  rw [←Complex.ofReal_sub,derivX_ofReal]
  exact (hδ hpos).2.2.1

lemma CriticalKernelUnits.logZUnit_deriv (k : CriticalKernelUnits) :
    ∀ᶠδ:ℂ in 𝓝 0,δ*deriv k.logZUnit δ=(k.A δ*k.r₁ δ)⁻¹-(5/2:ℂ) := by
  have hA0 : k.A 0 ≠ 0 := by rw [k.A_zero];norm_num
  have hr0 : k.r₁ 0 ≠ 0 := by rw [k.r_zero];norm_num
  apply complex_germ_identity_of_real_right _ _
    (analyticAt_id.mul k.logZUnit_analytic.deriv)
    (((k.A_analytic.mul k.r_analytic).inv (mul_ne_zero hA0 hr0)).sub analyticAt_const)
  have hcast : Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  filter_upwards [k.physical,k.logZUnit_physical.eventually_nhds,
    hcast.eventually k.logZUnit_analytic.eventually_analyticAt]
    with δ hphys hloc hpan hδ
  obtain ⟨hδlt,hA,ha,hr⟩ := hphys hδ
  have hY : y₀-δ ∈ Ioo (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have heq : (fun ε:ℝ=>k.logZUnit (ε:ℂ)) =ᶠ[𝓝 δ]
      (fun ε:ℝ=>((Real.log (WP.Z (y₀-ε))-(5/2:ℝ)*Real.log ε:ℝ):ℂ)) := by
    filter_upwards [hloc,eventually_gt_nhds hδ] with ε he hε
    exact he hε
  have hs : HasDerivAt (fun ε:ℝ=>y₀-ε) (-1) δ := by
    convert! (hasDerivAt_const δ y₀).sub (hasDerivAt_id δ) using 1 <;> simp
  have hZ := (logNormalizedAction_hasDerivAt_open_parameter (y₀-δ) hY).comp δ hs
  have hd := (hZ.sub ((Real.hasDerivAt_log hδ.ne').const_mul (5/2:ℝ))).ofReal_comp
  have hd' := hpan.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq heq.symm
  have hder : deriv k.logZUnit (δ:ℂ)=
      ((1/(WP.A (y₀-δ)*WP.r (y₀-δ))-(5/2:ℝ)/δ:ℝ):ℂ) := by
    convert! hd'.unique hd using 1 <;> ring
  change (δ:ℂ)*deriv k.logZUnit (δ:ℂ)=(k.A (δ:ℂ)*k.r₁ (δ:ℂ))⁻¹-(5/2:ℂ)
  rw [hder]
  have hdn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hAn : k.A (δ:ℂ) ≠ 0 := by
    rw [hA]
    exact_mod_cast (marked_A_pos (y₀-δ) ⟨hY.1.le,hY.2.le⟩).ne'
  have hrn : k.r₁ (δ:ℂ) ≠ 0 := by
    intro hz
    have hz' : (r (y₀-δ):ℂ)=0 := by rw [hr,hz,mul_zero]
    exact (by exact_mod_cast (r_pos _ ⟨hY.1.le,hY.2⟩).ne' : (r (y₀-δ):ℂ) ≠ 0) hz'
  push_cast
  rw [←hA,hr]
  field_simp
  <;> ring
end WP.Analysis
