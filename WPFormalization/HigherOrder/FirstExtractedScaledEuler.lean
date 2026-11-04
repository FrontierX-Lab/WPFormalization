import WPFormalization.Volumes.CriticalVariance
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

def CriticalKernelUnits.scaledEulerUnit (k : CriticalKernelUnits) (m : ℕ) (U : ℂ→ℂ) (δ:ℂ) : ℂ :=
  X ((y₀:ℂ)-δ) / k.a₁ δ * ((m:ℂ)*U δ - δ*deriv U δ)

lemma CriticalKernelUnits.scaledEulerUnit_analytic (k : CriticalKernelUnits) (m : ℕ)
    (U:ℂ→ℂ) (hU:AnalyticAt ℂ U 0) : AnalyticAt ℂ (k.scaledEulerUnit m U) 0 := by
  apply AnalyticAt.mul
  · apply AnalyticAt.div
    · exact (X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)
    · exact k.a_analytic
    · rw [k.a_zero];exact_mod_cast criticalB_pos.ne'
  · exact (analyticAt_const.mul hU).sub (analyticAt_id.mul hU.deriv)

lemma CriticalKernelUnits.scaledEulerUnit_zero (k : CriticalKernelUnits) (m : ℕ) (U : ℂ→ℂ) :
    k.scaledEulerUnit m U 0 = (y₀:ℂ)*(m:ℂ)*U 0 := by
  rw [CriticalKernelUnits.scaledEulerUnit,sub_zero,X_critical_value,k.a_zero]
  simp only [zero_mul,sub_zero]
  rw [criticalB_eq]
  push_cast
  have hx : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  have hy : (y₀:ℂ) ≠ 0 := by exact_mod_cast y₀_pos.ne'
  field_simp

lemma CriticalKernelUnits.scaledEulerUnit_physical (k : CriticalKernelUnits)
    (f : ℝ→ℝ) (U : ℂ→ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hU : AnalyticAt ℂ U 0)
    (hf : ∀x∈Ioo (0:ℝ) xCritical,DifferentiableAt ℝ f x)
    (htrace : ∀ᶠδ:ℝ in 𝓝 0,0<δ→U (δ:ℂ)=((f (XR (y₀-δ))*δ^m:ℝ):ℂ)) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.scaledEulerUnit m U (δ:ℂ)=((euler f (XR (y₀-δ))*δ^(m+2):ℝ):ℂ) := by
  have hcast : Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  filter_upwards [k.physical,htrace.eventually_nhds,hcast.eventually hU.eventually_analyticAt]
    with δ hphys hloc hUa hδ
  obtain ⟨hδlt,_,ha,_⟩ := hphys hδ
  let Y : ℝ := y₀-δ
  let x : ℝ := XR Y
  have hY : Y ∈ Ioo (0:ℝ) y₀ := ⟨by dsimp[Y];linarith,by dsimp[Y];linarith⟩
  have hx : x ∈ Ioo (0:ℝ) xCritical := by
    constructor
    · simpa only [x,XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
    · exact XR_strictMonoOn hY.2.le (le_refl y₀) hY.2
  have heq : (fun ε:ℝ=>U (ε:ℂ)) =ᶠ[𝓝 δ]
      (fun ε:ℝ=>((f (XR (y₀-ε))*ε^m:ℝ):ℂ)) := by
    filter_upwards [hloc,eventually_gt_nhds hδ] with ε he hε
    exact he hε
  have hX : HasDerivAt (fun ε:ℝ=>XR (y₀-ε)) (-a Y) δ := by
    have hs : HasDerivAt (fun ε:ℝ=>y₀-ε) (-1) δ := by
      convert! (hasDerivAt_const δ y₀).sub (hasDerivAt_id δ) using 1 <;> simp
    convert! (XR_hasDerivAt Y).comp δ hs using 1 <;> simp only [mul_neg_one]
  have hF : HasDerivAt (fun ε:ℝ=>f (XR (y₀-ε))) (-(a Y*deriv f x)) δ := by
    convert! (hf x hx).hasDerivAt.comp δ hX using 1 <;> ring
  have hd := (hF.mul ((hasDerivAt_id δ).pow m)).ofReal_comp
  have hd' := hUa.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq heq.symm
  have hder : deriv U (δ:ℂ)=
      (((-(a Y*deriv f x))*δ^m+f x*((m:ℝ)*δ^(m-1)):ℝ):ℂ) := by
    have hed := hd'.unique hd
    simpa only [Pi.mul_apply,Pi.pow_apply,id_eq,mul_one,x,Y] using hed
  have hv := heq.self_of_nhds
  change U (δ:ℂ)=((f x*δ^m:ℝ):ℂ) at hv
  have hn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have han : k.a₁ (δ:ℂ) ≠ 0 := by
    intro hz
    have haz : (a Y:ℂ)=0 := by simpa only [hz,mul_zero] using ha
    exact (by exact_mod_cast (a_pos Y ⟨hY.1.le,hY.2⟩).ne' : (a Y:ℂ) ≠ 0) haz
  rw [CriticalKernelUnits.scaledEulerUnit,←Complex.ofReal_sub,X_eq_ofReal_XR,hder,hv]
  simp only [euler]
  change (x:ℂ)/k.a₁ (δ:ℂ) * ((m:ℂ)*((f x*δ^m:ℝ):ℂ) - (δ:ℂ)*
    (((-(a Y*deriv f x))*δ^m+f x*((m:ℝ)*δ^(m-1)):ℝ):ℂ)) = _
  push_cast
  rw [ha]
  have hp : (δ:ℂ)*(δ:ℂ)^(m-1)=(δ:ℂ)^m := by
    rw [←pow_succ',Nat.sub_add_cancel hm]
  simp only [pow_add,pow_two]
  field_simp [han]
  linear_combination -(x:ℂ)*(m:ℂ)*(f x:ℂ)*hp
end WP.Analysis
