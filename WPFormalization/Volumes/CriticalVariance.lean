import WPFormalization.Volumes.CriticalKernelUnits

/-! The actual critical mean and variance are holomorphic units after multiplying
by the precise powers of delta. Standardized angle and centering factors are
constructed on one complex neighborhood and identified by real germ derivatives. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

def CriticalKernelUnits.psiUnit (k : CriticalKernelUnits) (δ : ℂ) : ℂ :=
  X ((y₀:ℂ)-δ)/(k.A δ*k.a₁ δ*k.r₁ δ)

def CriticalKernelUnits.varianceUnit (k : CriticalKernelUnits) (δ : ℂ) : ℂ :=
  X ((y₀:ℂ)-δ)*(2*k.psiUnit δ-δ*deriv k.psiUnit δ)/k.a₁ δ

lemma CriticalKernelUnits.psiUnit_analytic (k : CriticalKernelUnits) :
    AnalyticAt ℂ k.psiUnit 0 := by
  apply ((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)).div
    ((k.A_analytic.mul k.a_analytic).mul k.r_analytic)
  simp only [Pi.mul_apply]
  rw [k.A_zero,k.a_zero,k.r_zero]
  have hn : (criticalB:ℂ) ≠ 0 := by exact_mod_cast criticalB_pos.ne'
  exact mul_ne_zero (mul_ne_zero (by norm_num) hn) (by norm_num)

lemma CriticalKernelUnits.psiUnit_zero (k : CriticalKernelUnits) :
    k.psiUnit 0=(((5/2:ℝ)*y₀:ℝ):ℂ) := by
  rw [CriticalKernelUnits.psiUnit,sub_zero,X_critical_value,k.A_zero,k.a_zero,k.r_zero]
  have hy : (y₀:ℂ) ≠ 0 := by exact_mod_cast y₀_pos.ne'
  have hx : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  rw [criticalB_eq,Complex.ofReal_div]
  push_cast
  field_simp
  <;> ring

lemma CriticalKernelUnits.varianceUnit_analytic (k : CriticalKernelUnits) :
    AnalyticAt ℂ k.varianceUnit 0 := by
  apply (((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)).mul
    ((analyticAt_const.mul k.psiUnit_analytic).sub (analyticAt_id.mul k.psiUnit_analytic.deriv))).div k.a_analytic
  rw [k.a_zero]
  exact_mod_cast criticalB_pos.ne'

lemma CriticalKernelUnits.varianceUnit_zero (k : CriticalKernelUnits) :
    k.varianceUnit 0=((5*y₀^2:ℝ):ℂ) := by
  rw [CriticalKernelUnits.varianceUnit,sub_zero,X_critical_value,k.psiUnit_zero,k.a_zero]
  simp only [zero_mul,sub_zero]
  rw [criticalB_eq,Complex.ofReal_div]
  push_cast
  have hy : (y₀:ℂ) ≠ 0 := by exact_mod_cast y₀_pos.ne'
  have hx : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  field_simp
  <;> ring

lemma CriticalKernelUnits.psiUnit_physical (k : CriticalKernelUnits) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→k.psiUnit (δ:ℂ)=((Psi (XR (y₀-δ))*δ^2:ℝ):ℂ) := by
  filter_upwards [k.physical] with δ hδ hpos
  obtain ⟨hδlt,hA,ha,hr⟩ := hδ hpos
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  rw [CriticalKernelUnits.psiUnit,←Complex.ofReal_sub,X_eq_ofReal_XR,Psi_XR_eq_kernel_ratio _ hY]
  push_cast
  rw [ha,hr,←hA]
  have hn : (δ:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp
  <;> ring

lemma CriticalKernelUnits.varianceUnit_physical (k : CriticalKernelUnits) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.varianceUnit (δ:ℂ)=((euler Psi (XR (y₀-δ))*δ^4:ℝ):ℂ) := by
  have hcast : Tendsto (fun δ : ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  have hlocal := k.psiUnit_physical.eventually_nhds
  filter_upwards [k.physical,hlocal,hcast.eventually k.psiUnit_analytic.eventually_analyticAt]
    with δ hphys hloc hpan hδ
  obtain ⟨hδlt,hA,ha,hr⟩ := hphys hδ
  let Y : ℝ := y₀-δ
  let x : ℝ := XR Y
  have hY : Y ∈ Ico (0:ℝ) y₀ := ⟨by dsimp [Y];linarith,by dsimp [Y];linarith⟩
  have hx : x ∈ Ico (0:ℝ) xCritical := by
    refine ⟨XR_nonneg_interior Y hY,?_⟩
    exact XR_strictMonoOn hY.2.le (by simp) hY.2
  have heq : (fun ε : ℝ=>k.psiUnit (ε:ℂ)) =ᶠ[𝓝 δ]
      (fun ε : ℝ=>((Psi (XR (y₀-ε))*ε^2:ℝ):ℂ)) := by
    filter_upwards [hloc,eventually_gt_nhds hδ] with ε he hε
    exact he hε
  have hX : HasDerivAt (fun ε : ℝ=>XR (y₀-ε)) (-a Y) δ := by
    have hs : HasDerivAt (fun ε : ℝ=>y₀-ε) (-1) δ := by
      convert! (hasDerivAt_const δ y₀).sub (hasDerivAt_id δ) using 1 <;> simp
    convert! (XR_hasDerivAt Y).comp δ hs using 1 <;> simp only [mul_neg_one]
  have hΨ : HasDerivAt (fun ε : ℝ=>Psi (XR (y₀-ε))) (-(a Y*deriv Psi x)) δ := by
    convert! (Psi_analyticAt_interior x hx).differentiableAt.hasDerivAt.comp δ hX using 1 <;> ring
  have hd := (hΨ.mul ((hasDerivAt_id δ).pow 2)).ofReal_comp
  have hd' := (hpan.differentiableAt.hasDerivAt.comp_ofReal).congr_of_eventuallyEq heq.symm
  have hder : deriv k.psiUnit (δ:ℂ)=
      (((-(a Y*deriv Psi x))*δ^2+Psi x*(2*δ):ℝ):ℂ) := by
    have hed := hd'.unique hd
    simpa only [Pi.mul_apply,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one,x,Y] using hed
  have hv := heq.self_of_nhds
  change k.psiUnit (δ:ℂ)=_ at hv
  rw [CriticalKernelUnits.varianceUnit,←Complex.ofReal_sub,X_eq_ofReal_XR,hder,hv]
  change (x:ℂ)*(2*((Psi x*δ^2:ℝ):ℂ)-(δ:ℂ)*
    (((-(a Y*deriv Psi x))*δ^2+Psi x*(2*δ):ℝ):ℂ))/k.a₁ (δ:ℂ)=_
  have hn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have han : k.a₁ (δ:ℂ) ≠ 0 := by
    intro hz
    have haz : (a Y:ℂ)=0 := by simpa only [hz,mul_zero] using ha
    exact (by exact_mod_cast (a_pos Y hY).ne' : (a Y:ℂ) ≠ 0) haz
  simp only [WP.euler]
  push_cast
  rw [ha]
  field_simp
  <;> ring
end WP.Analysis

namespace WP.Analysis
lemma CriticalKernelUnits.normalization (k : CriticalKernelUnits) :
    ∃ L : ℂ→ℂ,AnalyticAt ℂ L 0 ∧
      L 0=(((Real.sqrt (5*y₀^2))⁻¹:ℝ):ℂ) ∧
      ∀ᶠδ:ℝ in 𝓝 0,0<δ→
        (δ:ℂ)^2*L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ) ∧
        k.psiUnit (δ:ℂ)*L (δ:ℂ)=((Psi (XR (y₀-δ))/Real.sqrt (euler Psi (XR (y₀-δ))):ℝ):ℂ) := by
  let L : ℂ→ℂ := fun δ=>(Complex.sqrt (k.varianceUnit δ))⁻¹
  have hv0 : 0 < 5*y₀^2 := mul_pos (by norm_num) (sq_pos_of_pos y₀_pos)
  have hs : AnalyticAt ℂ (fun δ=>Complex.sqrt (k.varianceUnit δ)) 0 :=
    (complex_sqrt_analyticAt (by rw [k.varianceUnit_zero];exact Or.inl hv0)).comp k.varianceUnit_analytic
  have hsc : Complex.sqrt (k.varianceUnit 0)=((Real.sqrt (5*y₀^2):ℝ):ℂ) := by
    rw [k.varianceUnit_zero]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hv0.le)
  have hsn : Complex.sqrt (k.varianceUnit 0) ≠ 0 := by
    rw [hsc]
    exact_mod_cast (Real.sqrt_pos.mpr hv0).ne'
  refine ⟨L,hs.inv hsn,?_,?_⟩
  · dsimp only [L]
    rw [hsc,Complex.ofReal_inv]
  filter_upwards [k.physical,k.psiUnit_physical,k.varianceUnit_physical]
    with δ hphys hpsi hvar hδ
  obtain ⟨hδlt,_,_,_⟩ := hphys hδ
  have hY : y₀-δ ∈ Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hxp : 0 < XR (y₀-δ) := by
    have hh := XR_strictMonoOn (show (0:ℝ)≤y₀ from y₀_pos.le) hY.2.le (by linarith : 0<y₀-δ)
    simpa only [XR_zero] using hh
  have hx : XR (y₀-δ) ∈ Ico (0:ℝ) xCritical :=
    ⟨hxp.le,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hvp : 0 < euler Psi (XR (y₀-δ)) := mul_pos hxp (Psi_deriv_pos_interior _ hx)
  have hsq : Complex.sqrt (k.varianceUnit (δ:ℂ))=
      ((Real.sqrt (euler Psi (XR (y₀-δ)))*δ^2:ℝ):ℂ) := by
    rw [hvar hδ]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg hvp.le (pow_nonneg hδ.le 4)))]
    simp only [Complex.ofReal_re]
    congr 1
    rw [Real.sqrt_mul hvp.le,show δ^4=(δ^2)^2 by ring,Real.sqrt_sq (sq_nonneg δ)]
  have hdn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hvn : ((Real.sqrt (euler Psi (XR (y₀-δ)))):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hvp).ne'
  constructor
  · dsimp only [L]
    rw [hsq]
    push_cast
    field_simp
  · rw [hpsi hδ]
    dsimp only [L]
    rw [hsq]
    push_cast
    field_simp
end WP.Analysis
