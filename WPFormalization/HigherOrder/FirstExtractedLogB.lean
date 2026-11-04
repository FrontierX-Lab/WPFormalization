import WPFormalization.Volumes.CriticalAmplitudeUnits
import WPFormalization.Volumes.CriticalLogZ
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

def CriticalKernelUnits.logExtractionBUnit (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (p : ℕ) (δ : ℂ) : ℂ :=
  ((p:ℂ)/2)*Complex.log (k.r₁ δ) +
    (1/2:ℂ)*(Complex.log (k.A δ)+Complex.log (Q δ)) -
    ((Real.log (Real.rpow (r 0) ((p:ℝ)/2)*Real.sqrt (WP.A 0*Theta 0)):ℝ):ℂ)

lemma CriticalKernelUnits.logExtractionBUnit_analytic (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (hQ : AnalyticAt ℂ Q 0) (hQ0 : Q 0=1) (p : ℕ) :
    AnalyticAt ℂ (k.logExtractionBUnit Q p) 0 := by
  have hr : k.r₁ 0∈Complex.slitPlane := by rw [k.r_zero];norm_num [Complex.slitPlane]
  have hA : k.A 0∈Complex.slitPlane := by rw [k.A_zero];norm_num [Complex.slitPlane]
  have hq : Q 0∈Complex.slitPlane := by rw [hQ0];norm_num [Complex.slitPlane]
  exact ((analyticAt_const.mul ((analyticAt_clog hr).comp k.r_analytic)).add
    (analyticAt_const.mul (((analyticAt_clog hA).comp k.A_analytic).add
      ((analyticAt_clog hq).comp hQ)))).sub analyticAt_const

lemma CriticalKernelUnits.logExtractionBUnit_physical (k : CriticalKernelUnits)
    (Q : ℂ → ℂ)
    (hQphys : ∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(Theta (y₀-δ):ℂ)) (p : ℕ) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.logExtractionBUnit Q p (δ:ℂ)=
        ((Real.log (extractionB p (XR (y₀-δ)))-((p:ℝ)/2)*Real.log δ:ℝ):ℂ) := by
  filter_upwards [k.physical,hQphys] with δ hphys hQδ hδ
  obtain ⟨hδlt,hA,_,hr⟩ := hphys hδ
  have hY : y₀-δ∈Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hApos := marked_A_pos _ ⟨hY.1,hY.2.le⟩
  have hQpos := marked_Theta_pos _ ⟨hY.1,hY.2.le⟩
  have hrpos := r_pos _ hY
  have hdn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hre : k.r₁ (δ:ℂ)=((r (y₀-δ)/δ:ℝ):ℂ) := by
    push_cast
    exact (eq_div_iff hdn).mpr (by simpa only [mul_comm] using hr.symm)
  have hinv : inverseY (XR (y₀-δ))=y₀-δ := inverseY_eq_of_root _ _ hY.2.le rfl
  have hamp : 0<Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)) :=
    marked_amplitude_pos p _ hY
  have hamp0 : 0<Real.rpow (r 0) ((p:ℝ)/2)*Real.sqrt (WP.A 0*Theta 0) :=
    marked_amplitude_pos p 0 ⟨le_rfl,y₀_pos⟩
  rw [CriticalKernelUnits.logExtractionBUnit,hre,hA,hQδ hδ,
    ←Complex.ofReal_log (div_pos hrpos hδ).le,
    ←Complex.ofReal_log hApos.le,←Complex.ofReal_log hQpos.le]
  rw [extractionB,hinv,Real.log_div hamp.ne' hamp0.ne']
  simp only [Real.rpow_eq_pow]
  rw [Real.log_mul (Real.rpow_pos_of_pos hrpos _).ne'
      (Real.sqrt_pos.mpr (mul_pos hApos hQpos)).ne',
    Real.log_rpow hrpos,Real.log_sqrt (mul_pos hApos hQpos).le,
    Real.log_mul hApos.ne' hQpos.ne',Real.log_div hrpos.ne' hδ.ne']
  push_cast
  ring

def CriticalKernelUnits.scaledLogBUnit (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (p : ℕ) (δ : ℂ) : ℂ :=
  -(X ((y₀:ℂ)-δ)/k.a₁ δ)*((p:ℂ)/2+δ*deriv (k.logExtractionBUnit Q p) δ)

lemma CriticalKernelUnits.scaledLogBUnit_analytic (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (hQ : AnalyticAt ℂ Q 0) (hQ0 : Q 0=1) (p : ℕ) :
    AnalyticAt ℂ (k.scaledLogBUnit Q p) 0 := by
  have ha : k.a₁ 0≠0 := by rw [k.a_zero];exact_mod_cast criticalB_pos.ne'
  exact ((((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)).div
    k.a_analytic ha).neg).mul
      (analyticAt_const.add (analyticAt_id.mul (k.logExtractionBUnit_analytic Q hQ hQ0 p).deriv))

lemma CriticalKernelUnits.scaledLogBUnit_zero (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (p : ℕ) :
    k.scaledLogBUnit Q p 0=(-(p:ℂ)*(y₀:ℂ)/2) := by
  rw [CriticalKernelUnits.scaledLogBUnit,sub_zero,X_critical_value,k.a_zero]
  simp only [zero_mul,add_zero]
  rw [criticalB_eq]
  push_cast
  have hx : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  have hy : (y₀:ℂ) ≠ 0 := by exact_mod_cast y₀_pos.ne'
  field_simp

lemma CriticalKernelUnits.scaledLogBUnit_physical (k : CriticalKernelUnits)
    (Q : ℂ → ℂ) (hQ : AnalyticAt ℂ Q 0) (hQ0 : Q 0=1)
    (hQphys : ∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(Theta (y₀-δ):ℂ)) (p : ℕ)
    (hb : ∀x∈Ioo (0:ℝ) xCritical,DifferentiableAt ℝ (fun t=>Real.log (extractionB p t)) x) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.scaledLogBUnit Q p (δ:ℂ)=
        ((euler (fun t=>Real.log (extractionB p t)) (XR (y₀-δ))*δ^2:ℝ):ℂ) := by
  have hcast : Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  have hunit := k.logExtractionBUnit_physical Q hQphys p
  have huAn := k.logExtractionBUnit_analytic Q hQ hQ0 p
  filter_upwards [k.physical,hunit.eventually_nhds,hcast.eventually huAn.eventually_analyticAt]
    with δ hphys hloc huδ hδ
  obtain ⟨hδlt,_,ha,_⟩ := hphys hδ
  let Y : ℝ := y₀-δ
  let x : ℝ := XR Y
  have hY : Y ∈ Ioo (0:ℝ) y₀ := ⟨by dsimp[Y];linarith,by dsimp[Y];linarith⟩
  have hx : x ∈ Ioo (0:ℝ) xCritical := by
    constructor
    · simpa only [x,XR_zero] using XR_strictMonoOn y₀_pos.le hY.2.le hY.1
    · exact XR_strictMonoOn hY.2.le (le_refl y₀) hY.2
  have heq : (fun ε:ℝ=>k.logExtractionBUnit Q p (ε:ℂ)) =ᶠ[𝓝 δ]
      (fun ε:ℝ=>((Real.log (extractionB p (XR (y₀-ε)))-((p:ℝ)/2)*Real.log ε:ℝ):ℂ)) := by
    filter_upwards [hloc,eventually_gt_nhds hδ] with ε he hε
    exact he hε
  have hX : HasDerivAt (fun ε:ℝ=>XR (y₀-ε)) (-a Y) δ := by
    have hs : HasDerivAt (fun ε:ℝ=>y₀-ε) (-1) δ := by
      convert! (hasDerivAt_const δ y₀).sub (hasDerivAt_id δ) using 1 <;> simp
    convert! (XR_hasDerivAt Y).comp δ hs using 1 <;> simp only [mul_neg_one]
  have hB : HasDerivAt (fun ε:ℝ=>Real.log (extractionB p (XR (y₀-ε))))
      (-a Y*deriv (fun t=>Real.log (extractionB p t)) x) δ := by
    convert! (hb x hx).hasDerivAt.comp δ hX using 1 <;> ring
  have hd := (hB.sub ((Real.hasDerivAt_log hδ.ne').const_mul ((p:ℝ)/2))).ofReal_comp
  have hd' := huδ.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq heq.symm
  have hder : deriv (k.logExtractionBUnit Q p) (δ:ℂ)=
      ((-a Y*deriv (fun t=>Real.log (extractionB p t)) x-(p:ℝ)/2*δ⁻¹:ℝ):ℂ) := by
    convert! hd'.unique hd using 1 <;> ring
  have han : k.a₁ (δ:ℂ)≠0 := by
    intro hz
    have haz : (a Y:ℂ)=0 := by simpa only [hz,mul_zero] using ha
    exact (by exact_mod_cast (a_pos Y ⟨hY.1.le,hY.2⟩).ne' : (a Y:ℂ) ≠ 0) haz
  have hn : (δ:ℂ)≠0 := by exact_mod_cast hδ.ne'
  rw [CriticalKernelUnits.scaledLogBUnit,←Complex.ofReal_sub,X_eq_ofReal_XR,hder]
  change -((x:ℂ)/k.a₁ (δ:ℂ)) * ((p:ℂ)/2+(δ:ℂ)*
    ((-a Y*deriv (fun t=>Real.log (extractionB p t)) x-(p:ℝ)/2*δ⁻¹:ℝ):ℂ))=_
  simp only [euler]
  push_cast
  rw [ha]
  field_simp [han,hn]
  <;> ring

end WP.Analysis
