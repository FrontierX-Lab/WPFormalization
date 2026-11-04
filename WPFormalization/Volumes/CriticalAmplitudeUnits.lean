import WPFormalization.Volumes.CriticalPhaseCalculus
import WPFormalization.Analysis.ExtractionFactorization
/-! The actual extraction amplitude separates a delta^(p/2) factor and
a nonvanishing holomorphic unit. The prescribed A, Theta and first-root r
are retained, and their physical values identify the analytic joint ratio. -/
noncomputable section
open Set Filter
open scoped Topology ComplexOrder
namespace WP.Analysis
lemma exists_criticalThetaUnit :
    ∃ Q:ℂ→ℂ,AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      ∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ) := by
  obtain ⟨Ω,hΩ,hΩconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ := common_holomorphic_kernel_moments
  have hcrit : (y₀:ℂ)∈Ω := hcover _ ⟨y₀_pos.le,le_rfl⟩
  let Qδ:ℂ→ℂ := fun δ=>Q ((y₀:ℂ)-δ)
  have hQa : AnalyticAt ℂ Qδ 0 := by
    have hQ0 : AnalyticAt ℂ Q ((y₀:ℂ)-(0:ℂ)) := by simpa using hQ _ hcrit
    exact hQ0.comp (analyticAt_const.sub analyticAt_id)
  refine ⟨Qδ,hQa,?_,?_⟩
  · dsimp only [Qδ]
    rw [sub_zero,(hmatch y₀ ⟨y₀_pos.le,le_rfl⟩).1,total_weight_critical_value]
    rfl
  filter_upwards [eventually_lt_nhds y₀_pos] with δ hδlt hδ
  have hY : y₀-δ∈Icc (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  dsimp only [Qδ]
  rw [←Complex.ofReal_sub,(hmatch _ hY).1]
  rfl

def CriticalKernelUnits.amplitudeUnit (k : CriticalKernelUnits) (Q:ℂ→ℂ) (p:ℕ) (δ:ℂ) : ℂ :=
  Complex.exp (((p:ℂ)/2)*Complex.log (k.r₁ δ))*Complex.sqrt (k.A δ*Q δ)

lemma CriticalKernelUnits.amplitudeUnit_analytic (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1) (p:ℕ) :
    AnalyticAt ℂ (k.amplitudeUnit Q p) 0 := by
  have hr : k.r₁ 0∈Complex.slitPlane := by rw [k.r_zero];norm_num [Complex.slitPlane]
  have hprod : AnalyticAt ℂ (fun δ:ℂ=>k.A δ*Q δ) 0 := k.A_analytic.mul hQ
  have hpos : (k.A 0*Q 0).re>0 := by rw [k.A_zero,hQ0];norm_num
  have hsq := AnalyticAt.comp (f:=fun δ:ℂ=>k.A δ*Q δ) (x:=0) (complex_sqrt_analyticAt (Or.inl hpos)) hprod
  exact ((analyticAt_const.mul ((analyticAt_clog hr).comp k.r_analytic)).cexp).mul hsq

lemma CriticalKernelUnits.amplitudeUnit_zero (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ0:Q 0=1) (p:ℕ) :
    k.amplitudeUnit Q p 0=
      ((Real.rpow 3 ((p:ℝ)/2)*Real.sqrt (2/15:ℝ):ℝ):ℂ) := by
  rw [CriticalKernelUnits.amplitudeUnit,k.r_zero,k.A_zero,hQ0,mul_one]
  have hs : Complex.sqrt (2/15:ℂ)=((Real.sqrt (2/15:ℝ):ℝ):ℂ) := by
    have hr : (2/15:ℂ).re=(2/15:ℝ) := by norm_num [Complex.div_re]
    have ht : 0≤((2/15:ℝ):ℂ) := Complex.zero_le_real.mpr (by norm_num)
    have hc : ((2/15:ℝ):ℂ)=(2/15:ℂ) := by push_cast;rfl
    rw [hc] at ht
    rw [Complex.sqrt_of_nonneg ht,hr]
  have hl : Complex.log (3:ℂ)=((Real.log (3:ℝ):ℝ):ℂ) := by
    simpa using (Complex.ofReal_log (x:=3) (by norm_num)).symm
  rw [hs,hl]
  rw [Real.rpow_eq_pow,Real.rpow_def_of_pos (show (0:ℝ)<3 by norm_num)]
  push_cast
  congr 1
  congr 1
  ring

lemma CriticalKernelUnits.amplitudeUnit_ne_zero (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ0:Q 0=1) (p:ℕ) : k.amplitudeUnit Q p 0≠0 := by
  rw [k.amplitudeUnit_zero Q hQ0 p]
  exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _)
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/15))).ne'

lemma CriticalKernelUnits.amplitudeUnit_physical (k : CriticalKernelUnits)
    (Q:ℂ→ℂ)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) (p:ℕ) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      ((Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)):ℝ):ℂ)=
        ((Real.rpow δ ((p:ℝ)/2):ℝ):ℂ)*k.amplitudeUnit Q p (δ:ℂ) := by
  filter_upwards [k.physical,hQphys] with δ hphys hQδ hδ
  obtain ⟨hδlt,hA,ha,hr⟩ := hphys hδ
  have hY : y₀-δ∈Ico (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
  have hrpos := r_pos _ hY
  have hApos := marked_A_pos _ ⟨hY.1,hY.2.le⟩
  have hΘpos := marked_Theta_pos _ ⟨hY.1,hY.2.le⟩
  have hdn : (δ:ℂ)≠0 := by exact_mod_cast hδ.ne'
  have hre : k.r₁ (δ:ℂ)=((r (y₀-δ)/δ:ℝ):ℂ) := by
    push_cast
    exact (eq_div_iff hdn).mpr (by simpa only [mul_comm] using hr.symm)
  rw [CriticalKernelUnits.amplitudeUnit,hA,hQδ hδ,hre,←Complex.ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast (mul_pos hApos hΘpos).le)]
  simp only [Complex.ofReal_re]
  rw [←Complex.ofReal_log (div_pos hrpos hδ).le]
  have hpow : Complex.exp (((p:ℂ)/2)*((Real.log (r (y₀-δ)/δ):ℝ):ℂ))=
      ((Real.rpow (r (y₀-δ)/δ) ((p:ℝ)/2):ℝ):ℂ) := by
    rw [Real.rpow_eq_pow,Real.rpow_def_of_pos (div_pos hrpos hδ)]
    push_cast
    congr 1
    ring
  rw [hpow]
  have he : Real.rpow (r (y₀-δ)) ((p:ℝ)/2)=
      Real.rpow δ ((p:ℝ)/2)*Real.rpow (r (y₀-δ)/δ) ((p:ℝ)/2) := by
    rw [Real.rpow_eq_pow,Real.rpow_eq_pow,Real.rpow_eq_pow,←Real.mul_rpow hδ.le (div_pos hrpos hδ).le]
    congr 1
    field_simp
  rw [he]
  push_cast
  ring
end WP.Analysis

namespace WP.Analysis
def CriticalKernelUnits.jointAmplitude (k : CriticalKernelUnits) (Q:ℂ→ℂ)
    (p:ℕ) (q:ℂ × ℂ→ℂ) (z:ℂ × ℂ) : ℂ :=
  Complex.exp (((p:ℂ)/2)*Complex.log (q z))*k.amplitudeUnit Q p (z.1*q z)/k.amplitudeUnit Q p z.1

lemma CriticalKernelUnits.jointAmplitude_analytic (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1) (p:ℕ)
    (q:ℂ × ℂ→ℂ) (hq:AnalyticAt ℂ q (0,0)) (hq0:q (0,0)=1) :
    AnalyticAt ℂ (k.jointAmplitude Q p q) (0,0) := by
  have hb := k.amplitudeUnit_analytic Q hQ hQ0 p
  have ht : AnalyticAt ℂ (fun z:ℂ × ℂ=>z.1*q z) (0,0) := analyticAt_fst.mul hq
  have hb0 : AnalyticAt ℂ (k.amplitudeUnit Q p) (((0,0):ℂ × ℂ).1*q (0,0)) := by simpa using hb
  have hbt : AnalyticAt ℂ (fun z:ℂ × ℂ=>k.amplitudeUnit Q p (z.1*q z)) (0,0) :=
    AnalyticAt.comp (f:=fun z:ℂ × ℂ=>z.1*q z) (x:=(0,0)) hb0 ht
  have hbf : AnalyticAt ℂ (fun z:ℂ × ℂ=>k.amplitudeUnit Q p z.1) (0,0) :=
    AnalyticAt.comp (f:=Prod.fst) (x:=((0,0):ℂ × ℂ)) hb analyticAt_fst
  have hplane : q (0,0)∈Complex.slitPlane := by rw [hq0];simp
  exact (((analyticAt_const.mul ((analyticAt_clog hplane).comp hq)).cexp).mul hbt).div hbf
    (k.amplitudeUnit_ne_zero Q hQ0 p)

lemma CriticalKernelUnits.jointAmplitude_zero (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ0:Q 0=1) (p:ℕ) (q:ℂ × ℂ→ℂ) (hq0:q (0,0)=1) :
    k.jointAmplitude Q p q (0,0)=1 := by
  simp only [CriticalKernelUnits.jointAmplitude,hq0,Complex.log_one,mul_zero,Complex.exp_zero,
    zero_mul,one_mul]
  exact div_self (k.amplitudeUnit_ne_zero Q hQ0 p)

lemma CriticalKernelUnits.jointAmplitude_axis (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1) (p:ℕ)
    (q:ℂ × ℂ→ℂ) (hqaxis:∀ᶠδ:ℂ in 𝓝 0,q (δ,0)=1) :
    ∀ᶠδ:ℂ in 𝓝 0,k.jointAmplitude Q p q (δ,0)=1 := by
  have hn := (k.amplitudeUnit_analytic Q hQ hQ0 p).continuousAt.eventually_ne
    (k.amplitudeUnit_ne_zero Q hQ0 p)
  filter_upwards [hqaxis,hn] with δ hqδ hnδ
  simp only [CriticalKernelUnits.jointAmplitude,hqδ,Complex.log_one,mul_zero,Complex.exp_zero,
    mul_one,one_mul]
  exact div_self hnδ
end WP.Analysis
