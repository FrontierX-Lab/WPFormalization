import WPFormalization.Volumes.CriticalPhaseCalculus
import WPFormalization.Analysis.ExtractionFactorization
/-! The critical logarithmic phase is the analytic continuation of the actual
real extraction phase: the two-weight physical identity retains the original
normalization Z(0) and cancels it exactly in the difference. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma extractionS_parameter_logZ (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀) :
    extractionS (XR Y)=Real.log (Z 0)-Real.log (Z Y) := by
  rw [extractionS,inverseY_eq_of_root _ _ hY.2.le rfl,
    Real.log_div (marked_Z_pos 0 ⟨le_rfl,y₀_pos⟩).ne' (marked_Z_pos Y hY).ne']

lemma CriticalKernelUnits.extractionS_difference_physical (k : CriticalKernelUnits) :
    ∀ᶠp:ℝ × ℝ in 𝓝 (0,0),0<p.1→0<p.2→
      ((extractionS (XR (y₀-p.2))-extractionS (XR (y₀-p.1)):ℝ):ℂ)=
        -(5/2:ℂ)*Complex.log ((p.2:ℂ)/(p.1:ℂ))-
          k.logZUnit (p.2:ℂ)+k.logZUnit (p.1:ℂ) := by
  have hf : Tendsto (Prod.fst:ℝ × ℝ→ℝ) (𝓝 (0,0)) (𝓝 (0:ℝ)) := continuous_fst.continuousAt.tendsto
  have hs : Tendsto (Prod.snd:ℝ × ℝ→ℝ) (𝓝 (0,0)) (𝓝 (0:ℝ)) := continuous_snd.continuousAt.tendsto
  filter_upwards [hf.eventually k.physical,hs.eventually k.physical,
    hf.eventually k.logZUnit_physical,hs.eventually k.logZUnit_physical]
    with p hp1 hp2 hJ1 hJ2 h1 h2
  have hY1 : y₀-p.1∈Ico (0:ℝ) y₀ := ⟨by linarith [(hp1 h1).1],by linarith⟩
  have hY2 : y₀-p.2∈Ico (0:ℝ) y₀ := ⟨by linarith [(hp2 h2).1],by linarith⟩
  rw [extractionS_parameter_logZ _ hY1,extractionS_parameter_logZ _ hY2,
    hJ1 h1,hJ2 h2,←Complex.ofReal_div,←Complex.ofReal_log (div_pos h2 h1).le,
    Real.log_div h2.ne' h1.ne']
  push_cast
  ring
end WP.Analysis
