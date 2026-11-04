import WPFormalization.Analysis.PoissonNormalizer
import WPFormalization.Analysis.DeltaExtensionLimit
import WPFormalization.Analysis.ScaledSeriesConvolution
import WPFormalization.Volumes.CriticalGaussianModel
import WPFormalization.Volumes.CriticalInversePsi
import WPFormalization.Volumes.CriticalRawCoefficientMatching
/-! The prescribed CG3 extraction coefficients have a common critical holomorphic extension and uniform Gevrey-two bounds. The value at the endpoint is proved equal to the original limUnder definition, using the actual physical trace. Inverse Poisson coefficient growth uses the previously registered Stirling input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma criticalExtractedCoefficient_eq_of_delta_extension (P:PsiTheory) (p j:ℕ)
    (F:ℂ→ℂ) (R:ℝ) (hR:0<R) (hF:ContinuousAt F 0)
    (htrace:∀δ∈Ioo (0:ℝ) R,F (δ:ℂ)=(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)) :
    F 0=(HigherOrder.criticalExtractedCoefficient P p j:ℂ) := by
  exact delta_extension_limit_real_trace (HigherOrder.rawExtractedCoefficient P p j) y₀ F R hR hF htrace

lemma CriticalGaussianCoordinateData.original_raw_critical_gevrey_two
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1≤p) :
    ∃(F:ℕ→ℂ→ℂ)(R C B:ℝ),0<R ∧ R<y₀ ∧ 0<C ∧ 0<B ∧
      (∀j,AnalyticOnNhd ℂ (F j) (Metric.closedBall 0 R)) ∧
      (∀j z,‖z‖≤R→‖F j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      (∀δ∈Ioo (0:ℝ) R,∀j,F j (δ:ℂ)=(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)) ∧
      (∀j,F j 0=(HigherOrder.criticalExtractedCoefficient P p j:ℂ)) ∧
      ∀z:ℂ,‖z‖≤R→F 0 z=1 := by
  obtain ⟨Q,Ω,f,ρ,Cg,Ba,hQ,hQ0,hQphys,hΩ,hcover,hf,hrest,hρ,hCg,hBa,hDiff,hBd,hGa,hGb,hG0⟩:=
    d.actual_gaussian_model_coefficient_family P p hp
  let G:ℕ→ℂ→ℂ:=fun j δ=>gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s (δ,u)) j
  let Bg:ℝ:=2*max Ba (2/ρ^2)
  have hBg:0<Bg:=mul_pos (by norm_num) (hBa.trans_le (le_max_left _ _))
  obtain ⟨Rm,hRm,hRmy,hRaw⟩:=d.original_raw_coefficients_eq_critical_model P p hp Q f Ω hΩ
    (hcover _ ⟨y₀_pos.le,le_rfl⟩) hQ hQ0 hQphys hf hrest
  obtain ⟨Rt,hRt,hRty,hTa,hTr⟩:=d.kernel.inversePsiUnit_common_bound
  obtain ⟨Cp,Bp,hCp,hBp,hcb⟩:=GevreyOneAsymptotic.coeff_bound
    (fun x=>(poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one
  let R:ℝ:=min ρ (min Rt Rm)/2
  have hR:0<R:=half_pos (lt_min hρ (lt_min hRt hRm))
  have hRρ:R<ρ:=(half_lt_self (lt_min hρ (lt_min hRt hRm))).trans_le (min_le_left _ _)
  have hRRt:R<Rt:=(half_lt_self (lt_min hρ (lt_min hRt hRm))).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRRm:R<Rm:=(half_lt_self (lt_min hρ (lt_min hRt hRm))).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hRy:R<y₀:=hRRm.trans hRmy
  let c:ℕ→ℝ:=fun j=>PowerSeries.coeff j (HigherOrder.poissonStirlingSeries⁻¹)
  let F:ℕ→ℂ→ℂ:=scaledSeriesConvolution G c d.kernel.inversePsiUnit
  let B:ℝ:=2*max Bg (Bp*1)
  have hB:0<B:=mul_pos (by norm_num) (hBg.trans_le (le_max_left _ _))
  have hGaR:∀j,AnalyticOnNhd ℂ (G j) (Metric.closedBall 0 R) := by
    intro j z hz
    have hn:‖z‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    exact hGa j z (by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_lt hRρ)
  have hTaR:AnalyticOnNhd ℂ d.kernel.inversePsiUnit (Metric.closedBall 0 R) := by
    intro z hz
    exact (hTa z ((show ‖z‖≤R from by simpa only[Metric.mem_closedBall,dist_zero_right] using hz).trans hRRt.le)).1
  have hFa:∀j,AnalyticOnNhd ℂ (F j) (Metric.closedBall 0 R):=
    fun j=>scaledSeriesConvolution_analyticOnNhd G c d.kernel.inversePsiUnit _ hGaR hTaR j
  have hFb(j:ℕ)(z:ℂ)(hz:‖z‖≤R):‖F j z‖≤(Cg*Cp)*B^j*(j.factorial:ℝ)^2 := by
    exact scaledSeriesConvolution_gevreyTwo_bound G c d.kernel.inversePsiUnit Cg Bg Cp Bp 1 hCg.le hBg.le
      hCp.le hBp.le zero_le_one z (fun i=>hGb i z (hz.trans_lt hRρ)) hcb (hTa z (hz.trans hRRt.le)).2 j
  have htrace(δ:ℝ)(hδ:δ∈Ioo (0:ℝ) R)(j:ℕ):F j (δ:ℂ)=(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ) := by
    have hδm:δ∈Ioo (0:ℝ) Rm:=⟨hδ.1,hδ.2.trans hRRm⟩
    have hδt:δ∈Ioo (0:ℝ) Rt:=⟨hδ.1,hδ.2.trans hRRt⟩
    have he:=(hRaw δ hδm j).2
    dsimp only[F,scaledSeriesConvolution,c]
    rw[hTr δ hδt]
    rw[he]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only[G]
    push_cast
    rw[div_pow,one_pow]
    ring
  have hend(j:ℕ):F j 0=(HigherOrder.criticalExtractedCoefficient P p j:ℂ) := by
    exact criticalExtractedCoefficient_eq_of_delta_extension P p j (F j) R hR
      (hFa j 0 (Metric.mem_closedBall_self hR.le)).continuousAt (fun δ hδ=>htrace δ hδ j)
  refine ⟨F,R,Cg*Cp,B,hR,hRy,mul_pos hCg hCp,hB,hFa,hFb,htrace,hend,?_⟩
  intro z hz
  have hg:G 0 z=1:=hG0 z (hz.trans_lt hRρ)
  dsimp only[F,scaledSeriesConvolution]
  simp only[Nat.zero_add,Finset.range_one,Finset.sum_singleton,Nat.sub_zero,pow_zero,mul_one,c]
  rw[hg]
  simp[PowerSeries.coeff_zero_eq_constantCoeff]
end WP.Analysis
