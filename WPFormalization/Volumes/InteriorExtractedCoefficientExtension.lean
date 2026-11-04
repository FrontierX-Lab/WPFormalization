import WPFormalization.Volumes.CompactRawCoefficientLocal
import WPFormalization.Analysis.BoundedFamilyPullback
import WPFormalization.HigherOrder.MarkedExtensionProof
/-! Every actual interior Y has one common-radius holomorphic Gevrey-two family for the ORIGINAL extracted coefficients. Actual compact joint Morse data and the true inverse-Poisson convolution supply the family in x; the entire original X transports it to Y. The real trace agrees with the prescribed extractedCoefficient on the closed physical interval, with both exceptional endpoint branches excluded by true X values. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma X_ofReal_XR (Y : ℝ) : X (Y : ℂ) = (XR Y : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using X_im_ofReal Y

set_option maxHeartbeats 1500000 in
lemma interior_extractedCoefficient_local_extension (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y0 : ℝ) (hY0 : Y0 ∈ Ioo (0 : ℝ) y₀) :
    ∃ r C B : ℝ, 0 < r ∧ 0 < C ∧ 0 < B ∧ ∃ F : ℕ → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball (Y0 : ℂ) r)) ∧
      (∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → (Y : ℂ) ∈ Metric.ball (Y0 : ℂ) r →
        F j (Y : ℂ) = (HigherOrder.extractedCoefficient P p j Y : ℂ)) ∧
      ∀ j z, z ∈ Metric.ball (Y0 : ℂ) r → ‖F j z‖ ≤ C * B^j * (j.factorial : ℝ)^2 := by
  let x0 : ℝ := XR Y0
  have hx0 : x0 ∈ Ioo (0 : ℝ) xCritical := by
    constructor
    · simpa only [XR_zero] using XR_strictMonoOn (show (0 : ℝ) ∈ Iic y₀ from y₀_pos.le)
        (show Y0 ∈ Iic y₀ from hY0.2.le) hY0.1
    · exact XR_strictMonoOn (show Y0 ∈ Iic y₀ from hY0.2.le) (show y₀ ∈ Iic y₀ from by simp) hY0.2
  let α : ℝ := x0/2
  let β : ℝ := (x0+xCritical)/2
  have hα : 0 < α := half_pos hx0.1
  have hβc : β < xCritical := by dsimp [β]; linarith [hx0.2]
  have hx0I : x0 ∈ Ioo α β := by dsimp [α,β]; constructor <;> linarith [hx0.1,hx0.2]
  have hαβ : α ≤ β := hx0I.1.le.trans hx0I.2.le
  obtain ⟨C0,B0,hC0,hB0,Ω,aC,f,hΩ,hcover,hf,hrest,hbound⟩ :=
    HigherOrder.markedCoefficient_common_complex_gevrey_two P p hp
  have hfa : ∀ j, AnalyticOnNhd ℂ (f j) Ω := fun j => (hf j).2
  have hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) = (HigherOrder.markedCoefficient P p j Y : ℂ) :=
    fun j Y hY => (hrest j Y hY).2
  have hfb : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C0 * B0^j * (j.factorial : ℝ)^2 := by
    intro j z hz
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound j z hz)
  obtain ⟨S,l,hData⟩ := actual_compact_exponential_phase_data α β hα hαβ hβc
  obtain ⟨Bc,hBc0,hBc⟩ := extractionB_complex_extension P p
  obtain ⟨G,R,C,B,hR,hC,hB,hGa,hGb,hGr⟩ := compact_raw_coefficient_local_x_extension P p hp
    α β hα hαβ hβc S l Bc Ω f C0 B0 hΩ hcover hC0 hB0 hfa hfr hfb
    (fun x hx => by
      have hd := hData x hx
      exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2⟩)
    (fun x hx => (hData x hx).2.2.2.1) hBc x0 ⟨hx0I.1.le,hx0I.2.le⟩
  let q : ℂ → ℂ := fun z => X z - (x0 : ℂ)
  have hq : AnalyticAt ℂ q (Y0 : ℂ) := (X_differentiable.analyticAt _).sub analyticAt_const
  have hq0 : q (Y0 : ℂ) = 0 := by dsimp only [q,x0]; rw [X_ofReal_XR,sub_self]
  have hqsmall : ∀ᶠ z : ℂ in 𝓝 (Y0 : ℂ), ‖q z‖ < R :=
    hq.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by rw [hq0,norm_zero]; exact hR))
  have hXRcont : ContinuousAt XR Y0 := by
    have ht : ContinuousAt (fun Y : ℝ => X (Y : ℂ)) Y0 :=
      ContinuousAt.comp (f := fun Y : ℝ => (Y : ℂ)) (x := Y0)
        (X_differentiable (Y0 : ℂ)).continuousAt Complex.continuous_ofReal.continuousAt
    exact Complex.continuous_re.continuousAt.comp ht
  have hXRnear : ∀ᶠ Y : ℝ in 𝓝 Y0, XR Y ∈ Ioo α β :=
    hXRcont.tendsto.eventually (isOpen_Ioo.mem_nhds hx0I)
  have hqreal : ∀ᶠ Y : ℝ in 𝓝 Y0, ‖q (Y : ℂ)‖ < R :=
    (Complex.continuous_ofReal.tendsto Y0).eventually hqsmall
  have htrace : ∀ᶠ Y : ℝ in 𝓝 Y0, Y ∈ Icc (0 : ℝ) y₀ →
      ∀ j, G j (q (Y : ℂ)) = (HigherOrder.extractedCoefficient P p j Y : ℂ) := by
    filter_upwards [hXRnear,hqreal] with Y hx hqr hY j
    have hqY : q (Y : ℂ) = ((XR Y-x0 : ℝ) : ℂ) := by
      dsimp only [q]
      rw [X_ofReal_XR,Complex.ofReal_sub]
    have hdist : |XR Y-x0| < R := by
      rw [hqY,Complex.norm_real,Real.norm_eq_abs] at hqr
      exact hqr
    have he := hGr (XR Y) ⟨hx.1.le,hx.2.le⟩ hdist j
    have hInv : inverseY (XR Y) = Y := inverseY_eq_of_root (XR Y) Y hY.2 rfl
    rw [hInv] at he
    have hYzero : Y ≠ 0 := by
      intro hz
      have hxp : 0 < XR Y := hα.trans hx.1
      rw [hz,XR_zero] at hxp
      linarith
    have hYcrit : Y ≠ y₀ := by
      intro hz
      have hxc : XR Y < xCritical := hx.2.trans hβc
      rw [hz] at hxc
      exact (lt_irrefl (XR y₀)) hxc
    rw [hqY]
    simpa only [HigherOrder.extractedCoefficient,ite_eq_right hYzero,ite_eq_right hYcrit] using he
  obtain ⟨r,hr,hFa,hFr,hFb⟩ := bounded_complex_family_local_pullback 0 y₀ Y0
    (fun j Y => (HigherOrder.extractedCoefficient P p j Y : ℂ)) G q R C B hR hGa hGb hq hq0 htrace
  exact ⟨r,C,B,hr,hC,hB,(fun j z => G j (q z)),hFa,hFr,hFb⟩
end WP.Analysis
