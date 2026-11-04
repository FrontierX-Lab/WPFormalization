import WPFormalization.Analysis.RatioSaddleCurvature
import WPFormalization.Marked.DilatonRefinement
import WPFormalization.Analysis.LogScaleVariation

/-! Uniform regularity of the actual finite-model saddle. The weighted derivative of b is bounded using the already proved common holomorphic kernel family; the actual transport coefficient is bounded from the proved kernel moments. No saddle-displacement estimate is an input. -/

noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma ratioSaddle_complex_bound {Ω : Set ℂ} (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Ω) :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Icc (0:ℝ) y₀,‖F (Y:ℂ)‖≤C := by
  have hc : ContinuousOn (fun Y:ℝ=>F (Y:ℂ)) (Icc (0:ℝ) y₀) := by
    intro Y hY
    exact ((hF _ (hcover Y hY)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro Y hY
  exact (hC ⟨Y,hY,rfl⟩).trans (le_max_left _ _)

lemma ratioSaddleDefect_differentiableAt (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    DifferentiableAt ℝ ratioSaddleDefect Y := by
  obtain ⟨Ω,hΩ,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_moments
  let B : ℂ → ℂ := fun z=>1-Ahat z*(1+Q z/2)
  have hB : AnalyticOnNhd ℂ B Ω := fun z hz=>
    analyticAt_const.sub ((hA z hz).mul (analyticAt_const.add ((hQ z hz).div_const)))
  have heq : (fun t:ℝ=>(B (t:ℂ)).re)=ᶠ[𝓝 Y] ratioSaddleDefect := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
    dsimp only [B,ratioSaddleDefect]
    rw [(hmatch t ⟨ht.1.le,ht.2.le⟩).1,(hmatch t ⟨ht.1.le,ht.2.le⟩).2]
    simp [Theta]
  exact (((hB _ (hcover Y ⟨hY.1.le,hY.2.le⟩)).differentiableAt.hasDerivAt.real_of_complex).congr_of_eventuallyEq heq.symm).differentiableAt

lemma ratioSaddleDefect_weighted_derivative_bound :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Ioo (0:ℝ) y₀,|A Y*r Y*deriv ratioSaddleDefect Y|≤C := by
  obtain ⟨Ω,hΩ,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_moments
  let B : ℂ → ℂ := fun z=>1-Ahat z*(1+Q z/2)
  have hB : AnalyticOnNhd ℂ B Ω := fun z hz=>
    analyticAt_const.sub ((hA z hz).mul (analyticAt_const.add ((hQ z hz).div_const)))
  have hBd : AnalyticOnNhd ℂ (deriv B) Ω := fun z hz=>(hB z hz).deriv
  obtain ⟨C,hC,hbound⟩ := ratioSaddle_complex_bound hcover
    ((hA.mul hR).mul hBd)
  refine ⟨C,hC,?_⟩
  intro Y hY
  have heq : (fun t:ℝ=>(B (t:ℂ)).re)=ᶠ[𝓝 Y] ratioSaddleDefect := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
    dsimp only [B,ratioSaddleDefect]
    rw [(hmatch t ⟨ht.1.le,ht.2.le⟩).1,(hmatch t ⟨ht.1.le,ht.2.le⟩).2]
    simp [Theta]
  have hd := ((hB _ (hcover Y ⟨hY.1.le,hY.2.le⟩)).differentiableAt.hasDerivAt.real_of_complex).congr_of_eventuallyEq heq.symm
  have he : A Y*r Y*deriv ratioSaddleDefect Y =
      (Ahat (Y:ℂ)*R (Y:ℂ)*deriv B (Y:ℂ)).re := by
    rw [hd.deriv,(hmatch Y ⟨hY.1.le,hY.2.le⟩).2,hraw Y ⟨hY.1.le,hY.2⟩]
    simp [Theta]
  rw [he]
  exact (Complex.abs_re_le_norm _).trans (hbound Y ⟨hY.1.le,hY.2.le⟩)

lemma ratioSaddle_transportBeta_bound (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Icc (0:ℝ) y₀,|transportBeta p Y|≤C := by
  obtain ⟨b,hb,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨B,hB,hbound⟩ := dilaton_correction_abs_uniform p
  refine ⟨B/b,div_pos hB hb,?_⟩
  intro Y hY
  have ha : 0 < A Y := hb.trans_le (hA Y hY)
  have h := hbound Y hY
  change |A Y*transportBeta p Y|≤B at h
  rw [abs_mul,abs_of_pos ha] at h
  apply (le_div_iff₀ hb).mpr
  nlinarith [mul_le_mul_of_nonneg_right (hA Y hY) (abs_nonneg (transportBeta p Y))]

end WP.Analysis
