import WPFormalization.Volumes.BoundaryTilt

/-! Uniform continuity of the actual inverse parameter under bounded Gaussian
exponential tilts. The compact injective XR map supplies the inverse modulus;
the genuine variance identity gives v ≥ Ψ and hence σ² ≥ min(h,hΨ).
No asymptotic chart or continuity/variance assumption is an input. -/

noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma inverse_parameter_physical_uniform_continuity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ico (0 : ℝ) xCritical,
      ∀ y ∈ Ico (0 : ℝ) xCritical, |x-y| < δ → |inverseY x-inverseY y| < ε := by
  let f : Icc (0 : ℝ) y₀ → ℝ := fun Y => XR Y
  have hf : Continuous f := by
    exact XR_continuous.comp continuous_subtype_val
  have hinj : Function.Injective f := by
    intro Y Z he
    apply Subtype.ext
    exact XR_strictMonoOn.injOn Y.property.2 Z.property.2 he
  have hemb := hf.isClosedEmbedding hinj
  have hinv : ContinuousOn inverseY (f '' Set.univ) := by
    apply hemb.isEmbedding.isInducing.continuousOn_image_iff.mpr
    have heq : inverseY ∘ f = fun Y : Icc (0 : ℝ) y₀ => (Y : ℝ) := by
      funext Y
      exact Analysis.inverseY_eq_of_root _ _ Y.property.2 rfl
    rw [heq]
    exact continuous_subtype_val.continuousOn
  have hcompact : IsCompact (f '' Set.univ) := isCompact_univ.image hf
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hinv) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  have hxmem : x ∈ f '' Set.univ := by
    have hb := inverseY_branch x hx
    exact ⟨⟨inverseY x,hb.1.1,hb.1.2.le⟩,mem_univ _,hb.2⟩
  have hymem : y ∈ f '' Set.univ := by
    have hb := inverseY_branch y hy
    exact ⟨⟨inverseY y,hb.1.1,hb.1.2.le⟩,mem_univ _,hb.2⟩
  simpa only [Real.dist_eq] using hmod x hxmem y hymem (by simpa only [Real.dist_eq] using hxy)

lemma boundary_variance_ge_mean (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical) :
    Psi x ≤ euler Psi x := by
  let Y := inverseY x
  have hY : Y ∈ Ico (0 : ℝ) y₀ := (inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hXY : XR Y=x := (inverseY_branch x ⟨hx.1.le,hx.2⟩).2
  have hY0 : Y ≠ 0 := by
    intro hz
    rw [hz,XR_zero] at hXY
    linarith [hx.1]
  have hYi : Y ∈ Ioo (0 : ℝ) y₀ := ⟨lt_of_le_of_ne hY.1 hY0.symm,hY.2⟩
  have hp := Analysis.ratioSaddle_mean_pos Y hYi
  have hb := Analysis.ratioSaddleDefect_lower Y hY
  have hv := Analysis.ratioSaddle_variance_formula Y hY
  rw [hXY] at hp hv
  rw [hv]
  nlinarith [mul_nonneg (by linarith : 0 ≤ Analysis.ratioSaddleDefect Y) (sq_nonneg (Psi x))]

lemma boundary_inverse_parameter_tilt_uniform (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ h : ℝ, 0 < h → ∀ x ∈ Ioo (0 : ℝ) xCritical,
      M ≤ min h (h*Psi x) → ∀ u : ℝ, |u| ≤ R →
      x*Real.exp (u/Real.sqrt (h*euler Psi x)) ∈ Ioo (0 : ℝ) xCritical →
      |inverseY (x*Real.exp (u/Real.sqrt (h*euler Psi x)))-inverseY x| ≤ ε := by
  obtain ⟨δ,hδ,hmod⟩ := inverse_parameter_physical_uniform_continuity ε hε
  have hxc := Analysis.xCritical_pos_parameter
  obtain ⟨η,hη,hExp⟩ := Metric.continuousAt_iff.mp (show ContinuousAt Real.exp (0 : ℝ) from Real.continuous_exp.continuousAt)
    (δ/xCritical) (div_pos hδ hxc)
  let S : ℝ := max 1 (2*R/η)
  have hS : 0 < S := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨S^2,sq_pos_of_pos hS,?_⟩
  intro h hh x hx hm u hu hxt
  let σ : ℝ := Real.sqrt (h*euler Psi x)
  have hv : 0 < euler Psi x := mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos hh hv)
  have hvar := boundary_variance_ge_mean x hx
  have hSsq : S^2 ≤ σ^2 := by
    rw [Real.sq_sqrt (mul_pos hh hv).le]
    exact hm.trans ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left hvar hh.le))
  have hSσ : S ≤ σ := by nlinarith [sq_nonneg (σ-S)]
  have hRσ : R/σ ≤ η/2 := by
    apply (div_le_iff₀ hσ).mpr
    have hs := le_max_right (1 : ℝ) (2*R/η)
    change 2*R/η ≤ S at hs
    have hh' := (div_le_iff₀ hη).mp hs
    nlinarith [mul_le_mul_of_nonneg_left hSσ hη.le]
  have hut : |u/σ| < η := by
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_div_of_nonneg_right hu hσ.le).trans_lt (hRσ.trans_lt (half_lt_self hη))
  have he : |Real.exp (u/σ)-1| < δ/xCritical := by
    have he := hExp (by simpa only [Real.dist_eq,sub_zero] using hut)
    simpa only [Real.dist_eq,Real.exp_zero] using he
  have hd : |x*Real.exp (u/σ)-x| < δ := by
    calc
      _ = x*|Real.exp (u/σ)-1| := by rw [←mul_sub_one,abs_mul,abs_of_pos hx.1]
      _ ≤ xCritical*|Real.exp (u/σ)-1| := mul_le_mul_of_nonneg_right hx.2.le (abs_nonneg _)
      _ < xCritical*(δ/xCritical) := mul_lt_mul_of_pos_left he hxc
      _ = δ := mul_div_cancel₀ δ hxc.ne'
  exact (hmod _ ⟨hxt.1.le,hxt.2⟩ x ⟨hx.1.le,hx.2⟩ hd).le

/-- The uniform modulus on the actual stable genus/marking parameters. -/
lemma boundary_inverse_parameter_tilt_uniform_stable (p : ℕ) (R ε : ℝ)
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ g : ℕ, Stable g p → ∀ x ∈ Ioo (0 : ℝ) xCritical,
      M ≤ min (complexity g p : ℝ) ((complexity g p : ℝ)*Psi x) →
      ∀ u : ℝ, |u| ≤ R →
      x*Real.exp (u/Real.sqrt ((complexity g p : ℝ)*euler Psi x)) ∈ Ioo (0 : ℝ) xCritical →
      |inverseY (x*Real.exp (u/Real.sqrt ((complexity g p : ℝ)*euler Psi x)))-inverseY x| ≤ ε := by
  obtain ⟨M,hM,hmod⟩ := boundary_inverse_parameter_tilt_uniform R ε hR hε
  refine ⟨M,hM,?_⟩
  intro g hs x hx hm u hu ht
  have hh : 0 < (complexity g p : ℝ) := by
    have hn : 0 < complexity g p := by unfold complexity Stable at *; omega
    exact_mod_cast hn
  exact hmod _ hh x hx hm u hu ht

end WP.BoundaryConvolution
