import WPFormalization.Analysis.PolarContour
import Mathlib

/-! The finite sector contour identity from its actual zero endpoint.
The inner circular arc and both small radial segments are bounded by their
lengths and vanish as their radius tends to zero.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter
open scoped Interval

lemma radialSegmentIntegral_norm_bound (f : ℂ → ℂ) (M r θ : ℝ)
    (hr : 0 ≤ r) (h : ∀z:ℂ,‖z‖≤r → ‖f z‖≤M) :
    ‖radialSegmentIntegral f θ 0 r‖≤M*r := by
  unfold radialSegmentIntegral
  have hb : ‖∫ t in (0:ℝ)..r,Complex.exp ((θ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ ≤ M*|r-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le hr] at ht
    have hn : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by rw [Complex.norm_exp];simp
    rw [norm_mul,hn,one_mul]
    apply h
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1.le,hn,mul_one]
    exact ht.2
  simpa only [sub_zero,abs_of_nonneg hr] using hb

lemma polarArcIntegral_norm_bound (f : ℂ → ℂ) (M r θ ψ : ℝ)
    (hr : 0 ≤ r) (h : ∀z:ℂ,‖z‖≤r → ‖f z‖≤M) :
    ‖polarArcIntegral f r θ ψ‖≤(r*M)*|ψ-θ| := by
  unfold polarArcIntegral
  rw [norm_mul,Complex.norm_I,one_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have hn : ‖(r:ℂ)*Complex.exp ((t:ℂ)*Complex.I)‖=r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,Complex.norm_exp]
    simp
  rw [norm_mul,hn]
  exact mul_le_mul_of_nonneg_left (h _ hn.le) hr

lemma polar_rectangle_deformation_from_zero (f : ℂ → ℂ) (A θ ψ ρ M : ℝ)
    (hA : 0 < A) (hρ : 0 < ρ) (_hM : 0 ≤ M)
    (hsmall : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖f z‖ ≤ M)
    (hθ : IntervalIntegrable (fun t:ℝ => Complex.exp ((θ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) volume 0 A)
    (hψ : IntervalIntegrable (fun t:ℝ => Complex.exp ((ψ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((ψ:ℂ)*Complex.I))) volume 0 A)
    (hf : ∀ δ : ℝ, 0 < δ → δ < A → DifferentiableOn ℂ f
      (Complex.exp '' (Complex.Rectangle ((Real.log δ : ℂ) + (θ : ℂ) * Complex.I)
        ((Real.log A : ℂ) + (ψ : ℂ) * Complex.I)))) :
    radialSegmentIntegral f θ 0 A-radialSegmentIntegral f ψ 0 A+
      polarArcIntegral f A θ ψ=0 := by
  let C := radialSegmentIntegral f θ 0 A-radialSegmentIntegral f ψ 0 A+
    polarArcIntegral f A θ ψ
  have hb (δ : ℝ) (hδ : 0<δ) (hδA : δ<A) (hδρ : δ≤ρ) :
      ‖C‖≤(M*(2+|ψ-θ|))*δ := by
    have hsub0 : uIcc (0:ℝ) δ ⊆ uIcc 0 A := by
      rw [uIcc_of_le hδ.le,uIcc_of_le hA.le]
      exact Icc_subset_Icc le_rfl hδA.le
    have hsubA : uIcc δ A ⊆ uIcc (0:ℝ) A := by
      rw [uIcc_of_le hδA.le,uIcc_of_le hA.le]
      exact Icc_subset_Icc hδ.le le_rfl
    have hsplitθ : radialSegmentIntegral f θ 0 δ+radialSegmentIntegral f θ δ A=
        radialSegmentIntegral f θ 0 A := by
      exact intervalIntegral.integral_add_adjacent_intervals (hθ.mono_set hsub0) (hθ.mono_set hsubA)
    have hsplitψ : radialSegmentIntegral f ψ 0 δ+radialSegmentIntegral f ψ δ A=
        radialSegmentIntegral f ψ 0 A := by
      exact intervalIntegral.integral_add_adjacent_intervals (hψ.mono_set hsub0) (hψ.mono_set hsubA)
    have hc := polar_rectangle_deformation f (Real.log δ) (Real.log A) θ ψ (hf δ hδ hδA)
    rw [Real.exp_log hδ,Real.exp_log hA] at hc
    have he : C=radialSegmentIntegral f θ 0 δ-radialSegmentIntegral f ψ 0 δ+
        polarArcIntegral f δ θ ψ := by
      dsimp [C]
      linear_combination hc-hsplitθ+hsplitψ
    have hB : ∀z:ℂ,‖z‖≤δ → ‖f z‖≤M := fun z hz => hsmall z (hz.trans hδρ)
    rw [he]
    calc
      _ ≤ ‖radialSegmentIntegral f θ 0 δ-radialSegmentIntegral f ψ 0 δ‖+
          ‖polarArcIntegral f δ θ ψ‖ := norm_add_le _ _
      _ ≤ (‖radialSegmentIntegral f θ 0 δ‖+‖radialSegmentIntegral f ψ 0 δ‖)+
          ‖polarArcIntegral f δ θ ψ‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (M*δ+M*δ)+(δ*M)*|ψ-θ| := by
        exact add_le_add (add_le_add
          (radialSegmentIntegral_norm_bound f M δ θ hδ.le hB)
          (radialSegmentIntegral_norm_bound f M δ ψ hδ.le hB))
          (polarArcIntegral_norm_bound f M δ θ ψ hδ.le hB)
      _ = _ := by ring
  have hlim : Tendsto (fun δ:ℝ => (M*(2+|ψ-θ|))*δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun δ:ℝ => (M*(2+|ψ-θ|))*δ) := by fun_prop
    simpa only [mul_zero] using hc.continuousAt.tendsto.mono_left
      (show nhdsWithin (0:ℝ) (Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hnorm : ‖C‖≤0 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hA).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds] with δ hδ hδA hδρ
    exact hb δ hδ hδA hδρ.le
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
end WP.Analysis
