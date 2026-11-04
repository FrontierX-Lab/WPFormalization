import WPFormalization.Analysis.StationaryComplexExtension
import WPFormalization.Analysis.ComplexKernelCalculus
import WPFormalization.Analysis.HarmonicProbability

/-! Actual normalized kernel data on one complex parameter neighborhood.
Mathlib dslope removes the common simple zero of the kernel numerator and a.
The physical normalized kernels identify the critical value by their proved
limits. A and the canonical total weight therefore extend holomorphically
on the same open set as the root continuation. Parameter analyticity is
proved for every fixed kernel argument, with exact restrictions including
the critical point. No joint holomorphy or higher coefficient theorem is
assumed or asserted by this module. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma regularizedK_restrict_interior (R : ℂ → ℂ) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) (w : ℂ) :
    regularizedKernel K R (Y:ℂ) w=barK Y w := by
  rw [regularizedKernel_restrict_interior K R K_zero hR0 hR Y hY w,barK,ite_eq_right (ne_of_lt hY.2)]

lemma regularizedH_restrict_interior (R : ℂ → ℂ) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) (w : ℂ) :
    regularizedKernel H R (Y:ℂ) w=barH Y w := by
  rw [regularizedKernel_restrict_interior H R H_zero hR0 hR Y hY w,barH,ite_eq_right (ne_of_lt hY.2)]

lemma regularizedK_critical (R : ℂ → ℂ) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (w : ℂ)
    (hK : AnalyticAt ℂ (fun z => regularizedKernel K R z w) (y₀:ℂ)) :
    regularizedKernel K R (y₀:ℂ) w=1-w := by
  have hmap : Tendsto (fun Y : ℝ => (Y:ℂ)) (𝓝[<] y₀) (𝓝 (y₀:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hExt := hK.continuousAt.tendsto.comp hmap
  have he : (fun Y : ℝ => regularizedKernel K R (Y:ℂ) w) =ᶠ[𝓝[<] y₀] (fun Y => barK Y w) := by
    filter_upwards [eventually_interior_left] with Y hY
    exact regularizedK_restrict_interior R hR0 hR Y hY w
  exact tendsto_nhds_unique hExt ((normalized_kernels_tendsto_critical_pointwise w).1.congr' he.symm)

lemma regularizedH_critical (R : ℂ → ℂ) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (w : ℂ)
    (hH : AnalyticAt ℂ (fun z => regularizedKernel H R z w) (y₀:ℂ)) :
    regularizedKernel H R (y₀:ℂ) w=1-(3/5:ℂ)*w := by
  have hmap : Tendsto (fun Y : ℝ => (Y:ℂ)) (𝓝[<] y₀) (𝓝 (y₀:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hExt := hH.continuousAt.tendsto.comp hmap
  have he : (fun Y : ℝ => regularizedKernel H R (Y:ℂ) w) =ᶠ[𝓝[<] y₀] (fun Y => barH Y w) := by
    filter_upwards [eventually_interior_left] with Y hY
    exact regularizedH_restrict_interior R hR0 hR Y hY w
  exact tendsto_nhds_unique hExt ((normalized_kernels_tendsto_critical_pointwise w).2.congr' he.symm)

lemma common_holomorphic_normalized_kernel_data :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ w : ℂ,AnalyticOnNhd ℂ (fun z => regularizedKernel K R z w) Ω ∧
          AnalyticOnNhd ℂ (fun z => regularizedKernel H R z w) Ω) ∧
        (∀ Y ∈ Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ) ∧
          ∀ w : ℂ,regularizedKernel K R (Y:ℂ) w=barK Y w ∧ regularizedKernel H R (Y:ℂ) w=barH Y w) ∧
        (∀ z ∈ Ω,complexAUnit z≠0) ∧
        (∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨U,hU,hconn,hcover,F,R,Q,hF,hR,hQ,hmatch,hraw,hR0,hR'⟩ :=
    stationary_root_mass_common_complex_extension
  let Ω : Set ℂ := U ∩ {z | complexAUnit z≠0}
  have hΩ : IsOpen Ω := hU.inter (isOpen_ne_fun complexAUnit_analytic.continuous continuous_const)
  have hcoverΩ : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω := fun Y hY =>
    ⟨hcover Y hY,complexAUnit_ne_zero_physical Y hY⟩
  have hK (w : ℂ) : AnalyticOnNhd ℂ (fun z => regularizedKernel K R z w) Ω :=
    regularizedKernel_analyticOnNhd Ω hΩ (hcoverΩ y₀ ⟨y₀_pos.le,le_rfl⟩) K R
      (fun w => (K_root_curve_analyticOnNhd U R hR w).mono inter_subset_left) (fun z hz => hz.2) w
  have hH (w : ℂ) : AnalyticOnNhd ℂ (fun z => regularizedKernel H R z w) Ω :=
    regularizedKernel_analyticOnNhd Ω hΩ (hcoverΩ y₀ ⟨y₀_pos.le,le_rfl⟩) H R
      (fun w => (H_root_curve_analyticOnNhd U R hR w).mono inter_subset_left) (fun z hz => hz.2) w
  let Ahat : ℂ → ℂ := fun z => regularizedKernel H R z 1/3
  have hAhat : AnalyticOnNhd ℂ Ahat Ω := fun z hz => (hH 1 z hz).div_const
  refine ⟨Ω,hΩ,hcoverΩ,R,Q,Ahat,hR.mono inter_subset_left,hQ.mono inter_subset_left,hAhat,
    fun w => ⟨hK w,hH w⟩,?_,(fun z hz => hz.2),hraw,hR0,hR'⟩
  intro Y hY
  have hnorm (w : ℂ) : regularizedKernel K R (Y:ℂ) w=barK Y w ∧
      regularizedKernel H R (Y:ℂ) w=barH Y w := by
    by_cases he : Y=y₀
    · subst Y
      have hk := regularizedK_critical R hR0 hraw w (hK w _ (hcoverΩ y₀ ⟨y₀_pos.le,le_rfl⟩))
      have hh := regularizedH_critical R hR0 hraw w (hH w _ (hcoverΩ y₀ ⟨y₀_pos.le,le_rfl⟩))
      simpa only [barK,barH,ite_true] using And.intro hk hh
    · have hYi : Y ∈ Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
      exact ⟨regularizedK_restrict_interior R hR0 hraw Y hYi w,regularizedH_restrict_interior R hR0 hraw Y hYi w⟩
  refine ⟨(hmatch Y hY).2,?_,hnorm⟩
  dsimp [Ahat]
  rw [(hnorm 1).2]
  have he : barH Y 1=((barH Y 1).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using barH_one_im_zero Y
  rw [he]
  simp only [A,Complex.ofReal_div,Complex.ofReal_ofNat]

lemma actual_complex_root_identity (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hraw : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) :
    ∀ z ∈ Ω,K z (R z)=0 := by
  have hK : AnalyticOnNhd ℂ (fun z => K z (R z)) Ω := by
    simpa only [mul_one] using K_root_curve_analyticOnNhd Ω R hR 1
  have hc : y₀/2 ∈ Ioo (0:ℝ) y₀ := ⟨half_pos y₀_pos,half_lt_self y₀_pos⟩
  have hreal : ∀ᶠ Y : ℝ in 𝓝 (y₀/2),K (Y:ℂ) (R (Y:ℂ))=0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with Y hY
    rw [hraw Y ⟨hY.1.le,hY.2⟩]
    exact K_r_zero Y ⟨hY.1.le,hY.2⟩
  exact complex_identity_of_real_germ _ (fun _ => 0) Ω (y₀/2) hK analyticOnNhd_const
    hconn (hcover _ ⟨hc.1.le,hc.2.le⟩) hreal

end WP.Analysis
