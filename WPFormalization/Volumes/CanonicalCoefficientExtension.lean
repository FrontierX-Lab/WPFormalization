import WPFormalization.Volumes.InteriorExtractedCoefficientExtension
import WPFormalization.Volumes.CriticalCoefficientGevrey
import WPFormalization.HigherOrder.OriginCoefficientExtension
import WPFormalization.Analysis.BoundedComplexFamilyGluing
import WPFormalization.HigherOrder.ExtensionDefinitions
/-! The ORIGINAL extracted coefficients admit ONE holomorphic Gevrey-two family across the full closed parameter interval. Actual origin and critical endpoint families join the genuinely joint interior Morse families. Overlap identities precede bounded finite-cover gluing. The critical value remains the original one-sided limUnder, and the physical first root is never continued through its endpoint by totalization. Continuity follows from the actual common real restriction. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
set_option maxHeartbeats 1500000 in
lemma canonical_coefficient_gevrey_extension (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ HigherOrder.GevreyExtension (HigherOrder.extractedCoefficient P p) C B := by
  have hlocal : ∀ Y0 ∈ Icc (0 : ℝ) y₀, ∃ r C B : ℝ, 0 < r ∧ 0 < C ∧ 0 < B ∧
      ∃ F : ℕ → ℂ → ℂ,
        (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball (Y0 : ℂ) r)) ∧
        (∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → (Y : ℂ) ∈ Metric.ball (Y0 : ℂ) r →
          F j (Y : ℂ) = (HigherOrder.extractedCoefficient P p j Y : ℂ)) ∧
        ∀ j z, z ∈ Metric.ball (Y0 : ℂ) r → ‖F j z‖ ≤ C * B^j * (j.factorial : ℝ)^2 := by
    intro Y0 hY0
    by_cases hz : Y0 = 0
    · subst Y0
      obtain ⟨F,η,C,B,hη,hηy,hC,hB,hFa,hF0,hFr,hCont,hLim⟩ :=
        HigherOrder.actual_origin_coefficient_extension P p hp
      refine ⟨η/2,C,B,half_pos hη,hC,hB,F,?_,?_,?_⟩
      · intro j
        simpa only [Complex.ofReal_zero] using (hFa j).1.mono
          (Metric.ball_subset_ball (half_le_self hη.le))
      · intro j Y hY hdist
        have hd : |Y| < η/2 := by
          simpa only [Complex.ofReal_zero,Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using hdist
        have hYη : Y ≤ η := (le_abs_self Y).trans (hd.le.trans (half_le_self hη.le))
        exact hFr j Y ⟨hY.1,hYη⟩
      · intro j z hz
        have hd : ‖z‖ < η/2 := by simpa only [Complex.ofReal_zero,Metric.mem_ball,dist_zero_right] using hz
        exact (hFa j).2 z (hd.le.trans (half_le_self hη.le))
    by_cases hcrit : Y0 = y₀
    · subst Y0
      obtain ⟨d⟩ := exists_criticalGaussianCoordinateData
      obtain ⟨F,R,C,B,hR,hRy,hC,hB,hFa,hFb,hFr,hEnd,hF0⟩ := d.original_raw_critical_gevrey_two P p hp
      let G : ℕ → ℂ → ℂ := fun j z => F j ((y₀ : ℂ)-z)
      have hdist (z : ℂ) (hz : z ∈ Metric.ball (y₀ : ℂ) (R/2)) : ‖(y₀ : ℂ)-z‖ ≤ R := by
        have hd : ‖(y₀ : ℂ)-z‖ < R/2 := by
          simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hz
        exact hd.le.trans (half_le_self hR.le)
      refine ⟨R/2,C,B,half_pos hR,hC,hB,G,?_,?_,?_⟩
      · intro j z hz
        exact (hFa j _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hdist z hz)).comp
          (analyticAt_const.sub analyticAt_id)
      · intro j Y hY hball
        have hd : |Y-y₀| < R/2 := by
          simpa only [Metric.mem_ball,complex_dist_ofReal_eq_real,Real.dist_eq] using hball
        have hδR : y₀-Y < R := by
          rw [abs_of_nonpos (sub_nonpos.mpr hY.2)] at hd
          linarith
        by_cases hYe : Y = y₀
        · subst Y
          dsimp only [G]
          rw [sub_self,hEnd j,HigherOrder.extractedCoefficient,
            ite_eq_right y₀_pos.ne',ite_eq_left rfl]
        have hYzero : Y ≠ 0 := by intro hzero; rw [hzero] at hδR; linarith
        have hδ : y₀-Y ∈ Ioo (0 : ℝ) R := ⟨sub_pos.mpr (lt_of_le_of_ne hY.2 hYe),hδR⟩
        dsimp only [G]
        rw [←Complex.ofReal_sub,HigherOrder.extractedCoefficient,ite_eq_right hYzero,ite_eq_right hYe]
        simpa only [sub_sub_cancel] using hFr (y₀-Y) hδ j
      · intro j z hz
        exact hFb j _ (hdist z hz)
    exact interior_extractedCoefficient_local_extension P p hp Y0
      ⟨lt_of_le_of_ne hY0.1 (Ne.symm hz),lt_of_le_of_ne hY0.2 hcrit⟩
  obtain ⟨Ω,F,C,B,hΩ,hcover,hC,hB,hFa,hFr,hFb⟩ :=
    exists_common_bounded_complex_family_extension 0 y₀
      (fun j Y => (HigherOrder.extractedCoefficient P p j Y : ℂ)) hlocal
  exact ⟨C,B,hC,hB,Ω,F,hΩ,hcover,hFa,hFr,hFb⟩

lemma continuousOn_of_gevreyExtension (a : ℕ → ℝ → ℝ) (C B : ℝ)
    (ha : HigherOrder.GevreyExtension a C B) :
    ∀ j, ContinuousOn (a j) (Icc (0 : ℝ) y₀) := by
  obtain ⟨Ω,F,hΩ,hcover,hFa,hFr,hFb⟩ := ha
  intro j
  have hc : ContinuousOn (fun Y : ℝ => (F j (Y : ℂ)).re) (Icc (0 : ℝ) y₀) := by
    intro Y hY
    have hF : ContinuousAt (fun t : ℝ => F j (t : ℂ)) Y :=
      ContinuousAt.comp (f := fun t : ℝ => (t : ℂ)) (x := Y)
        (hFa j (Y : ℂ) (hcover Y hY)).continuousAt Complex.continuous_ofReal.continuousAt
    exact (Complex.continuous_re.continuousAt.comp hF).continuousWithinAt
  apply hc.congr
  intro Y hY
  exact (congrArg Complex.re (hFr j Y hY)).trans (Complex.ofReal_re _) |>.symm
end WP.Analysis
