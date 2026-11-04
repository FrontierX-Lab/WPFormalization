import WPFormalization.Volumes.BoundaryConvolutionIdentification

/-! The explicit positive convolution has the original boundary-volume Taylor
coefficients. The identification uses the proved real string EGF and the
complex identity principle on the actual cusp disk. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

lemma scalar_boundary_series_ofReal (c : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hr : ENNReal.ofReal R ≤
      (FormalMultilinearSeries.ofScalars ℂ (fun q => ((c q:ℂ)/(q.factorial:ℂ)))).radius)
    (x : ℝ) (hx : |x| < R) :
    let S := FormalMultilinearSeries.ofScalars ℂ (fun q => ((c q:ℂ)/(q.factorial:ℂ)))
    S.sum (x:ℂ) = Complex.ofReal (S.sum (x:ℂ)).re := by
  dsimp only
  let S := FormalMultilinearSeries.ofScalars ℂ (fun q => ((c q:ℂ)/(q.factorial:ℂ)))
  have hm : (x:ℂ) ∈ Metric.eball (0:ℂ) S.radius := by
    rw [Metric.mem_eball,edist_dist,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hx) hr
  have hs := (S.hasSum hm).mapL Complex.imCLM
  have hs0 : HasSum (fun _ : ℕ => (0:ℝ)) (S.sum (x:ℂ)).im := by
    convert hs using 1
    · ext j
      simp only [S,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,
        ←Complex.ofReal_natCast,←Complex.ofReal_div,←Complex.ofReal_pow,
        ←Complex.ofReal_mul,Complex.imCLM_apply,Complex.ofReal_im]
    · rfl
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (hasSum_zero.unique hs0).symm

lemma boundaryG_coefficient (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) (hp : 1 ≤ p)
    (L : Fin p → ℝ) (k : ℕ) :
    WP.coeff (boundaryG P g p L) k = Complex.ofReal
      (boundaryVolumeModel P g (k+p) (Fin.append (fun _ : Fin k => 0) L) /
        ((2*Real.pi^2)^(dimension g (k+p))*(k.factorial:ℝ))) := by
  let t : Fin p → ℝ := fun i => lengthTime (L i)
  let c : ℕ → ℝ := fun q => stringBoundaryAmplitude P g t q 0
  let S := FormalMultilinearSeries.ofScalars ℂ (fun q => ((c q:ℂ)/(q.factorial:ℂ)))
  have ht : ∀ i, 0 ≤ t i := fun i => lengthTime_nonneg _
  have hfamily := externalStringAmplitude_positive_egf P g hg hp
    (fun i b => realTranslationWeight (t i) b)
    (fun i b Y => realTranslationWeight_analyticAt _ _ _)
    (fun i b Y => realTranslationWeight_hasDerivAt _ _ _)
    (fun i b Y hY => realTranslationWeight_nonneg _ (ht i) _ _ hY)
  have hrad : ENNReal.ofReal xCritical ≤ S.radius :=
    Analysis.ofReal_le_of_positive_interval_le xCritical Analysis.xCritical_pos_parameter _ hfamily.1
  have hR : 0 < S.radius := lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr Analysis.xCritical_pos_parameter) hrad
  have hSa : AnalyticOnNhd ℂ S.sum (Metric.ball 0 xCritical) := by
    intro z hz
    exact Analysis.scalar_egf_analyticAt_of_radius c xCritical Analysis.xCritical_pos_parameter
      hrad z (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have hGa : AnalyticOnNhd ℂ (boundaryG P g p L) (Metric.ball 0 xCritical) := by
    intro z hz
    exact boundaryG_analyticAt P g p L z (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have hstable : Stable g p := by unfold Stable;omega
  have hreal (x : ℝ) (hx : x ∈ Ioo 0 xCritical) : boundaryG P g p L (x:ℂ)=S.sum (x:ℂ) := by
    rw [boundaryG_ofReal P g p hp hstable L x ⟨hx.1.le,hx.2⟩,
      scalar_boundary_series_ofReal c xCritical Analysis.xCritical_pos_parameter hrad x
        (by simpa only [abs_of_pos hx.1] using hx.2)]
    apply congrArg Complex.ofReal
    have hh := hfamily.2 0 x ⟨hx.1.le,hx.2⟩
    exact hh.symm
  have hxc := Analysis.xCritical_pos_parameter
  have hc : xCritical/2 ∈ Ioo (0:ℝ) xCritical := ⟨half_pos hxc,half_lt_self hxc⟩
  have hmem : ((xCritical/2:ℝ):ℂ) ∈ Metric.ball 0 xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.1] using hc.2
  have heq := Analysis.complex_identity_of_real_germ (boundaryG P g p L) S.sum
    (Metric.ball 0 xCritical) (xCritical/2) hGa hSa
    (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
      exact hreal x hx)
  have hevent : boundaryG P g p L =ᶠ[𝓝 (0:ℂ)] S.sum := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hxc] with z hz
    exact heq hz
  rw [WP.coeff,hevent.iteratedDeriv_eq,Analysis.scalar_series_iteratedDeriv_zero c hR k]
  dsimp only [c,t,lengthTime]
  rw [stringBoundaryAmplitude_zero_eq_boundary_scaled]
  push_cast
  ring

end WP.BoundaryConvolution
