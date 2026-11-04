import WPFormalization.Volumes.CompactPremorseModel
/-! Actual compact pre-Morse amplitudes for a previously fixed canonical
coefficient family. The given inverse-variance scale, actual Bc, coefficient
functions and rate B are preserved exactly. A genuine joint compact-axis
neighborhood supplies one radius and uniform all-order bounds, without
reselecting the coefficient family or an optimal truncation parameter. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma compact_premorse_family_of_fixed_coefficients (P:PsiTheory)(p:ℕ)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hbc:b<xCritical)(L Bc:ℂ→ℂ)
    (hL:∀x∈Icc a b,AnalyticAt ℂ L (x:ℂ))
    (hBc:∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ))
    (Ωf:Set ℂ)(f:ℕ→ℂ→ℂ)(C₀ B:ℝ)(hΩf:IsOpen Ωf)
    (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ωf)(hC₀:0<C₀)(hB:0<B)
    (hFa:∀j,AnalyticOnNhd ℂ (f j) Ωf)
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hfb:∀j z,z∈Ωf→‖f j z‖≤C₀*B^j*(j.factorial:ℝ)^2):
    ∃(U:Set ℂ)(r C:ℝ),IsOpen U ∧ (∀x∈Icc a b,(x:ℂ)∈U) ∧ 0<r ∧ 0<C ∧
      (∀j,AnalyticOnNhd ℂ (compactPremorseAmplitude P Bc L f j) (U ×ˢ Metric.ball 0 r)) ∧
      ∀x∈U,∀u:ℂ,‖u‖<r→‖compactModelPoint L (x,u)‖<xCritical ∧
        ∀j,‖compactPremorseAmplitude P Bc L f j (x,u)‖≤C*B^j*(j.factorial:ℝ)^2:=by
  let K:Set ℂ:=(fun x:ℝ=>(x:ℂ)) '' Icc a b
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  let A:ℂ × ℂ → ℂ:=fun z=>Bc (compactModelPoint L z)/Bc z.1
  let Y:ℂ × ℂ → ℂ:=fun z=>PositiveConvolution.planarInverse P (compactModelPoint L z)
  have hpoint(x:ℝ)(hx:x ∈ Icc a b):x ∈ Ico (0:ℝ) xCritical:=⟨(ha.trans_le hx.1).le,hx.2.trans_lt hbc⟩
  have hAn(x:ℂ)(hx:x ∈ K):AnalyticAt ℂ A (x,0) ∧ A (x,0)=1 := by
    rcases hx with ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have hBct:AnalyticAt ℂ Bc (t:ℂ):=(hBc t htI).1
    have hBcn:Bc (t:ℂ)≠0:=by rw[(hBc t htI).2];exact_mod_cast (extractionB_pos_interior p t htI).ne'
    have harg:=compactModelPoint_analyticAt L (t:ℂ) (hL t ht)
    constructor
    · exact (hBct.comp_of_eq harg (compactModelPoint_axis L (t:ℂ))).div
        (hBct.comp (f:=fun z:ℂ × ℂ=>z.1) analyticAt_fst) hBcn
    · dsimp only[A]
      rw[compactModelPoint_axis,div_self hBcn]
  have hYn(x:ℂ)(hx:x ∈ K):AnalyticAt ℂ Y (x,0) ∧ Y (x,0) ∈ Ωf := by
    rcases hx with ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have htN:‖(t:ℂ)‖<xCritical:=by rw[Complex.norm_of_nonneg htI.1];exact htI.2
    have harg:=compactModelPoint_analyticAt L (t:ℂ) (hL t ht)
    constructor
    · exact (PositiveConvolution.planarInverse_analyticAt P (t:ℂ) htN).comp_of_eq harg
        (compactModelPoint_axis L (t:ℂ))
    · dsimp only[Y]
      rw[compactModelPoint_axis,PositiveConvolution.planarInverse_ofReal P t htI]
      have hy:inverseY t ∈ Ico (0:ℝ) y₀:=(inverseY_branch t htI).1
      exact hcover _ ⟨hy.1,hy.2.le⟩
  obtain ⟨U,hU,hKU,r,hr,hAf,hAb⟩:=compact_axis_composition_gevrey_two_family K hK A Y Ωf hΩf f C₀ B
    hC₀.le hB.le (fun x hx=>(hAn x hx).1) (fun x hx=>(hYn x hx).1)
    (fun x hx=>(hAn x hx).2) (fun x hx=>(hYn x hx).2) hFa hfb
  have hdisk:∀x ∈ K,∀ᶠz:ℂ × ℂ in 𝓝 (x,0),‖compactModelPoint L z‖<xCritical := by
    rintro x ⟨t,ht,rfl⟩
    have htI:=hpoint t ht
    have hn:‖compactModelPoint L ((t:ℂ),0)‖<xCritical := by
      rw[compactModelPoint_axis,Complex.norm_of_nonneg htI.1];exact htI.2
    exact (compactModelPoint_analyticAt L (t:ℂ) (hL t ht)).continuousAt.norm.tendsto.eventually
      (eventually_lt_nhds hn)
  obtain ⟨V,hV,hKV,s,hs,hdisks⟩:=compact_axis_uniform_neighborhood K hK
    (fun z=>‖compactModelPoint L z‖<xCritical) hdisk
  refine ⟨U∩V,min r s,2*C₀,hU.inter hV,(fun x hx=>⟨hKU ⟨x,hx,rfl⟩,hKV ⟨x,hx,rfl⟩⟩),lt_min hr hs,
    by positivity,?_,?_⟩
  · intro j z hz
    exact hAf j z ⟨hz.1.1,Metric.mem_ball.mpr (by
      have hu:‖z.2‖< min r s:=by simpa only[Metric.mem_ball,dist_zero_right] using hz.2
      simpa only[dist_zero_right] using hu.trans_le (min_le_left _ _))⟩
  · intro x hx u hu
    exact ⟨hdisks x hx.2 u (hu.trans_le (min_le_right _ _)),
      fun j=>hAb j x hx.1 u (hu.trans_le (min_le_left _ _))⟩
end WP.Analysis
