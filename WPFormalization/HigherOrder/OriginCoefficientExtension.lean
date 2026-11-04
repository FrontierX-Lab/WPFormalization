import WPFormalization.HigherOrder.OriginPoissonRawOverlap
import WPFormalization.HigherOrder.OriginPoissonParameterFamily
/-! A single complex Gevrey-two family extends the original CG3 coefficients
across the origin. The actual raw formula is identified by the full-circle
Poisson comparison; its right limits agree with the prescribed marked
endpoint coefficients. The common disk is chosen before all orders. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma origin_canonical_extension_of_raw_matching (P:PsiTheory) (p:ℕ) (AC:ℕ→ℂ→ℂ) (η:ℝ)
    (hη:0<η) (hηy:η<y₀)
    (hAC:∀n,AnalyticOnNhd ℂ (AC n) (Metric.ball 0 η))
    (hzero:∀n,AC n 0=(markedCoefficient P p n 0:ℂ))
    (hraw:∀n Y,Y∈Ioo (0:ℝ) η→AC n (Y:ℂ)=(rawExtractedCoefficient P p n Y:ℂ)):
    (∀n Y,Y∈Icc (0:ℝ) (η/2)→AC n (Y:ℂ)=(extractedCoefficient P p n Y:ℂ))∧
    (∀n,ContinuousOn (extractedCoefficient P p n) (Icc (0:ℝ) (η/2)))∧
    ∀n,Tendsto (rawExtractedCoefficient P p n) (𝓝[>] (0:ℝ)) (𝓝 (markedCoefficient P p n 0)):=by
  have hrest:∀n Y,Y∈Icc (0:ℝ) (η/2)→AC n (Y:ℂ)=(extractedCoefficient P p n Y:ℂ):=by
    intro n Y hY
    by_cases hY0:Y=0
    · subst Y
      rw[extractedCoefficient_at_zero]
      simpa only[Complex.ofReal_zero] using hzero n
    have hYp:0<Y:=lt_of_le_of_ne hY.1 (Ne.symm hY0)
    have hYe:Y<η:=hY.2.trans_lt (half_lt_self hη)
    rw[extractedCoefficient,ite_eq_right hY0,ite_eq_right (ne_of_lt (hYe.trans hηy))]
    exact hraw n Y ⟨hYp,hYe⟩
  refine ⟨hrest,?_,?_⟩
  · intro n
    have hc:ContinuousOn (fun Y:ℝ=>(AC n (Y:ℂ)).re) (Icc (0:ℝ) (η/2)):=by
      intro Y hY
      have hYn:‖(Y:ℂ)‖<η:=by
        rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hY.1]
        exact hY.2.trans_lt (half_lt_self hη)
      have ha:AnalyticAt ℂ (AC n) (Y:ℂ):=hAC n (Y:ℂ) (by simpa only[Metric.mem_ball,dist_zero_right] using hYn)
      exact (Complex.continuous_re.continuousAt.comp
        (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
    apply hc.congr
    intro Y hY
    exact (congrArg Complex.re (hrest n Y hY) |>.trans (Complex.ofReal_re _)).symm
  · intro n
    have ha:AnalyticAt ℂ (AC n) 0:=hAC n 0 (Metric.mem_ball_self hη)
    have hc:ContinuousAt (fun Y:ℝ=>(AC n (Y:ℂ)).re) 0:=by
      have hac:ContinuousAt (AC n) (((0:ℝ):ℂ)):=by simpa only[Complex.ofReal_zero] using ha.continuousAt
      have ht:ContinuousAt (fun Y:ℝ=>AC n (Y:ℂ)) 0:=
        ContinuousAt.comp (f:=fun Y:ℝ=>(Y:ℂ)) (x:=(0:ℝ)) hac Complex.continuous_ofReal.continuousAt
      exact Complex.continuous_re.continuousAt.comp ht
    have ht:Tendsto (fun Y:ℝ=>(AC n (Y:ℂ)).re) (𝓝[>] (0:ℝ)) (𝓝 (markedCoefficient P p n 0)):=by
      have hz:(AC n ((0:ℝ):ℂ)).re=markedCoefficient P p n 0:=by rw[Complex.ofReal_zero,hzero,Complex.ofReal_re]
      rw[←hz]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards[(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with Y hYe hY0
    exact congrArg Complex.re (hraw n Y ⟨hY0,hYe⟩) |>.trans (Complex.ofReal_re _)
end WP.HigherOrder
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_origin_coefficient_extension_of_parameter_data (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)(hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(AC:ℕ→ℂ→ℂ)(η E D:ℝ),0<η ∧ η<y₀ ∧ 0<E ∧ 0<D ∧
      (∀j,AnalyticOnNhd ℂ (AC j) (Metric.ball 0 η) ∧
        ∀z:ℂ,‖z‖≤η→‖AC j z‖≤E*D^j*(j.factorial:ℝ)^2) ∧
      (∀j,AC j 0=(markedCoefficient P p j 0:ℂ)) ∧
      (∀j Y,Y∈Icc (0:ℝ) η→AC j (Y:ℂ)=(extractedCoefficient P p j Y:ℂ)) ∧
      (∀j,ContinuousOn (extractedCoefficient P p j) (Icc (0:ℝ) η)) ∧
      ∀j,Tendsto (rawExtractedCoefficient P p j) (𝓝[>] (0:ℝ)) (𝓝 (markedCoefficient P p j 0)):=by
  obtain ⟨S,Bc,Z,δ,E,D,hδ,hE,hD,hS,hS0,hSd,hBc0,hSr,hcoef,hzero,hrawν⟩:=
    actual_origin_poisson_raw_overlap_of_parameter_data P p hp Ω L C B hΩ hcover hC hB hLa hL0 hLr hLb
  obtain ⟨η0,hη0,hη0y,hparam,hfamily,hAC0,htrace⟩:=
    originExtractedCoefficientFamily_parameter_extension P p S Bc L Z δ E D hδ hS hSr hcoef hzero
  let AC:ℕ→ℂ→ℂ:=originExtractedCoefficientFamily P p S Bc L Z
  have hμ:Tendsto (fun Y:ℝ=>density Y/2) (𝓝 0) (𝓝 (0:ℝ)):=by
    have hd:ContinuousAt (fun Y:ℝ=>density Y/2) 0:=
      ((WP.Analysis.density_analyticAt_interior 0 ⟨le_rfl,y₀_pos⟩).continuousAt).div_const 2
    simpa only[density_zero_value,zero_div] using hd.tendsto
  obtain ⟨r,hr,hbound⟩:=Metric.eventually_nhds_iff.mp (hμ.eventually (eventually_lt_nhds hδ))
  let η:ℝ:=min η0 (r/2)
  have hη:0<η:=lt_min hη0 (half_pos hr)
  have hηη:η≤η0:=min_le_left _ _
  have hηr:η<r:=(min_le_right _ _).trans_lt (half_lt_self hr)
  have hηy:η<y₀:=hηη.trans_lt hη0y
  have hraw:∀j Y,Y∈Ioo (0:ℝ) η→AC j (Y:ℂ)=(rawExtractedCoefficient P p j Y:ℂ):=by
    intro j Y hY
    have hYy:Y∈Ico (0:ℝ) y₀:=⟨hY.1.le,hY.2.trans hηy⟩
    have hd:0<density Y:=by
      have hh:=WP.Analysis.density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hYy hY.1
      simpa only[density_zero_value] using hh
    have hν:0<density Y/2:=by positivity
    have hνδ:density Y/2<δ:=hbound (by rw[Real.dist_eq,sub_zero,abs_of_pos hY.1];exact hY.2.trans hηr)
    have hinv:densityY (2*(density Y/2))=Y:=by
      rw[show 2*(density Y/2)=density Y by ring]
      have hs:=WP.Analysis.densityY_spec (density Y) hd.le
      exact WP.Analysis.density_strictMonoOn.injOn hs.1 hYy hs.2
    change originExtractedCoefficientFamily P p S Bc L Z j (Y:ℂ)=_
    rw[htrace j Y ⟨hY.1.le,hY.2.le.trans hηη⟩,hrawν (density Y/2) ⟨hν,hνδ⟩ j,hinv]
  obtain ⟨hrest,hcont,hlim⟩:=origin_canonical_extension_of_raw_matching P p AC η hη hηy
    (fun j=>(hfamily j).1.mono (Metric.ball_subset_ball hηη)) hAC0 hraw
  refine ⟨AC,η/2,E,D,half_pos hη,(half_lt_self hη).trans hηy,hE,hD,?_,hAC0,hrest,hcont,hlim⟩
  intro j
  constructor
  · exact (hfamily j).1.mono (Metric.ball_subset_ball ((half_le_self hη.le).trans hηη))
  · intro z hz
    exact (hfamily j).2 z (hz.trans ((half_le_self hη.le).trans hηη))
lemma actual_origin_coefficient_extension (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃(AC:ℕ→ℂ→ℂ)(η E D:ℝ),0<η ∧ η<y₀ ∧ 0<E ∧ 0<D ∧
      (∀j,AnalyticOnNhd ℂ (AC j) (Metric.ball 0 η) ∧
        ∀z:ℂ,‖z‖≤η→‖AC j z‖≤E*D^j*(j.factorial:ℝ)^2) ∧
      (∀j,AC j 0=(markedCoefficient P p j 0:ℂ)) ∧
      (∀j Y,Y∈Icc (0:ℝ) η→AC j (Y:ℂ)=(extractedCoefficient P p j Y:ℂ)) ∧
      (∀j,ContinuousOn (extractedCoefficient P p j) (Icc (0:ℝ) η)) ∧
      ∀j,Tendsto (rawExtractedCoefficient P p j) (𝓝[>] (0:ℝ)) (𝓝 (markedCoefficient P p j 0)):=by
  obtain ⟨C,B,hC,hB,Ω,a,L0,hΩ,hcover,hana,hrest,hbound⟩:=markedCoefficient_common_complex_gevrey_two P p hp
  let L:ℕ→ℂ→ℂ:=fun j z=>if j=0 then 1 else L0 j z
  have hLa:∀j,AnalyticOnNhd ℂ (L j) Ω:=by
    intro j
    by_cases hj:j=0
    · simp only[L,hj,ite_true];exact analyticOnNhd_const
    · simpa only[L,ite_eq_right hj] using (hana j).2
  have hL0:∀z,L 0 z=1:=by intro z;simp[L]
  have hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ):=by
    intro j Y hY
    by_cases hj:j=0
    · subst j;simp[L,markedCoefficient_zero]
    · simpa only[L,ite_eq_right hj] using (hrest j Y hY).2
  have hLb:∀j z,z∈Ω→‖L j z‖≤(C+1)*B^j*(j.factorial:ℝ)^2:=by
    intro j z hz
    by_cases hj:j=0
    · subst j
      simp only[L,ite_true,norm_one,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      linarith
    · simp only[L,ite_eq_right hj]
      have hb:‖L0 j z‖≤C*B^j*(j.factorial:ℝ)^2:=
        (le_add_of_nonneg_left (norm_nonneg (a j z))).trans (hbound j z hz)
      apply hb.trans
      gcongr
      linarith
  exact actual_origin_coefficient_extension_of_parameter_data P p hp Ω L (C+1) B hΩ hcover (by positivity) hB hLa hL0 hLr hLb
end WP.HigherOrder
