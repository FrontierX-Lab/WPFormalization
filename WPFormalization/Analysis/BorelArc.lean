import WPFormalization.Analysis.BorelSlitContour
import Mathlib

/-! Circular joining arcs for a first square-root Borel cut. Their actual
integrability and endpoint limits give exact upper and lower finite-bank
identities. Compact arc bounds are derived from the raw local formula.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
open scoped Interval

lemma sin_ne_zero_on_symmetric_interval (φ θ : ℝ) (hφ : φ<Real.pi)
    (hθ : θ∈Icc (-φ) φ) (hθ0 : θ≠0) : Real.sin θ≠0 := by
  rcases lt_or_gt_of_ne hθ0 with hn|hp
  · exact (Real.sin_neg_of_neg_of_neg_pi_lt hn (by linarith [hθ.1])).ne
  · exact (Real.sin_pos_of_pos_of_lt_pi hp (by linarith [hθ.2])).ne'

lemma slit_arc_intervalIntegrable (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f firstBorelSlit) (A φ M : ℝ)
    (hA : 0<A) (hφ : 0<φ) (hφπ : φ<Real.pi)
    (hbound : ∀θ∈Icc (-φ) φ,‖f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M) :
    IntervalIntegrable (fun θ:ℝ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*
      f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) volume (-φ) φ := by
  let T : Set ℝ := Icc (-φ) φ \ {0}
  let F : ℝ → ℂ := fun θ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*
    f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
  have hcont : ContinuousOn F T := by
    apply ContinuousOn.mul (by fun_prop)
    apply hf.continuousOn.comp (by fun_prop)
    intro θ hθ
    apply Or.inl
    have hi : ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im=A*Real.sin θ := by simp [Complex.exp_im]
    rw [hi]
    exact mul_ne_zero hA.ne' (sin_ne_zero_on_symmetric_interval φ θ hφπ hθ.1 (by simpa using hθ.2))
  have hEq : T=ᵐ[volume] Icc (-φ) φ := by
    filter_upwards [volume.ae_ne 0] with θ hθ
    simp [T,hθ]
  have hmeas : AEStronglyMeasurable F (volume.restrict (Icc (-φ) φ)) := by
    rw [←Measure.restrict_congr_set hEq]
    exact hcont.aestronglyMeasurable (measurableSet_Icc.diff (measurableSet_singleton 0))
  have hmaj : Integrable (fun _:ℝ => A*M) (volume.restrict (Icc (-φ) φ)) := integrable_const _
  have hi : IntegrableOn F (Icc (-φ) φ) := by
    apply hmaj.mono' hmeas
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro θ hθ
    have hn : ‖(A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖=A := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,Complex.norm_exp]
      simp
    dsimp [F]
    rw [norm_mul,hn]
    exact mul_le_mul_of_nonneg_left (hbound θ hθ) hA.le
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -φ≤φ)).mpr hi

lemma polarArcIntegral_left_limit (f : ℂ → ℂ) (A a b : ℝ) (hab : a≤b)
    (hi : IntervalIntegrable (fun θ:ℝ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*
      f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) volume a b)
    (l : Filter ℝ) (hl : Tendsto (fun θ:ℝ => θ) l (nhds a))
    (hm : ∀ᶠ θ in l,θ∈Icc a b) :
    Tendsto (fun θ:ℝ => polarArcIntegral f A θ b) l (nhds (polarArcIntegral f A a b)) := by
  have hIcc := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  have hU : IntegrableOn (fun θ:ℝ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*
      f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hIcc
  have hc := intervalIntegral.continuousOn_primitive_interval_left hU
  have ht : Tendsto (fun θ:ℝ => θ) l (nhdsWithin a (uIcc a b)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hl,by simpa only [uIcc_of_le hab] using hm⟩
  have h := (hc a left_mem_uIcc).tendsto.comp ht
  exact tendsto_const_nhds.mul h

lemma polarArcIntegral_right_limit (f : ℂ → ℂ) (A a b : ℝ) (hab : a≤b)
    (hi : IntervalIntegrable (fun θ:ℝ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*
      f ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) volume a b)
    (l : Filter ℝ) (hl : Tendsto (fun θ:ℝ => θ) l (nhds b))
    (hm : ∀ᶠ θ in l,θ∈Icc a b) :
    Tendsto (fun θ:ℝ => polarArcIntegral f A a θ) l (nhds (polarArcIntegral f A a b)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have ht : Tendsto (fun θ:ℝ => θ) l (nhdsWithin b (uIcc a b)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hl,by simpa only [uIcc_of_le hab] using hm⟩
  exact tendsto_const_nhds.mul ((hc b right_mem_uIcc).tendsto.comp ht)
lemma sqrt_cut_arc_uniform_bound (H α β : ℂ → ℂ) (S : ℂ) (r φ : ℝ)
    (hr : 0<r) (hφπ : φ<Real.pi)
    (hφdist : ∀θ∈Icc (-φ) φ,‖Complex.exp ((θ:ℂ)*Complex.I)-1‖≤r/(2*(1+r)))
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    ∃M:ℝ,0<M ∧ ∀θ∈Icc (-φ) φ,‖H ((1+r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M := by
  obtain ⟨C,hC,hEnv⟩ := sqrt_cut_radial_envelope_of_analytic H α β S r hr hH hα hβ hform
  let M : ℝ := C*(1+(Real.sqrt r)⁻¹)+‖H ((1+r:ℝ):ℂ)‖+1
  have hM : 0<M := by dsimp [M];positivity
  refine ⟨M,hM,?_⟩
  intro θ hθ
  by_cases hθ0 : θ=0
  · subst θ
    simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
    dsimp [M]
    push_cast
    nlinarith [show 0≤C*(1+(Real.sqrt r)⁻¹) by positivity]
  · have hu : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by rw [Complex.norm_exp];simp
    have him : (((1+r:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im≠0 := by
      have he : (((1+r:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im=(1+r)*Real.sin θ := by simp [Complex.exp_im]
      rw [he]
      exact mul_ne_zero (by positivity) (sin_ne_zero_on_symmetric_interval φ θ hφπ hθ hθ0)
    have hb := hEnv (1+r) ⟨by positivity,le_rfl⟩ (by linarith) _ hu (hφdist θ hθ) him
    have he : |1-(1+r)|=r := by rw [show (1:ℝ)-(1+r)=-r by ring,abs_neg,abs_of_pos hr]
    rw [he] at hb
    have hec : ((1+r:ℝ):ℂ)=(1+r:ℂ) := by push_cast;rfl
    rw [hec] at hb
    exact hb.trans (by dsimp [M];linarith [norm_nonneg (H ((1+r:ℝ):ℂ))])

lemma polarArc_laplace_exp_bound (H : ℂ → ℂ) (A φ M ξ a b : ℝ)
    (hA : 0<A) (hφπ : φ≤Real.pi) (hM : 0≤M) (hξ : 0≤ξ)
    (ha : a∈Icc (-φ) φ) (hb : b∈Icc (-φ) φ)
    (hH : ∀θ∈Icc (-φ) φ,‖H ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M) :
    ‖polarArcIntegral (laplaceSlitFunction H ξ) A a b‖≤
      (A*Real.exp (-(ξ*(A*Real.cos φ)))*M)*|b-a| := by
  let γ : ℝ → ℂ := fun θ => (A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  have hmem (θ : ℝ) (hθ : θ∈uIcc a b) : θ∈Icc (-φ) φ := by
    rcases mem_uIcc.mp hθ with h|h <;> constructor <;> linarith [ha.1,ha.2,hb.1,hb.2,h.1,h.2]
  have hnorm (θ : ℝ) : ‖γ θ‖=A := by
    dsimp [γ]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,Complex.norm_exp]
    simp
  have hre (θ : ℝ) (hθ : θ∈uIcc a b) : A*Real.cos φ≤(γ θ).re := by
    have hc : Real.cos φ≤Real.cos θ := by
      simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hφπ (abs_le.mpr (hmem θ hθ))
    have he : (γ θ).re=A*Real.cos θ := by dsimp [γ];simp [Complex.exp_re]
    rw [he]
    exact mul_le_mul_of_nonneg_left hc hA.le
  have hi := compact_contour_laplace_norm_bound (fun θ => H (γ θ)) γ γ a b ξ (A*Real.cos φ)
    A M hξ hA.le hM hre (fun θ _ => (hnorm θ).le) (fun θ hθ => hH θ (hmem θ hθ))
  simpa only [polarArcIntegral,laplaceSlitFunction,γ,norm_mul,Complex.norm_I,one_mul,mul_assoc] using hi

lemma norm_laplaceSlitFunction_le (H : ℂ → ℂ) (ξ : ℝ) (z : ℂ)
    (hξ : 0≤ξ) (hz : 0≤z.re) : ‖laplaceSlitFunction H ξ z‖≤‖H z‖ := by
  unfold laplaceSlitFunction
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  simpa using neg_nonpos.mpr (mul_nonneg hξ hz)

lemma finite_slit_upper_bank_identity (H α β : ℂ → ℂ) (S : ℂ) (r ξ φ : ℝ)
    (hr : 0<r) (hξ : 0≤ξ) (hφ : 0<φ) (hφπ : φ<Real.pi/2)
    (hφdist : ∀θ∈Icc (-φ) φ,‖Complex.exp ((θ:ℂ)*Complex.I)-1‖≤r/(2*(1+r)))
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    radialSegmentIntegral (laplaceSlitFunction H ξ) φ 0 (1+r)=
      (∫ t in Ioc 0 (1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutUpperBank H α β S t)+
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) 0 φ := by
  let l := nhdsWithin (0:ℝ) (Ioi 0)
  have hl : Tendsto (fun θ:ℝ => θ) l (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ θ in l,Real.sin θ≠0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with θ hθ hθπ
    exact (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
  obtain ⟨hBank,hRad⟩ := radial_laplace_bank_integral_limit H α β S r ξ hr hξ hH hα hβ hform
    l hl hs (firstCutUpperBank H α β S)
    (fun t ht ht1 => radial_H_upper_bank_limit H α β S r t hr ht ht1 hH hα hβ hform)
  have hf := analyticOnNhd_laplaceSlitFunction H hH ξ
  have hA : 0<1+r := by linarith
  have hφπ' : φ<Real.pi := by linarith [Real.pi_pos]
  obtain ⟨M,hM,hMB⟩ := sqrt_cut_arc_uniform_bound H α β S r φ hr hφπ' hφdist hH hα hβ hform
  have hFBound (θ : ℝ) (hθ : θ∈Icc (-φ) φ) :
      ‖laplaceSlitFunction H ξ ((1+r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M := by
    apply (norm_laplaceSlitFunction_le H ξ _ hξ ?_).trans (hMB θ hθ)
    have hc : 0≤Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
    simpa [Complex.exp_re] using mul_nonneg hA.le hc
  have hInt := slit_arc_intervalIntegrable (laplaceSlitFunction H ξ) hf (1+r) φ M hA hφ hφπ' (fun θ hθ => by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using hFBound θ hθ)
  have hSub : uIcc (0:ℝ) φ ⊆ uIcc (-φ) φ := by
    rw [uIcc_of_le hφ.le,uIcc_of_le (by linarith : -φ≤φ)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hm : ∀ᶠ θ in l,θ∈Icc 0 φ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hφ).filter_mono nhdsWithin_le_nhds] with θ hθ hθφ
    exact ⟨hθ.le,hθφ.le⟩
  have hArc := polarArcIntegral_left_limit (laplaceSlitFunction H ξ) (1+r) 0 φ hφ.le
    (hInt.mono_set hSub) l hl hm
  have hLim := (hRad.sub (tendsto_const_nhds (x:=radialSegmentIntegral (laplaceSlitFunction H ξ) φ 0 (1+r)))).add hArc
  have hEq : (fun θ:ℝ => radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 (1+r)-
      radialSegmentIntegral (laplaceSlitFunction H ξ) φ 0 (1+r)+
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) θ φ)=ᶠ[l](fun _=>0) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hφ).filter_mono nhdsWithin_le_nhds] with θ hθ hθφ
    apply slit_polar_deformation_from_zero (laplaceSlitFunction H ξ) hf (1+r) θ φ hA
    intro η hη
    rw [uIcc_of_le hθφ.le] at hη
    exact (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hθ hη.1)
      (lt_of_le_of_lt hη.2 hφπ')).ne'
  have hZero : Tendsto (fun θ:ℝ => radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 (1+r)-
      radialSegmentIntegral (laplaceSlitFunction H ξ) φ 0 (1+r)+
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) θ φ) l (nhds 0) :=
    tendsto_const_nhds.congr' hEq.symm
  have hh := tendsto_nhds_unique hLim hZero
  linear_combination -hh

lemma finite_slit_lower_bank_identity (H α β : ℂ → ℂ) (S : ℂ) (r ξ φ : ℝ)
    (hr : 0<r) (hξ : 0≤ξ) (hφ : 0<φ) (hφπ : φ<Real.pi/2)
    (hφdist : ∀θ∈Icc (-φ) φ,‖Complex.exp ((θ:ℂ)*Complex.I)-1‖≤r/(2*(1+r)))
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    radialSegmentIntegral (laplaceSlitFunction H ξ) (-φ) 0 (1+r)=
      (∫ t in Ioc 0 (1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*firstCutLowerBank H α β S t)-
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) (-φ) 0 := by
  let l := nhdsWithin (0:ℝ) (Iio 0)
  have hl : Tendsto (fun θ:ℝ => θ) l (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ θ in l,Real.sin θ≠0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show -Real.pi<(0:ℝ) by linarith [Real.pi_pos])).filter_mono nhdsWithin_le_nhds]
      with θ hθ hθπ
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hθ hθπ).ne
  obtain ⟨hBank,hRad⟩ := radial_laplace_bank_integral_limit H α β S r ξ hr hξ hH hα hβ hform
    l hl hs (firstCutLowerBank H α β S)
    (fun t ht ht1 => radial_H_lower_bank_limit H α β S r t hr ht ht1 hH hα hβ hform)
  have hf := analyticOnNhd_laplaceSlitFunction H hH ξ
  have hA : 0<1+r := by linarith
  have hφπ' : φ<Real.pi := by linarith [Real.pi_pos]
  obtain ⟨M,hM,hMB⟩ := sqrt_cut_arc_uniform_bound H α β S r φ hr hφπ' hφdist hH hα hβ hform
  have hFBound (θ : ℝ) (hθ : θ∈Icc (-φ) φ) :
      ‖laplaceSlitFunction H ξ ((1+r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M := by
    apply (norm_laplaceSlitFunction_le H ξ _ hξ ?_).trans (hMB θ hθ)
    have hc : 0≤Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1],by linarith [hθ.2]⟩
    simpa [Complex.exp_re] using mul_nonneg hA.le hc
  have hInt := slit_arc_intervalIntegrable (laplaceSlitFunction H ξ) hf (1+r) φ M hA hφ hφπ' (fun θ hθ => by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using hFBound θ hθ)
  have hSub : uIcc (-φ) (0:ℝ) ⊆ uIcc (-φ) φ := by
    rw [uIcc_of_le (by linarith : -φ≤0),uIcc_of_le (by linarith : -φ≤φ)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hm : ∀ᶠ θ in l,θ∈Icc (-φ) 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show -φ<(0:ℝ) by linarith)).filter_mono nhdsWithin_le_nhds]
      with θ hθ hθφ
    exact ⟨hθφ.le,hθ.le⟩
  have hArc := polarArcIntegral_right_limit (laplaceSlitFunction H ξ) (1+r) (-φ) 0 (by linarith)
    (hInt.mono_set hSub) l hl hm
  have hLim := ((tendsto_const_nhds (x:=radialSegmentIntegral (laplaceSlitFunction H ξ) (-φ) 0 (1+r))).sub hRad).add hArc
  have hEq : (fun θ:ℝ => radialSegmentIntegral (laplaceSlitFunction H ξ) (-φ) 0 (1+r)-
      radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 (1+r)+
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) (-φ) θ)=ᶠ[l](fun _=>0) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show -φ<(0:ℝ) by linarith)).filter_mono nhdsWithin_le_nhds]
      with θ hθ hθφ
    apply slit_polar_deformation_from_zero (laplaceSlitFunction H ξ) hf (1+r) (-φ) θ hA
    intro η hη
    rw [uIcc_of_le hθφ.le] at hη
    exact (Real.sin_neg_of_neg_of_neg_pi_lt (lt_of_le_of_lt hη.2 hθ)
      (lt_of_lt_of_le (by linarith : -Real.pi< -φ) hη.1)).ne
  have hZero : Tendsto (fun θ:ℝ => radialSegmentIntegral (laplaceSlitFunction H ξ) (-φ) 0 (1+r)-
      radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 (1+r)+
      polarArcIntegral (laplaceSlitFunction H ξ) (1+r) (-φ) θ) l (nhds 0) :=
    tendsto_const_nhds.congr' hEq.symm
  have hh := tendsto_nhds_unique hLim hZero
  linear_combination hh

end WP.Analysis
