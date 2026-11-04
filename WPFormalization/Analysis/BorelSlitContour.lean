import WPFormalization.Analysis.PolarFromZero
import WPFormalization.Analysis.SqrtCutEnvelope
import Mathlib

/-! Raw slit analyticity and a local square-root formula imply the actual bank
limits and the finite radial Laplace dominated-convergence limit. The finite
sector deformation uses the proved logarithmic rectangle identity. No
uniform jump expansion is assumed.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
open scoped Interval

def firstBorelSlit : Set ℂ := {z | z.im≠0 ∨ |z.re|<1}

lemma slit_radial_mem (t θ : ℝ) (ht : 0≤t) (hθ : Real.sin θ≠0) :
    (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)∈firstBorelSlit := by
  by_cases ht0 : t=0
  · subst t
    simp [firstBorelSlit]
  · apply Or.inl
    have he : ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im=t*Real.sin θ := by
      simp [Complex.exp_im]
    rw [he]
    exact mul_ne_zero ht0 hθ

lemma slit_polar_deformation_from_zero (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f firstBorelSlit) (A θ ψ : ℝ) (hA : 0<A)
    (hsin : ∀η∈uIcc θ ψ,Real.sin η≠0) :
    radialSegmentIntegral f θ 0 A-radialSegmentIntegral f ψ 0 A+
      polarArcIntegral f A θ ψ=0 := by
  have hc : ContinuousOn f (Metric.closedBall 0 (1/2:ℝ)) := by
    apply hf.continuousOn.mono
    intro z hz
    apply Or.inr
    have hn : ‖z‖≤1/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact (Complex.abs_re_le_norm z).trans_lt (by linarith)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) (1/2:ℝ)).exists_bound_of_continuousOn hc
  have hsmall : ∀z:ℂ,‖z‖≤1/2 → ‖f z‖≤|M|+1 := by
    intro z hz
    have hm := hM z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    linarith [le_abs_self M]
  have hi (η : ℝ) (hη : η∈uIcc θ ψ) :
      IntervalIntegrable (fun t:ℝ => Complex.exp ((η:ℂ)*Complex.I)*
        f ((t:ℂ)*Complex.exp ((η:ℂ)*Complex.I))) volume 0 A := by
    have hcont : ContinuousOn (fun t:ℝ => Complex.exp ((η:ℂ)*Complex.I)*
        f ((t:ℂ)*Complex.exp ((η:ℂ)*Complex.I))) (uIcc 0 A) := by
      apply ContinuousOn.mul continuous_const.continuousOn
      apply hf.continuousOn.comp (by fun_prop)
      intro t ht
      rw [uIcc_of_le hA.le] at ht
      exact slit_radial_mem t η ht.1 (hsin η hη)
    exact hcont.intervalIntegrable
  apply polar_rectangle_deformation_from_zero f A θ ψ (1/2) (|M|+1) hA
    (by norm_num) (by positivity) hsmall (hi θ left_mem_uIcc) (hi ψ right_mem_uIcc)
  intro δ hδ hδA z hz
  obtain ⟨w,hw,rfl⟩ := hz
  apply (hf _ ?_).differentiableAt.differentiableWithinAt
  apply Or.inl
  have hwi : w.im∈uIcc θ ψ := by simpa using hw.2
  rw [Complex.exp_im]
  exact mul_ne_zero (Real.exp_ne_zero _) (hsin w.im hwi)
def firstCutUpperBank (H α β : ℂ → ℂ) (S : ℂ) (t : ℝ) : ℂ :=
  if t<1 then H (t:ℂ) else S*(-Complex.I*(Real.sqrt (t-1):ℂ))⁻¹*α (t:ℂ)+β (t:ℂ)

def firstCutLowerBank (H α β : ℂ → ℂ) (S : ℂ) (t : ℝ) : ℂ :=
  if t<1 then H (t:ℂ) else S*(Complex.I*(Real.sqrt (t-1):ℂ))⁻¹*α (t:ℂ)+β (t:ℂ)

lemma radial_H_upper_bank_limit (H α β : ℂ → ℂ) (S : ℂ) (r t : ℝ) (hr : 0<r)
    (ht : t∈Ioc 0 (1+r)) (ht1 : t≠1)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    Tendsto (fun θ:ℝ => H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
      (nhdsWithin 0 (Ioi 0)) (nhds (firstCutUpperBank H α β S t)) := by
  have hz : Tendsto (fun θ:ℝ => (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (t:ℂ)) := by
    have hc : Continuous (fun θ:ℝ => (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  by_cases hlt : t<1
  · rw [firstCutUpperBank,ite_eq_left hlt]
    have hmem : (t:ℂ)∈firstBorelSlit := Or.inr (by
      rw [Complex.ofReal_re,abs_of_pos ht.1]
      exact hlt)
    exact (hH _ hmem).continuousAt.tendsto.comp hz
  · have hgt : 1<t := lt_of_le_of_ne (not_lt.mp hlt) ht1.symm
    rw [firstCutUpperBank,ite_eq_right hlt]
    have hmem : (t:ℂ)∈closedBall 1 (2*r) := by
      simp only [mem_closedBall,dist_eq_norm,←Complex.ofReal_one,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hgt)]
      linarith [ht.2]
    apply local_sqrt_cut_upper_bank_limit _ H α β S t r hgt (by linarith [ht.2]) hz
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds Real.pi_pos).filter_mono nhdsWithin_le_nhds] with θ hθ hθπ
      have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
      simpa [Complex.exp_im] using mul_pos ht.1 hs
    · exact (hα _ hmem).continuousAt
    · exact (hβ _ hmem).continuousAt
    · exact hform

lemma radial_H_lower_bank_limit (H α β : ℂ → ℂ) (S : ℂ) (r t : ℝ) (hr : 0<r)
    (ht : t∈Ioc 0 (1+r)) (ht1 : t≠1)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    Tendsto (fun θ:ℝ => H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
      (nhdsWithin 0 (Iio 0)) (nhds (firstCutLowerBank H α β S t)) := by
  have hz : Tendsto (fun θ:ℝ => (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (nhdsWithin 0 (Iio 0)) (nhds (t:ℂ)) := by
    have hc : Continuous (fun θ:ℝ => (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  by_cases hlt : t<1
  · rw [firstCutLowerBank,ite_eq_left hlt]
    have hmem : (t:ℂ)∈firstBorelSlit := Or.inr (by
      rw [Complex.ofReal_re,abs_of_pos ht.1]
      exact hlt)
    exact (hH _ hmem).continuousAt.tendsto.comp hz
  · have hgt : 1<t := lt_of_le_of_ne (not_lt.mp hlt) ht1.symm
    rw [firstCutLowerBank,ite_eq_right hlt]
    have hmem : (t:ℂ)∈closedBall 1 (2*r) := by
      simp only [mem_closedBall,dist_eq_norm,←Complex.ofReal_one,←Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hgt)]
      linarith [ht.2]
    apply local_sqrt_cut_lower_bank_limit _ H α β S t r hgt (by linarith [ht.2]) hz
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show -Real.pi<(0:ℝ) by linarith [Real.pi_pos])).filter_mono nhdsWithin_le_nhds]
        with θ hθ hθπ
      have hs := Real.sin_neg_of_neg_of_neg_pi_lt hθ hθπ
      simpa [Complex.exp_im] using mul_neg_of_pos_of_neg ht.1 hs
    · exact (hα _ hmem).continuousAt
    · exact (hβ _ hmem).continuousAt
    · exact hform

lemma integrable_of_sqrt_cut_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated] [l.NeBot]
    (F : ι → ℝ → E) (f : ℝ → E) (A C : ℝ) (hA : 1 ≤ A)
    (hF : ∀ᶠ i in l,AEStronglyMeasurable (F i) (volume.restrict (Ioc 0 A)))
    (hbound : ∀ᶠ i in l,∀t∈Ioc 0 A,t≠1 →
      ‖F i t‖ ≤ C*(1+(Real.sqrt |1-t|)⁻¹))
    (hlim : ∀t∈Ioc 0 A,t≠1 → Tendsto (fun i => F i t) l (nhds (f t))) :
    IntegrableOn f (Ioc 0 A) := by
  classical
  let μ := volume.restrict (Ioc (0:ℝ) A)
  let G : ι → ℝ → E := fun i t => if AEStronglyMeasurable (F i) μ then F i t else 0
  have hG (i : ι) : AEStronglyMeasurable (G i) μ := by
    by_cases hi : AEStronglyMeasurable (F i) μ
    · simpa only [G,ite_eq_left hi] using hi
    · simp only [G,ite_eq_right hi]
      exact aestronglyMeasurable_const
  have he : ∀ᶠ i in l,G i=F i := by
    filter_upwards [hF] with i hi
    funext t
    exact ite_eq_left hi
  have hlimae : ∀ᵐ t ∂μ,Tendsto (fun i => G i t) l (nhds (f t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,μ.ae_ne 1] with t ht ht1
    apply (hlim t ht ht1).congr'
    filter_upwards [he] with i hi
    exact congr_fun hi.symm t
  have hfmeas : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae l hG hlimae
  have hAi : (0:ℝ)≤A := by linarith
  have hconst : IntervalIntegrable (fun _:ℝ => (1:ℝ)) volume 0 A := intervalIntegrable_const
  have hi := (hconst.add (intervalIntegrable_inv_sqrt_abs_one_sub A hA)).const_mul C
  have hib : IntegrableOn (fun t:ℝ => C*(1+(Real.sqrt |1-t|)⁻¹)) (Ioc 0 A) := by
    simpa only [intervalIntegrable_iff,uIoc_of_le hAi] using hi
  apply hib.mono' hfmeas
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,μ.ae_ne 1] with t ht ht1
  apply le_of_tendsto (hlim t ht ht1).norm
  filter_upwards [hbound] with i hi
  exact hi t ht ht1

def laplaceSlitFunction (H : ℂ → ℂ) (ξ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(ξ:ℂ)*z)*H z

lemma analyticOnNhd_laplaceSlitFunction (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit) (ξ : ℝ) :
    AnalyticOnNhd ℂ (laplaceSlitFunction H ξ) firstBorelSlit := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).cexp.mul (hH z hz)

lemma slit_radial_intervalIntegrable (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f firstBorelSlit) (A θ : ℝ) (hA : 0≤A)
    (hsin : Real.sin θ≠0) :
    IntervalIntegrable (fun t:ℝ => Complex.exp ((θ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) volume 0 A := by
  have hc : ContinuousOn (fun t:ℝ => Complex.exp ((θ:ℂ)*Complex.I)*
      f ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) (uIcc 0 A) := by
    apply ContinuousOn.mul continuous_const.continuousOn
    apply hf.continuousOn.comp (by fun_prop)
    intro t ht
    rw [uIcc_of_le hA] at ht
    exact slit_radial_mem t θ ht.1 hsin
  exact hc.intervalIntegrable

lemma norm_radial_laplace_le (H : ℂ → ℂ) (ξ t θ : ℝ)
    (hξ : 0≤ξ) (ht : 0≤t) (hcos : 0≤Real.cos θ) :
    ‖Complex.exp ((θ:ℂ)*Complex.I)*
      laplaceSlitFunction H ξ ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ ≤
        ‖H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ := by
  have hn : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by rw [Complex.norm_exp];simp
  unfold laplaceSlitFunction
  rw [norm_mul,hn,one_mul,norm_mul,Complex.norm_exp]
  have hre : (-(ξ:ℂ)*((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))).re=
      -(ξ*(t*Real.cos θ)) := by simp [Complex.exp_re]
  rw [hre]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hξ (mul_nonneg ht hcos)))

lemma radial_laplace_bank_integral_limit (H α β : ℂ → ℂ) (S : ℂ) (r ξ : ℝ)
    (hr : 0<r) (hξ : 0≤ξ)
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z)
    (l : Filter ℝ) [l.IsCountablyGenerated] [l.NeBot]
    (hl : Tendsto (fun θ:ℝ => θ) l (nhds 0))
    (hsin : ∀ᶠ θ in l,Real.sin θ≠0) (B : ℝ → ℂ)
    (hbank : ∀t∈Ioc 0 (1+r),t≠1 →
      Tendsto (fun θ:ℝ => H ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) l (nhds (B t))) :
    IntegrableOn (fun t:ℝ => Complex.exp (-(ξ:ℂ)*(t:ℂ))*B t) (Ioc 0 (1+r)) ∧
      Tendsto (fun θ:ℝ => radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 (1+r)) l
        (nhds (∫ t in Ioc 0 (1+r),Complex.exp (-(ξ:ℂ)*(t:ℂ))*B t)) := by
  obtain ⟨φ,hφ,hφπ,hφgap,hφdist⟩ := exists_fixed_cut_angle r hr
  obtain ⟨C,hC,hEnv⟩ := sqrt_cut_radial_envelope_of_analytic H α β S r hr hH hα hβ hform
  let F : ℝ → ℝ → ℂ := fun θ t => Complex.exp ((θ:ℂ)*Complex.I)*
    laplaceSlitFunction H ξ ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
  let f : ℝ → ℂ := fun t => Complex.exp (-(ξ:ℂ)*(t:ℂ))*B t
  have hA : (1:ℝ)≤1+r := by linarith
  have hθnear : ∀ᶠ θ in l,θ∈Icc (-φ) φ ∧ Real.sin θ≠0 := by
    have habs : Tendsto (fun θ:ℝ => |θ|) l (nhds 0) := by
      simpa only [Function.comp_def,abs_zero] using (continuous_abs.tendsto (0:ℝ)).comp hl
    filter_upwards [habs.eventually_lt_const hφ,hsin] with θ hθ hsin
    exact ⟨abs_le.mp hθ.le,hsin⟩
  have hF : ∀ᶠ θ in l,AEStronglyMeasurable (F θ) (volume.restrict (Ioc 0 (1+r))) := by
    filter_upwards [hθnear] with θ hθ
    exact (slit_radial_intervalIntegrable (laplaceSlitFunction H ξ)
      (analyticOnNhd_laplaceSlitFunction H hH ξ) (1+r) θ (by linarith) hθ.2).1.aestronglyMeasurable
  have hbound : ∀ᶠ θ in l,∀t∈Ioc 0 (1+r),t≠1 →
      ‖F θ t‖≤C*(1+(Real.sqrt |1-t|)⁻¹) := by
    filter_upwards [hθnear] with θ hθ
    intro t ht ht1
    have hu : ‖Complex.exp ((θ:ℂ)*Complex.I)‖=1 := by rw [Complex.norm_exp];simp
    have hcos : 0≤Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1.1],by linarith [hθ.1.2]⟩
    apply (norm_radial_laplace_le H ξ t θ hξ ht.1.le hcos).trans
    apply hEnv t ⟨ht.1.le,ht.2⟩ ht1 _ hu (hφdist θ hθ.1)
    have hi : ((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)).im=t*Real.sin θ := by simp [Complex.exp_im]
    rw [hi]
    exact mul_ne_zero ht.1.ne' hθ.2
  have hunit : Tendsto (fun θ:ℝ => Complex.exp ((θ:ℂ)*Complex.I)) l (nhds 1) := by
    have hc : Continuous (fun θ:ℝ => Complex.exp ((θ:ℂ)*Complex.I)) := by fun_prop
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,Complex.exp_zero] using (hc.tendsto (0:ℝ)).comp hl
  have hlim (t : ℝ) (ht : t∈Ioc 0 (1+r)) (ht1 : t≠1) :
      Tendsto (fun θ:ℝ => F θ t) l (nhds (f t)) := by
    have hz : Tendsto (fun θ:ℝ => (t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) l (nhds (t:ℂ)) := by
      simpa only [mul_one] using tendsto_const_nhds.mul hunit
    have he : Tendsto (fun θ:ℝ => Complex.exp (-(ξ:ℂ)*((t:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))) l
        (nhds (Complex.exp (-(ξ:ℂ)*(t:ℂ)))) :=
      Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul hz)
    simpa only [F,f,laplaceSlitFunction,one_mul] using hunit.mul (he.mul (hbank t ht ht1))
  refine ⟨integrable_of_sqrt_cut_limit l F f (1+r) C hA hF hbound hlim,?_⟩
  have hdct := sqrt_cut_dominated_integral_limit l F f (1+r) C hA hF hbound hlim
  simpa only [radialSegmentIntegral,intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤1+r),F,f] using hdct

end WP.Analysis
