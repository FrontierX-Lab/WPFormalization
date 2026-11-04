import WPFormalization.Analysis.SqrtBanks
import Mathlib

/-! A local square-root cut gives an actual uniform radial majorant, bank limits,
and a dominated-convergence limit. The fixed contour angle is constructed from
continuity. No bound on a Painleve jump is assumed.
-/
noncomputable section
namespace WP.Analysis
open Complex Set Metric Filter MeasureTheory

lemma sqrt_cut_radial_envelope (H α β : ℂ → ℂ) (S : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hH : ContinuousOn H (Metric.closedBall 0 (1 - r)))
    (hα : ContinuousOn α (Metric.closedBall 1 (2 * r)))
    (hβ : ContinuousOn β (Metric.closedBall 1 (2 * r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    ∃ C:ℝ,0<C ∧ ∀t:ℝ,t∈Icc 0 (1+r) → t≠1 → ∀u:ℂ,
      ‖u‖=1 → ‖u-1‖ ≤ r/(2*(1+r)) → ((t:ℂ)*u).im≠0 →
      ‖H ((t:ℂ)*u)‖ ≤ C * (1 + (Real.sqrt |1 - t|)⁻¹) := by
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0:ℂ) (1 - r)).exists_bound_of_continuousOn hH
  obtain ⟨Mα,hMα⟩ := (isCompact_closedBall (1:ℂ) (2 * r)).exists_bound_of_continuousOn hα
  obtain ⟨Mβ,hMβ⟩ := (isCompact_closedBall (1:ℂ) (2 * r)).exists_bound_of_continuousOn hβ
  let M : ℝ := |Mα|+|Mβ|+1
  have hM : 0 ≤ M := by dsimp [M];positivity
  let C : ℝ := |M₀|+‖S‖*M+M+1
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro t ht ht1 u hu hu1 him
  have ht0 : 0 ≤ t := ht.1
  have hA : 0 < 1+r := by linarith
  have hnorm : ‖(t:ℂ)*u‖=t := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0,hu,mul_one]
  have hq : 0 ≤ (Real.sqrt |1 - t|)⁻¹ := by positivity
  by_cases hsmall : t≤1-r
  · have hmem : (t:ℂ)*u∈Metric.closedBall 0 (1 - r) := by
      rw [Metric.mem_closedBall,dist_zero_right,hnorm]
      exact hsmall
    calc
      _ ≤ M₀ := hM₀ _ hmem
      _ ≤ |M₀| := le_abs_self _
      _ ≤ C := by dsimp [C];nlinarith [mul_nonneg (norm_nonneg S) hM]
      _ ≤ C * (1 + (Real.sqrt |1 - t|)⁻¹) := by nlinarith
  · have habs : |t-1|≤r := abs_le.mpr ⟨by linarith,by linarith [ht.2]⟩
    have hdist : ‖(t:ℂ)*u-1‖≤|t-1|+t*‖u-1‖ := by
      have he : (t:ℂ)*u-1=((t-1:ℝ):ℂ)+(t:ℂ)*(u-1) := by push_cast;ring
      rw [he]
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0] using
        norm_add_le ((t-1:ℝ):ℂ) ((t:ℂ)*(u-1))
    have htprod : t*‖u-1‖≤r/2 := by
      calc
        _ ≤ (1+r)*(r/(2*(1+r))) := mul_le_mul ht.2 hu1 (norm_nonneg _) hA.le
        _ = r/2 := by field_simp
    have hnear : ‖(t:ℂ)*u-1‖<2*r := by linarith
    have hmem : (t:ℂ)*u∈Metric.closedBall 1 (2 * r) := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hnear.le
    have hαM : ‖α ((t:ℂ)*u)‖≤M := (hMα _ hmem).trans (by
      dsimp [M];linarith [le_abs_self Mα,abs_nonneg Mβ])
    have hβM : ‖β ((t:ℂ)*u)‖≤M := (hMβ _ hmem).trans (by
      dsimp [M];linarith [le_abs_self Mβ,abs_nonneg Mα])
    have hsqrt := norm_inv_sqrt_one_sub_real_mul_unit_bound t ht0 ht1 u hu
    rw [hform _ hnear him]
    calc
      _ ≤ ‖S*(Complex.sqrt (1-(t:ℂ)*u))⁻¹*α ((t:ℂ)*u)‖+‖β ((t:ℂ)*u)‖ := norm_add_le _ _
      _ ≤ (‖S‖*(Real.sqrt |1 - t|)⁻¹)*M+M := by
        rw [norm_mul,norm_mul]
        exact add_le_add (mul_le_mul
          (mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)) hαM (norm_nonneg _) (by positivity)) hβM
      _ ≤ C * (1 + (Real.sqrt |1 - t|)⁻¹) := by
        have hc0 : M≤C := by dsimp [C];nlinarith [abs_nonneg M₀,mul_nonneg (norm_nonneg S) hM]
        have hc1 : ‖S‖*M≤C := by dsimp [C];nlinarith [abs_nonneg M₀]
        nlinarith
lemma sqrt_cut_radial_envelope_of_analytic (H α β : ℂ → ℂ) (S : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hH : AnalyticOnNhd ℂ H {z:ℂ | z.im≠0 ∨ |z.re|<1})
    (hα : AnalyticOnNhd ℂ α (Metric.closedBall 1 (2 * r)))
    (hβ : AnalyticOnNhd ℂ β (Metric.closedBall 1 (2 * r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    ∃ C:ℝ,0<C ∧ ∀t:ℝ,t∈Icc 0 (1+r) → t≠1 → ∀u:ℂ,
      ‖u‖=1 → ‖u-1‖ ≤ r/(2*(1+r)) → ((t:ℂ)*u).im≠0 →
      ‖H ((t:ℂ)*u)‖ ≤ C * (1 + (Real.sqrt |1 - t|)⁻¹) := by
  apply sqrt_cut_radial_envelope H α β S r hr _ hα.continuousOn hβ.continuousOn hform
  apply hH.continuousOn.mono
  intro z hz
  apply Or.inr
  have hn : ‖z‖≤1-r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  exact (Complex.abs_re_le_norm z).trans_lt (by linarith)

lemma exists_fixed_cut_angle (r : ℝ) (hr : 0 < r) :
    ∃ φ:ℝ,0<φ ∧ φ<Real.pi/2 ∧
      1+r/2<(1+r)*Real.cos φ ∧
      ∀θ:ℝ,θ∈Icc (-φ) φ →
        ‖Complex.exp ((θ:ℂ)*Complex.I)-1‖ ≤ r/(2*(1+r)) := by
  have hA : 0<1+r := by linarith
  have htol : 0<r/(2*(1+r)) := by positivity
  have hdist : ∀ᶠ θ:ℝ in nhds 0,
      ‖Complex.exp ((θ:ℂ)*Complex.I)-1‖<r/(2*(1+r)) := by
    have hc : Continuous (fun θ:ℝ => ‖Complex.exp ((θ:ℂ)*Complex.I)-1‖) := by fun_prop
    apply Filter.Tendsto.eventually_lt_const _ hc.continuousAt.tendsto
    simpa using htol
  have hcos : ∀ᶠ θ:ℝ in nhds 0,1+r/2<(1+r)*Real.cos θ := by
    have hc : Continuous (fun θ:ℝ => (1+r)*Real.cos θ) := by fun_prop
    have h0 : 1+r/2<(1+r)*Real.cos (0:ℝ) := by simpa using (by linarith : 1+r/2<1+r)
    exact hc.continuousAt.tendsto.eventually (eventually_gt_nhds h0)
  obtain ⟨δ,hδ,hδprop⟩ := Metric.eventually_nhds_iff.mp (hdist.and hcos)
  let φ : ℝ := min (δ/2) (Real.pi/4)
  have hφ : 0<φ := lt_min (by positivity) (by positivity)
  have hφδ : φ<δ := by dsimp [φ];have := min_le_left (δ/2) (Real.pi/4);linarith
  have hφπ : φ<Real.pi/2 := by
    dsimp [φ]
    have := min_le_right (δ/2) (Real.pi/4)
    linarith [Real.pi_pos]
  have hφprop := hδprop (y:=φ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hφ] using hφδ)
  refine ⟨φ,hφ,hφπ,hφprop.2,?_⟩
  intro θ hθ
  have habs : |θ|≤φ := abs_le.mpr hθ
  exact (hδprop (y:=θ) (by simpa only [Real.dist_eq,sub_zero] using habs.trans_lt hφδ)).1.le

lemma local_sqrt_cut_upper_bank_limit {ι : Type*} {l : Filter ι}
    (z : ι → ℂ) (H α β : ℂ → ℂ) (S : ℂ) (a r : ℝ)
    (ha : 1 < a) (har : a - 1 < 2 * r) (hz : Tendsto z l (nhds (a : ℂ)))
    (him : ∀ᶠ i in l, 0 < (z i).im)
    (hα : ContinuousAt α (a : ℂ)) (hβ : ContinuousAt β (a : ℂ))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    Tendsto (fun i => H (z i)) l
      (nhds (S*(-Complex.I*(Real.sqrt (a-1):ℂ))⁻¹*α (a : ℂ)+β (a : ℂ))) := by
  have hw : Tendsto (fun i => 1-z i) l (nhds (-((a-1:ℝ):ℂ))) := by
    have he : (1:ℂ)-(a : ℂ)=-((a-1:ℝ):ℂ) := by push_cast;ring
    rw [←he]
    exact tendsto_const_nhds.sub hz
  have hwi : ∀ᶠ i in l,(1-z i).im<0 := by
    filter_upwards [him] with i hi
    simpa using hi
  have hsq := (tendsto_sqrt_neg_real_from_lower _ (a-1) (sub_pos.mpr ha) hw hwi).inv₀
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ha)).ne'))
  have hball : (a : ℂ)∈Metric.ball 1 (2 * r) := by
    simpa only [Metric.mem_ball,dist_eq_norm,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ha)] using har
  have hnear := hz.eventually (isOpen_ball.mem_nhds hball)
  have he : (fun i => H (z i))=ᶠ[l]
      (fun i => S*(Complex.sqrt (1-z i))⁻¹*α (z i)+β (z i)) := by
    filter_upwards [hnear,him] with i hi him
    apply hform
    · simpa only [Metric.mem_ball,dist_eq_norm] using hi
    · exact ne_of_gt him
  exact ((tendsto_const_nhds.mul hsq).mul (hα.tendsto.comp hz) |>.add
    (hβ.tendsto.comp hz)).congr' he.symm

lemma local_sqrt_cut_lower_bank_limit {ι : Type*} {l : Filter ι}
    (z : ι → ℂ) (H α β : ℂ → ℂ) (S : ℂ) (a r : ℝ)
    (ha : 1 < a) (har : a - 1 < 2 * r) (hz : Tendsto z l (nhds (a : ℂ)))
    (him : ∀ᶠ i in l, (z i).im < 0)
    (hα : ContinuousAt α (a : ℂ)) (hβ : ContinuousAt β (a : ℂ))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z) :
    Tendsto (fun i => H (z i)) l
      (nhds (S*(Complex.I*(Real.sqrt (a-1):ℂ))⁻¹*α (a : ℂ)+β (a : ℂ))) := by
  have hw : Tendsto (fun i => 1-z i) l (nhds (-((a-1:ℝ):ℂ))) := by
    have he : (1:ℂ)-(a : ℂ)=-((a-1:ℝ):ℂ) := by push_cast;ring
    rw [←he]
    exact tendsto_const_nhds.sub hz
  have hwi : ∀ᶠ i in l,0≤(1-z i).im := by
    filter_upwards [him] with i hi
    simp only [Complex.sub_im,Complex.one_im]
    linarith
  have hsq := (tendsto_sqrt_neg_real_from_upper _ (a-1) (sub_pos.mpr ha) hw hwi).inv₀
    (mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ha)).ne'))
  have hball : (a : ℂ)∈Metric.ball 1 (2 * r) := by
    simpa only [Metric.mem_ball,dist_eq_norm,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ha)] using har
  have hnear := hz.eventually (isOpen_ball.mem_nhds hball)
  have he : (fun i => H (z i))=ᶠ[l]
      (fun i => S*(Complex.sqrt (1-z i))⁻¹*α (z i)+β (z i)) := by
    filter_upwards [hnear,him] with i hi him
    apply hform
    · simpa only [Metric.mem_ball,dist_eq_norm] using hi
    · exact ne_of_lt him
  exact ((tendsto_const_nhds.mul hsq).mul (hα.tendsto.comp hz) |>.add
    (hβ.tendsto.comp hz)).congr' he.symm

lemma sqrt_cut_dominated_integral_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (F : ι → ℝ → E) (f : ℝ → E) (A C : ℝ) (hA : 1 ≤ A)
    (hF : ∀ᶠ i in l, AEStronglyMeasurable (F i) (volume.restrict (Ioc 0 A)))
    (hbound : ∀ᶠ i in l, ∀ t ∈ Ioc 0 A, t ≠ 1 →
      ‖F i t‖ ≤ C * (1 + (Real.sqrt |1 - t|)⁻¹))
    (hlim : ∀ t ∈ Ioc 0 A, t ≠ 1 → Tendsto (fun i => F i t) l (nhds (f t))) :
    Tendsto (fun i => ∫ t in Ioc 0 A,F i t) l (nhds (∫t in Ioc 0 A,f t)) := by
  have hAi : (0:ℝ)≤A := by linarith
  have hconst : IntervalIntegrable (fun _:ℝ => (1:ℝ)) volume 0 A := intervalIntegrable_const
  have hi := (hconst.add (intervalIntegrable_inv_sqrt_abs_one_sub A hA)).const_mul C
  have hib : IntegrableOn (fun t:ℝ => C * (1 + (Real.sqrt |1 - t|)⁻¹)) (Ioc 0 A) := by
    simpa only [intervalIntegrable_iff,uIoc_of_le hAi] using hi
  apply tendsto_integral_filter_of_dominated_convergence _ hF _ hib _
  · filter_upwards [hbound] with i hi
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      (volume.restrict (Ioc (0:ℝ) A)).ae_ne 1] with t ht ht1
    exact hi t ht ht1
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      (volume.restrict (Ioc (0:ℝ) A)).ae_ne 1] with t ht ht1
    exact hlim t ht ht1

end WP.Analysis
