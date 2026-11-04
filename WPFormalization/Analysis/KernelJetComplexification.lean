import WPFormalization.Analysis.KernelInverseComplexification
/-! Holomorphic parameter extensions of every finite kernel jet, on a single
complex neighborhood of the full physical interval. The removable root factor
uses the analytic continuation R, whose critical value is zero; it is not
the totalized physical r outside its interior domain. Actual critical jet
values follow from joint continuity and dense interior restriction. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma kernel_moment_curve_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (q : ℝ → ℂ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => ∫ s : ℝ in (0)..1,
      q s*g (z+R z*w/2*(1-(s:ℂ)^2))) Ω := by
  intro z hz
  apply complex_analyticAt_of_contDiffAt_one
  have hp : ContDiffAt ℂ 1 (fun ζ : ℂ => (ζ,R ζ*w)) z :=
    contDiffAt_id.prodMk ((hR z hz).contDiffAt.mul contDiffAt_const)
  simpa only [Function.comp_def] using
    (kernel_moment_prod_contDiff_one q hq g hg).contDiffAt.comp z hp

lemma iteratedDeriv_K_integral (j : ℕ) (Y u : ℂ) :
    iteratedDeriv j (K Y) u = ∫ s : ℝ in (0)..1,
      ((1-(s:ℂ)^2)/2)^j*iteratedDeriv (j+1) X (Y+u/2*(1-(s:ℂ)^2)) := by
  have h := iteratedDeriv_kernelIntegral (fun _ => 1) continuous_const (deriv X) X_differentiable.deriv j Y u
  simp only [one_mul,←iteratedDeriv_succ'] at h
  change iteratedDeriv j (K Y) u = _ at h
  exact h

lemma iteratedDeriv_H_integral (j : ℕ) (Y u : ℂ) :
    iteratedDeriv j (H Y) u = 3*∫ s : ℝ in (0)..1,
      (s:ℂ)^2*((1-(s:ℂ)^2)/2)^j*iteratedDeriv (j+1) X (Y+u/2*(1-(s:ℂ)^2)) := by
  have he : H Y=(fun w : ℂ => 3*(∫ s : ℝ in (0)..1,
      (s:ℂ)^2*deriv X (Y+w/2*(1-(s:ℂ)^2)))) := rfl
  rw [he,iteratedDeriv_const_mul_field]
  congr 1
  simpa only [iteratedDeriv_succ'] using
    iteratedDeriv_kernelIntegral (fun s : ℝ => (s:ℂ)^2) (by fun_prop)
      (deriv X) X_differentiable.deriv j Y u

lemma K_jet_root_curve_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (j : ℕ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => iteratedDeriv j (K z) (R z*w)) Ω := by
  have he : (fun z : ℂ => iteratedDeriv j (K z) (R z*w)) =
      (fun z => ∫ s : ℝ in (0)..1, ((1-(s:ℂ)^2)/2)^j*
        iteratedDeriv (j+1) X (z+R z*w/2*(1-(s:ℂ)^2))) :=
    funext (fun z => iteratedDeriv_K_integral j z (R z*w))
  rw [he]
  exact kernel_moment_curve_analyticOnNhd Ω R hR _ (by fun_prop)
    _ (iteratedDeriv_X_differentiable (j+1)) w

lemma H_jet_root_curve_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (j : ℕ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => iteratedDeriv j (H z) (R z*w)) Ω := by
  have he : (fun z : ℂ => iteratedDeriv j (H z) (R z*w)) =
      (fun z => 3*(∫ s : ℝ in (0)..1, (s:ℂ)^2*((1-(s:ℂ)^2)/2)^j*
        iteratedDeriv (j+1) X (z+R z*w/2*(1-(s:ℂ)^2)))) :=
    funext (fun z => iteratedDeriv_H_integral j z (R z*w))
  rw [he]
  intro z hz
  exact analyticAt_const.mul (kernel_moment_curve_analyticOnNhd Ω R hR _ (by fun_prop)
    _ (iteratedDeriv_X_differentiable (j+1)) w z hz)

def rootPowerFactor (R : ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (z-(y₀:ℂ))^(j-1)*(dslope R (y₀:ℂ) z)^j/complexAUnit z

lemma rootPowerFactor_analyticOnNhd (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ) ∈ Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hunit : ∀ z ∈ Ω,complexAUnit z≠0) (j : ℕ) :
    AnalyticOnNhd ℂ (rootPowerFactor R j) Ω := by
  intro z hz
  exact (((analyticAt_id.sub analyticAt_const).pow (j-1)).mul
    ((dslope_analyticOnNhd_complex Ω hΩ R hR y₀ hc z hz).pow j)).div
      (complexAUnit_analytic z (mem_univ _)) (hunit z hz)

lemma rootPowerFactor_scale (R : ℂ → ℂ) (j : ℕ) (hj : 1≤j)
    (hR0 : R (y₀:ℂ)=0) (z : ℂ) (hz : z≠(y₀:ℂ)) (hunit : complexAUnit z≠0) :
    rootPowerFactor R j z=R z^j/deriv X z := by
  have hRf := sub_smul_dslope R (y₀:ℂ) z
  simp only [smul_eq_mul,hR0,sub_zero] at hRf
  have hAf := complexAUnit_factor z
  have hδ : z-(y₀:ℂ)≠0 := sub_ne_zero.mpr hz
  have hpow : (z-(y₀:ℂ))^j=(z-(y₀:ℂ))^(j-1)*(z-(y₀:ℂ)) := by
    rw [←pow_succ,Nat.sub_add_cancel hj]
  unfold rootPowerFactor
  rw [←hRf,←hAf,mul_pow,hpow]
  field_simp [hδ,hunit] <;> ring

def regularizedKernelJet (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (j : ℕ) (w z : ℂ) : ℂ :=
  if j=0 then regularizedKernel B R z w else
    rootPowerFactor R j z*iteratedDeriv j (B z) (R z*w)

lemma regularizedKernelJet_analyticOnNhd (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (hB : ∀ j w,AnalyticOnNhd ℂ (fun z => iteratedDeriv j (B z) (R z*w)) Ω)
    (j : ℕ) (w : ℂ) : AnalyticOnNhd ℂ (regularizedKernelJet B R j w) Ω := by
  by_cases hj : j=0
  · subst j
    have he : regularizedKernelJet B R 0 w=(fun z => regularizedKernel B R z w) := by
      funext z;simp [regularizedKernelJet]
    rw [he]
    exact regularizedKernel_analyticOnNhd Ω hΩ hc B R (by simpa only [iteratedDeriv_zero] using hB 0) hunit w
  · have he : regularizedKernelJet B R j w=(fun z => rootPowerFactor R j z*iteratedDeriv j (B z) (R z*w)) := by
      funext z;simp [regularizedKernelJet,hj]
    rw [he]
    intro z hz
    exact (rootPowerFactor_analyticOnNhd Ω hΩ hc R hR hunit j z hz).mul (hB j w z hz)

lemma regularizedKernelJet_restrict_interior (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB_zero : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (hRraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (j : ℕ) (w : ℂ) (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀) :
    regularizedKernelJet B R j w (Y:ℂ)=
      iteratedDeriv j (fun v => B (Y:ℂ) ((r Y:ℂ)*v)/(a Y:ℂ)) w := by
  by_cases hj : j=0
  · subst j
    simp only [regularizedKernelJet,ite_true,iteratedDeriv_zero]
    exact regularizedKernel_restrict_interior B R hB_zero hR0 hRraw Y hY w
  · simp only [regularizedKernelJet,ite_eq_right hj]
    rw [rootPowerFactor_scale R j (by omega) hR0 (Y:ℂ)
      (by exact_mod_cast (ne_of_lt hY.2)) (complexAUnit_ne_zero_physical Y ⟨hY.1,hY.2.le⟩),
      hRraw Y hY,derivX_ofReal,iteratedDeriv_div_const,iteratedDeriv_comp_mul_left]
    ring
lemma jet_eq_factorial_coeff_shift (f : ℂ → ℂ) (j : ℕ) (w : ℂ) :
    iteratedDeriv j f w=(j.factorial:ℂ)*WP.coeff (fun v => f (w+v)) j := by
  unfold WP.coeff
  rw [iteratedDeriv_comp_const_add]
  simp only [add_zero]
  have hfac : (j.factorial:ℂ)≠0 := by exact_mod_cast j.factorial_ne_zero
  field_simp

lemma physical_kernel_jet_continuous (N : ℝ → ℂ → ℂ)
    (hN : ∀ Y∈Icc (0:ℝ) y₀,Differentiable ℂ (N Y))
    (hjoint : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => N (p.1:ℝ) p.2)) (j : ℕ) (w : ℂ) :
    ContinuousOn (fun Y => iteratedDeriv j (N Y) w) (Icc (0:ℝ) y₀) := by
  have hc := physical_kernel_coeff_continuous (fun Y v => N Y (w+v))
    (fun Y hY => (hN Y hY).comp ((differentiable_const w).add differentiable_id))
    (hjoint.comp (continuous_fst.prodMk (continuous_const.add continuous_snd))) j
  have he : (fun Y => iteratedDeriv j (N Y) w) =
      (fun Y => (j.factorial:ℂ)*WP.coeff (fun v => N Y (w+v)) j) :=
    funext (fun Y => jet_eq_factorial_coeff_shift (N Y) j w)
  rw [he]
  exact continuousOn_const.mul hc

lemma regularizedKernelJet_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (B : ℂ → ℂ → ℂ) (N : ℝ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB : ∀ j w,AnalyticOnNhd ℂ (fun z => iteratedDeriv j (B z) (R z*w)) Ω)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (hN : ∀ Y∈Icc (0:ℝ) y₀,Differentiable ℂ (N Y))
    (hjoint : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => N (p.1:ℝ) p.2))
    (hnormal : ∀ Y∈Ico (0:ℝ) y₀,N Y=(fun w => B (Y:ℂ) ((r Y:ℂ)*w)/(a Y:ℂ)))
    (j : ℕ) (w : ℂ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    regularizedKernelJet B R j w (Y:ℂ)=iteratedDeriv j (N Y) w := by
  have ha := regularizedKernelJet_analyticOnNhd Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) B R hR hunit hB j w
  have hc : ContinuousOn (fun Y : ℝ => regularizedKernelJet B R j w (Y:ℂ)) (Icc (0:ℝ) y₀) :=
    fun Y hY => ((ha _ (hcover Y hY)).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have he : EqOn (fun Y : ℝ => regularizedKernelJet B R j w (Y:ℂ))
      (fun Y => iteratedDeriv j (N Y) w) (Ico (0:ℝ) y₀) := by
    intro Y hY
    dsimp only
    rw [hnormal Y hY]
    exact regularizedKernelJet_restrict_interior B R hB0 hR0 hraw j w Y hY
  exact he.of_subset_closure hc (physical_kernel_jet_continuous N hN hjoint j w) Ico_subset_Icc_self
    (by rw [closure_Ico y₀_pos.ne]) hY

lemma normalized_kernel_jets_holomorphic_on_common_domain (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ j : ℕ,∀ w : ℂ,AnalyticOnNhd ℂ (regularizedKernelJet K R j w) Ω ∧
      AnalyticOnNhd ℂ (regularizedKernelJet H R j w) Ω ∧
      ∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet K R j w (Y:ℂ)=iteratedDeriv j (barK Y) w ∧
        regularizedKernelJet H R j w (Y:ℂ)=iteratedDeriv j (barH Y) w := by
  have hc := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hK := K_jet_root_curve_analyticOnNhd Ω R hR
  have hH := H_jet_root_curve_analyticOnNhd Ω R hR
  intro j w
  refine ⟨regularizedKernelJet_analyticOnNhd Ω hΩ hc K R hR hunit hK j w,
    regularizedKernelJet_analyticOnNhd Ω hΩ hc H R hR hunit hH j w,?_⟩
  intro Y hY
  constructor
  · apply regularizedKernelJet_restrict_closed Ω hΩ hcover K barK R hK K_zero hR hR0 hraw hunit
      (fun Y _ => barK_differentiable Y) barK_joint_continuous _ j w Y hY
    intro Y hY
    funext v
    simp only [barK,ite_eq_right (ne_of_lt hY.2)]
  · apply regularizedKernelJet_restrict_closed Ω hΩ hcover H barH R hH H_zero hR hR0 hraw hunit
      (fun Y _ => barH_differentiable Y) barH_joint_continuous _ j w Y hY
    intro Y hY
    funext v
    simp only [barH,ite_eq_right (ne_of_lt hY.2)]
lemma common_holomorphic_kernel_jets :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ Y∈Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ)) ∧
        (∀ j : ℕ,∀ w : ℂ,AnalyticOnNhd ℂ (regularizedKernelJet K R j w) Ω ∧
          AnalyticOnNhd ℂ (regularizedKernelJet H R j w) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,regularizedKernelJet K R j w (Y:ℂ)=iteratedDeriv j (barK Y) w ∧
            regularizedKernelJet H R j w (Y:ℂ)=iteratedDeriv j (barH Y) w) ∧
        (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧
          ∀ Y∈Icc (0:ℝ) y₀,complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧ complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ)) ∧
        (∀ z∈Ω,complexAUnit z≠0) ∧
        (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_inverse_coefficients
  refine ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,?_,?_,?_,hunit,hraw,hR0,hR'⟩
  · exact fun Y hY => ⟨(hmatch Y hY).1,(hmatch Y hY).2.1⟩
  · exact normalized_kernel_jets_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  · intro n
    refine ⟨(hcoeff n).2.2.1,(hcoeff n).2.2.2.1,?_⟩
    intro Y hY
    exact ⟨((hcoeff n).2.2.2.2 Y hY).2.2.1,((hcoeff n).2.2.2.2 Y hY).2.2.2⟩
end WP.Analysis
