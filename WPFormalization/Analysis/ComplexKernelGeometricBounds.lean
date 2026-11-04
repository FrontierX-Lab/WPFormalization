import WPFormalization.Analysis.ComplexKernelJointContinuity
import WPFormalization.Analysis.CompactNonzeroParameters
import WPFormalization.Analysis.WeightMomentComplexification
/-! The genuine Appendix C complex kernel geometric bounds. Joint continuity
and compact nonvanishing produce one parameter neighborhood and one disk
with radius greater than one. Actual Taylor identities connect the normalized
kernel, its first-root deflation and the canonical inverse coefficients.
Cauchy gives geometric decay of w_l and b_d; theta_n is a finite prefix and
is uniformly bounded. Its critical value remains exactly one for every n.
No Gevrey hierarchy estimate or path compatibility is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

lemma normalized_complex_kernels_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hR0 : R (y₀:ℂ)=0) (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ Y∈Icc (0:ℝ) y₀,∀ w : ℂ,regularizedKernel K R (Y:ℂ) w=barK Y w ∧
      regularizedKernel H R (Y:ℂ) w=barH Y w := by
  have hj := normalized_kernel_jets_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  intro Y hY w
  simpa only [regularizedKernelJet,ite_true,iteratedDeriv_zero] using (hj 0 w).2.2 Y hY

lemma common_complex_kernel_circle_control :
    ∃ (Ω : Set ℂ) (R : ℂ → ℂ) (ρ M : ℝ),IsOpen Ω ∧ Convex ℝ Ω ∧
      (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧ 1<ρ ∧ 0<M ∧ AnalyticOnNhd ℂ R Ω ∧
      (∀ z∈closure Ω,complexAUnit z≠0 ∧ complexDeflatedCoeff R 0 z≠0 ∧
        ∀ w : ℂ,‖w‖≤ρ → complexDeflatedKernel R z w≠0 ∧
          ‖(complexDeflatedKernel R z w)⁻¹‖≤M ∧ ‖regularizedKernel H R z w‖≤M) ∧
      (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨U,hU,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_all_kernel_moments
  have haunit : ∀ z∈U,complexAUnit z≠0 := fun z hz => (hunit z hz).2.2.1
  have hc : (y₀:ℂ)∈U := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hD := complexDeflatedKernel_joint_continuous U hU hc R hR hR0 hraw haunit
  have hH := (normalized_complex_kernels_joint_continuous U hU hc R hR hR0 haunit).2
  have hclosed := normalized_complex_kernels_restrict_closed U hU hcover R hR hR0 hraw haunit
  obtain ⟨η,hη,hzero⟩ := deflatedBarK_uniform_zero_free
  let ρ : ℝ := 1+η/2
  have hρ : 1<ρ := by dsimp [ρ];linarith
  have hρtop : ρ≤1+η := by dsimp [ρ];linarith
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) y₀
  let T : Set ℂ := Metric.closedBall 0 ρ
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hT : IsCompact T := isCompact_closedBall _ _
  have hTne : T.Nonempty := ⟨0,by simpa only [T,Metric.mem_closedBall,dist_self] using (zero_lt_one.trans hρ).le⟩
  have hSU : S⊆U := by rintro z ⟨Y,hY,rfl⟩;exact hcover Y hY
  have hzS : ∀ z∈S,∀ w∈T,complexDeflatedKernel R z w≠0 := by
    rintro z ⟨Y,hY,rfl⟩ w hw
    rw [complexDeflatedKernel_restrict_closed R (fun Y hY w => (hclosed Y hY w).1) Y hY w]
    exact hzero Y hY w ((show ‖w‖≤ρ by simpa only [T,Metric.mem_closedBall,dist_zero_right] using hw).trans hρtop)
  obtain ⟨V,hV,hSV,hVC,hVU,M,hM,hbound⟩ := compact_nonzero_parameter_uniform_bound U S T hU hS hT hTne hSU
    (complexDeflatedKernel R) (fun z w => regularizedKernel H R z w)
    (continuousAt_of_open_parameter_product U hU _ hD)
    (continuousAt_of_open_parameter_product U hU _ hH) hzS
  have hcoverV : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V := fun Y hY => hSV ⟨Y,hY,rfl⟩
  obtain ⟨Ω,hΩ,hΩconv,hΩcover,hΩV⟩ := exists_convex_physical_neighborhood V hV hcoverV
  have hΩC : closure Ω⊆closure V := closure_mono hΩV
  have hΩU : Ω⊆U := hΩV.trans (subset_closure.trans hVU)
  refine ⟨Ω,R,ρ,M,hΩ,hΩconv,hΩcover,hρ,hM,hR.mono hΩU,?_,hraw,hR0,hR'⟩
  intro z hz
  have hzV := hΩC hz
  refine ⟨haunit z (hVU hzV),(hunit z (hVU hzV)).2.2.2,?_⟩
  intro w hw
  exact hbound z hzV w (by simpa only [T,Metric.mem_closedBall,dist_zero_right] using hw)
end WP.Analysis
namespace WP.Analysis

lemma regularizedKernelCoeff_eq_coeff_off_critical (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (z : ℂ) (hz : z≠(y₀:ℂ)) (hunit : complexAUnit z≠0) (n : ℕ) :
    regularizedKernelCoeff B R n z=WP.coeff (fun w => regularizedKernel B R z w) n := by
  have he : (fun w => regularizedKernel B R z w)=(fun w => B z (R z*w)/deriv X z) :=
    funext (fun w => regularizedKernel_eq_raw_off_critical B R hB0 hR0 z w hz hunit)
  have hδ : z-(y₀:ℂ)≠0 := sub_ne_zero.mpr hz
  have ha : deriv X z≠0 := by rw [←complexAUnit_factor z];exact mul_ne_zero hδ hunit
  rw [he,coeff_scaled_div]
  by_cases hn : n=0
  · subst n
    simp only [regularizedKernelCoeff,ite_true,pow_zero,one_mul,WP.coeff,iteratedDeriv_zero,
      mul_zero,Nat.factorial_zero,Nat.cast_one,div_one,hB0,div_self ha]
  · exact regularizedKernelCoeff_scale B R n (by omega) hR0 z hz hunit

lemma normalized_complex_kernel_coefficients_identity (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hR0 : R (y₀:ℂ)=0) (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ z∈Ω,∀ n : ℕ,regularizedKernelCoeff K R n z=WP.coeff (fun w => regularizedKernel K R z w) n ∧
      regularizedKernelCoeff H R n z=WP.coeff (fun w => regularizedKernel H R z w) n := by
  have hcrit := (normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit)
  have hc : (y₀:ℂ)∈Ω := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  intro z hz n
  by_cases he : z=(y₀:ℂ)
  · subst z
    have hK (w : ℂ) := regularizedK_critical R hR0 hraw w
      (regularizedKernel_analyticOnNhd Ω hΩ hc K R (K_root_curve_analyticOnNhd Ω R hR) hunit w _ hc)
    have hH (w : ℂ) := regularizedH_critical R hR0 hraw w
      (regularizedKernel_analyticOnNhd Ω hΩ hc H R (H_root_curve_analyticOnNhd Ω R hR) hunit w _ hc)
    have hKfun : (fun w => regularizedKernel K R (y₀:ℂ) w)=barK y₀ := by
      funext w
      rw [hK w]
      simp only [barK,ite_true]
    have hHfun : (fun w => regularizedKernel H R (y₀:ℂ) w)=barH y₀ := by
      funext w
      rw [hH w]
      simp only [barH,ite_true]
    rw [hKfun,hHfun]
    exact (hcrit n).2.2 y₀ ⟨y₀_pos.le,le_rfl⟩
  · exact ⟨regularizedKernelCoeff_eq_coeff_off_critical K R K_zero hR0 z he (hunit z hz) n,
      regularizedKernelCoeff_eq_coeff_off_critical H R H_zero hR0 z he (hunit z hz) n⟩

lemma normalized_complex_kernel_zero_one (Ω : Set ℂ) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hR0 : R (y₀:ℂ)=0) (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ z∈Ω,regularizedKernel K R z 0=1 ∧ regularizedKernel K R z 1=0 := by
  have hc : (y₀:ℂ)∈Ω := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hK (w : ℂ) := regularizedKernel_analyticOnNhd Ω hΩ hc K R
    (K_root_curve_analyticOnNhd Ω R hR) hunit w
  have hr : y₀/2∈Ioo (0:ℝ) y₀ := ⟨half_pos y₀_pos,half_lt_self y₀_pos⟩
  have hreal (w : ℂ) (c : ℂ) (hphys : ∀ Y∈Ico (0:ℝ) y₀,barK Y w=c) :
      ∀ᶠ Y : ℝ in 𝓝 (y₀/2),regularizedKernel K R (Y:ℂ) w=c := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with Y hY
    rw [regularizedK_restrict_interior R hR0 hraw Y ⟨hY.1.le,hY.2⟩ w]
    exact hphys Y ⟨hY.1.le,hY.2⟩
  have h0 := complex_identity_of_real_germ _ (fun _ => 1) Ω (y₀/2) (hK 0) analyticOnNhd_const
    hconn (hcover _ ⟨hr.1.le,hr.2.le⟩) (hreal 0 1 (fun Y hY => barK_zero_closed Y ⟨hY.1,hY.2.le⟩))
  have h1 := complex_identity_of_real_germ _ (fun _ => 0) Ω (y₀/2) (hK 1) analyticOnNhd_const
    hconn (hcover _ ⟨hr.1.le,hr.2.le⟩) (hreal 1 0 (fun Y hY => barK_one_zero Y ⟨hY.1,hY.2.le⟩))
  exact fun z hz => ⟨h0 hz,h1 hz⟩

lemma complexDeflatedKernel_identity (R : ℂ → ℂ) (z : ℂ)
    (hf : Differentiable ℂ (fun w => regularizedKernel K R z w))
    (h1 : regularizedKernel K R z 1=0) (w : ℂ) :
    (1-w)*complexDeflatedKernel R z w=regularizedKernel K R z w := by
  have he := firstRootDeflation_eq_neg_dslope _ hf w
  change complexDeflatedKernel R z w=_ at he
  rw [he]
  have h := sub_smul_dslope (fun v => regularizedKernel K R z v) (1:ℂ) w
  simp only [smul_eq_mul,h1,sub_zero] at h
  linear_combination h

lemma deflated_inverse_taylor (f D : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hD : AnalyticAt ℂ D 0)
    (hf0 : f 0=1) (hidentity : ∀ w : ℂ,(1-w)*D w=f w) :
    taylor (fun w => (D w)⁻¹)=(PowerSeries.C 1-PowerSeries.X)*(taylor f)⁻¹ := by
  have hD0 : D 0=1 := by simpa only [sub_zero,one_mul,hf0] using hidentity 0
  have ht : (PowerSeries.C 1-PowerSeries.X)*taylor D=taylor f := by
    have hmul := taylor_mul (f:=fun w : ℂ => 1-w) (g:=D) (analyticAt_const.sub analyticAt_id) hD
    have hp : taylor (fun w : ℂ => 1-w)=PowerSeries.C 1-PowerSeries.X := by
      simpa only [taylor_const,taylor_id] using
        taylor_sub (f:=fun _ : ℂ => 1) (g:=fun w : ℂ => w) analyticAt_const analyticAt_id
    rw [hp] at hmul
    rw [←hmul]
    congr 1
    funext w
    exact hidentity w
  have hfc : PowerSeries.constantCoeff (taylor f)≠0 := by rw [taylor_constant,hf0];norm_num
  have hDc : PowerSeries.constantCoeff (taylor D)≠0 := by rw [taylor_constant,hD0];norm_num
  rw [taylor_inv hD (by rw [hD0];norm_num)]
  apply (PowerSeries.eq_mul_inv_iff_mul_eq hfc).mpr
  rw [←ht]
  calc
    (taylor D)⁻¹*((PowerSeries.C 1-PowerSeries.X)*taylor D)=
      (PowerSeries.C 1-PowerSeries.X)*((taylor D)⁻¹*taylor D) := by ring
    _ = _ := by rw [PowerSeries.inv_mul_cancel _ hDc,mul_one]
end WP.Analysis
namespace WP.Analysis
lemma complexWeightCoeff_eq_coeff_deflated_inverse (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (z : ℂ) (hz : z∈Ω) (n : ℕ) :
    complexWeightCoeff R n z=WP.coeff (fun w => (complexDeflatedKernel R z w)⁻¹) n := by
  have hc : (y₀:ℂ)∈Ω := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hFD := (normalized_complex_kernels_entire Ω hΩ hc R hR hR0 hraw hunit z hz).1
  have hDD := complexDeflatedKernel_entire Ω hΩ hc R hR hR0 hraw hunit z hz
  have h01 := normalized_complex_kernel_zero_one Ω hΩ hconn hcover R hR hR0 hraw hunit z hz
  have hs : complexKernelSeries R z=taylor (fun w => regularizedKernel K R z w) := by
    ext k
    simp only [complexKernelSeries,PowerSeries.coeff_mk,taylor_coeff]
    exact (normalized_complex_kernel_coefficients_identity Ω hΩ hcover R hR hR0 hraw hunit z hz k).1
  have ht := deflated_inverse_taylor _ _ (hFD.analyticAt 0) (hDD.analyticAt 0) h01.1
    (complexDeflatedKernel_identity R z hFD h01.2)
  rw [←hs] at ht
  have h := congrArg (fun p : PowerSeries ℂ => PowerSeries.coeff n p) ht
  rw [sub_mul] at h
  simp only [taylor_coeff,map_sub,PowerSeries.coeff_C_mul,one_mul] at h
  cases n with
  | zero => simpa only [complexWeightCoeff,ite_true,sub_zero,PowerSeries.coeff_zero_X_mul,
      complexThetaCoeff] using h.symm
  | succ n => simpa only [complexWeightCoeff,ite_false,Nat.succ_ne_zero,Nat.add_sub_cancel,
      PowerSeries.coeff_succ_X_mul,complexThetaCoeff] using h.symm

lemma complexWeightCoeff_norm_le_circle (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (ρ M : ℝ) (hρ : 0<ρ) (z : ℂ) (hz : z∈Ω)
    (hbound : ∀ w : ℂ,‖w‖≤ρ → complexDeflatedKernel R z w≠0 ∧ ‖(complexDeflatedKernel R z w)⁻¹‖≤M)
    (n : ℕ) : ‖complexWeightCoeff R n z‖≤M/ρ^n := by
  rw [complexWeightCoeff_eq_coeff_deflated_inverse Ω hΩ hconn hcover R hR hR0 hraw hunit z hz n]
  have hDD := complexDeflatedKernel_entire Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) R hR hR0 hraw hunit z hz
  apply coeff_norm_le_circle_bound _ ρ M hρ
  · intro w hw
    have hwρ : ‖w‖≤ρ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    exact ((hDD w).inv (hbound w hwρ).1).differentiableWithinAt
  · intro w hw
    exact (hbound w (le_of_eq (by simpa only [Metric.mem_sphere,dist_zero_right] using hw))).2

def complexDilatonCoefficient (R : ℂ → ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  if 1≤d then regularizedKernelCoeff H R (d-1) z/3 else 0

lemma complexDilatonCoefficient_norm_le_circle (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (ρ M : ℝ) (hρ : 0<ρ) (hM : 0≤M) (z : ℂ) (hz : z∈Ω)
    (hbound : ∀ w : ℂ,‖w‖≤ρ → ‖regularizedKernel H R z w‖≤M) (d : ℕ) :
    ‖complexDilatonCoefficient R d z‖≤(M*ρ)/ρ^d := by
  by_cases hd : 1≤d
  · have hHD := (normalized_complex_kernels_entire Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩)
        R hR hR0 hraw hunit z hz).2
    have hco := coeff_norm_le_circle_bound _ ρ M hρ hHD.differentiableOn
      (fun w hw => hbound w (le_of_eq (by simpa only [Metric.mem_sphere,dist_zero_right] using hw))) (d-1)
    have hid := (normalized_complex_kernel_coefficients_identity Ω hΩ hcover R hR hR0 hraw hunit z hz (d-1)).2
    have hpow : ρ^d=ρ^(d-1)*ρ := by rw [←pow_succ,Nat.sub_add_cancel hd]
    calc
      ‖complexDilatonCoefficient R d z‖ = ‖regularizedKernelCoeff H R (d-1) z‖/3 := by
        simp only [complexDilatonCoefficient,ite_eq_left hd,norm_div];norm_num
      _ ≤ ‖regularizedKernelCoeff H R (d-1) z‖ := by nlinarith [norm_nonneg (regularizedKernelCoeff H R (d-1) z)]
      _ ≤ M/ρ^(d-1) := by rw [hid];exact hco
      _ = (M*ρ)/ρ^d := by rw [hpow];field_simp
  · simp only [complexDilatonCoefficient,ite_eq_right hd,norm_zero]
    positivity

lemma complexThetaCoeff_prefix_weight (R : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    (∑ l∈Finset.range (n+1),complexWeightCoeff R l z)=complexThetaCoeff R n z := by
  induction n with
  | zero => simp [complexWeightCoeff]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [complexWeightCoeff,ite_false,Nat.succ_ne_zero,Nat.add_sub_cancel]
    ring

lemma complexThetaCoeff_norm_le_geometric (R : ℂ → ℂ) (z : ℂ) (ρ M : ℝ)
    (hρ : 1<ρ) (hM : 0≤M) (hbound : ∀ l : ℕ,‖complexWeightCoeff R l z‖≤M/ρ^l) (n : ℕ) :
    ‖complexThetaCoeff R n z‖≤M/(1-ρ⁻¹) := by
  have hρp : 0<ρ := zero_lt_one.trans hρ
  have hInv : ‖(ρ⁻¹:ℝ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρp)]
    exact (inv_lt_one₀ hρp).mpr hρ
  have hg := hasSum_geometric_of_norm_lt_one hInv
  rw [←complexThetaCoeff_prefix_weight R z n]
  calc
    _ ≤ ∑ l∈Finset.range (n+1),‖complexWeightCoeff R l z‖ := norm_sum_le _ _
    _ ≤ ∑ l∈Finset.range (n+1),M/ρ^l := Finset.sum_le_sum (fun l hl => hbound l)
    _ = M*∑ l∈Finset.range (n+1),(ρ⁻¹)^l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [inv_pow,div_eq_mul_inv]
    _ ≤ M*∑' l : ℕ,(ρ⁻¹)^l := mul_le_mul_of_nonneg_left
      (hg.summable.sum_le_tsum _ (fun l hl => pow_nonneg (inv_nonneg.mpr hρp.le) l)) hM
    _ = M/(1-ρ⁻¹) := by rw [hg.tsum_eq];rfl
end WP.Analysis
namespace WP.Analysis
lemma complexDilatonCoefficient_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hH : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω) (d : ℕ) :
    AnalyticOnNhd ℂ (complexDilatonCoefficient R d) Ω := by
  by_cases hd : 1≤d
  · have he : complexDilatonCoefficient R d=(fun z => regularizedKernelCoeff H R (d-1) z/3) := by
      funext z
      simp only [complexDilatonCoefficient,ite_eq_left hd]
    rw [he]
    exact fun z hz => (hH (d-1) z hz).div_const
  · have he : complexDilatonCoefficient R d=(fun _ : ℂ => 0) := by
      funext w
      simp only [complexDilatonCoefficient,ite_eq_right hd]
    rw [he]
    exact analyticOnNhd_const

lemma complexDilatonCoefficient_restrict_closed (R : ℂ → ℂ)
    (hH : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n)
    (d : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexDilatonCoefficient R d (Y:ℂ)=(canonicalDilatonCoefficient Y d:ℂ) := by
  by_cases hd : 1≤d
  · simp only [complexDilatonCoefficient,ite_eq_left hd]
    rw [hH (d-1) Y hY]
    have hr : WP.coeff (barH Y) (d-1)=((realCoeff (barH Y) (d-1):ℝ):ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using barH_realCoefficients Y (d-1)
    rw [hr]
    simp only [canonicalDilatonCoefficient,ite_eq_left hd,Complex.ofReal_div,Complex.ofReal_ofNat]
  · simp only [complexDilatonCoefficient,canonicalDilatonCoefficient,ite_eq_right hd,Complex.ofReal_zero]

lemma common_complex_geometric_kernel_bounds :
    ∃ (Ω : Set ℂ) (R : ℂ → ℂ) (ρ C : ℝ),IsOpen Ω ∧ Convex ℝ Ω ∧
      (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧ 1<ρ ∧ 0<C ∧ AnalyticOnNhd ℂ R Ω ∧
      (∀ z∈Ω,complexAUnit z≠0 ∧ complexDeflatedCoeff R 0 z≠0) ∧
      (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 ∧
      (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧
        AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexDilatonCoefficient R n) Ω) ∧
      (∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧
        complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ) ∧ complexDilatonCoefficient R n (Y:ℂ)=(canonicalDilatonCoefficient Y n:ℂ)) ∧
      (∀ z∈Ω,∀ n : ℕ,‖complexThetaCoeff R n z‖≤C ∧ ‖complexWeightCoeff R n z‖≤C/ρ^n ∧
        ‖complexDilatonCoefficient R n z‖≤C/ρ^n) ∧
      (∀ n : ℕ,complexThetaCoeff R n (y₀:ℂ)=1) := by
  obtain ⟨Ω,R,ρ,M,hΩ,hconv,hcover,hρ,hM,hR,hcircle,hraw,hR0,hR'⟩ := common_complex_kernel_circle_control
  have hρp : 0<ρ := zero_lt_one.trans hρ
  have hunit : ∀ z∈Ω,complexAUnit z≠0 := fun z hz => (hcircle z (subset_closure hz)).1
  have hcoeff := normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  have hθa := complexThetaCoeff_analyticOnNhd Ω R (fun n => (hcoeff n).1)
  have hwa := complexWeightCoeff_analyticOnNhd Ω R hθa
  have hHcoeff : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n :=
    fun n Y hY => ((hcoeff n).2.2 Y hY).2
  have hKcoeff : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n :=
    fun n Y hY => ((hcoeff n).2.2 Y hY).1
  let C : ℝ := max (M*ρ) (M/(1-ρ⁻¹))
  have hCMρ : M*ρ≤C := le_max_left _ _
  have hCMθ : M/(1-ρ⁻¹)≤C := le_max_right _ _
  have hCM : M≤C := (show M≤M*ρ by nlinarith).trans hCMρ
  have hCp : 0<C := lt_of_lt_of_le (mul_pos hM hρp) hCMρ
  refine ⟨Ω,R,ρ,C,hΩ,hconv,hcover,hρ,hCp,hR,?_,hraw,hR0,hR',?_,?_,?_,?_⟩
  · exact fun z hz => ⟨hunit z hz,(hcircle z (subset_closure hz)).2.1⟩
  · exact fun n => ⟨hθa n,hwa n,complexDilatonCoefficient_analyticOnNhd Ω R (fun n => (hcoeff n).2.1) n⟩
  · intro n Y hY
    exact ⟨complexThetaCoeff_restrict_closed R hKcoeff n Y hY,
      complexWeightCoeff_restrict_closed R hKcoeff n Y hY,complexDilatonCoefficient_restrict_closed R hHcoeff n Y hY⟩
  · intro z hz n
    have hw : ∀ l : ℕ,‖complexWeightCoeff R l z‖≤M/ρ^l :=
      complexWeightCoeff_norm_le_circle Ω hΩ hconv.isPreconnected hcover R hR hR0 hraw hunit ρ M hρp z hz
        (fun w hw => ⟨((hcircle z (subset_closure hz)).2.2 w hw).1,((hcircle z (subset_closure hz)).2.2 w hw).2.1⟩)
    have hb := complexDilatonCoefficient_norm_le_circle Ω hΩ hcover R hR hR0 hraw hunit ρ M hρp hM.le z hz
      (fun w hw => ((hcircle z (subset_closure hz)).2.2 w hw).2.2) n
    exact ⟨(complexThetaCoeff_norm_le_geometric R z ρ M hρ hM.le hw n).trans hCMθ,
      (hw n).trans (div_le_div_of_nonneg_right hCM (pow_nonneg hρp.le n)),
      hb.trans (div_le_div_of_nonneg_right hCMρ (pow_nonneg hρp.le n))⟩
  · intro n
    rw [complexThetaCoeff_restrict_closed R hKcoeff n y₀ ⟨y₀_pos.le,le_rfl⟩,critical_kernels.2 n]
    norm_num
end WP.Analysis
