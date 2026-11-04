import WPFormalization.Analysis.BesselSignBounds
import WPFormalization.Analysis.BesselZeros
import WPFormalization.Analysis.RealKernelRoot
import WPFormalization.Analysis.RealBessel
import WPFormalization.Analysis.BesselPositivity
import WPFormalization.Analysis.LogCoefficients
import WPFormalization.Analysis.ParameterSeries

/-! Entire integral kernels and their analytic identities, followed by positivity and lattice statements. -/
noncomputable section
namespace WP
open Filter Asymptotics
open scoped Topology

/- Eq.2.1, entire kernels defined by the displayed integrals. -/
/- Blueprint label(s): eq:P1
Paper v3: 2.1 [PDF 16]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P1"]
def K (Y : ℂ) (z : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, deriv X (Y + z / 2 * (1 - (s : ℂ)^2))
/- Blueprint label(s): eq:P1
Paper v3: 2.1 [PDF 16]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P1"]
def H (Y : ℂ) (z : ℂ) : ℂ :=
  3 * ∫ s : ℝ in (0)..1, (s : ℂ)^2 * deriv X (Y + z / 2 * (1 - (s : ℂ)^2))

lemma K_differentiable (Y : ℂ) : Differentiable ℂ (K Y) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have he : K Y = fun w => ∫ s : ℝ in (0)..1, (1 : ℂ)*deriv X (Y+w/2*(1-(s : ℂ)^2)) := by
    funext w
    simp only [K,one_mul]
  rw [he]
  exact fun z => (hasDerivAt_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg Y z).differentiableAt
lemma H_differentiable (Y : ℂ) : Differentiable ℂ (H Y) := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  intro z
  exact ((hasDerivAt_kernelIntegral (fun s : ℝ => (s : ℂ)^2)
    (by fun_prop) (deriv X) hg Y z).const_mul (3 : ℂ)).differentiableAt
lemma iteratedDeriv_K_zero (Y : ℂ) (n : ℕ) :
    iteratedDeriv n (K Y) 0 =
      (n.factorial : ℂ)/oddFactorial n*iteratedDeriv (n+1) X Y := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have h := iteratedDeriv_kernelIntegral (fun _ => 1) continuous_const (deriv X) hg n Y 0
  simp only [zero_div,zero_mul,add_zero,one_mul,← iteratedDeriv_succ'] at h
  change iteratedDeriv n (K Y) 0 = _ at h
  rw [h,intervalIntegral.integral_mul_const]
  change kernelMoment n * _ = _
  rw [kernelMoment_eval]
lemma iteratedDeriv_H_zero (Y : ℂ) (n : ℕ) :
    iteratedDeriv n (H Y) 0 =
      3*((n.factorial : ℂ)/oddFactorial (n+1))*iteratedDeriv (n+1) X Y := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have h := iteratedDeriv_kernelIntegral (fun s : ℝ => (s : ℂ)^2)
    (by fun_prop) (deriv X) hg n Y 0
  simp only [zero_div,zero_mul,add_zero,← iteratedDeriv_succ'] at h
  unfold H
  rw [iteratedDeriv_const_mul_field,h,intervalIntegral.integral_mul_const]
  change 3*(kernelSecondMoment n*_) = _
  rw [kernelSecondMoment_eval]
  ring
lemma K_zero (Y : ℂ) : K Y 0 = deriv X Y := by simp [K]
lemma H_zero (Y : ℂ) : H Y 0 = deriv X Y := by
  have h := iteratedDeriv_H_zero Y 0
  norm_num [oddFactorial,Finset.prod_range_succ] at h
  exact h
/- Eq.2.1 includes the integral/series equalities, not merely names for the kernels. -/
/- Blueprint label(s): eq:P1
Paper v3: 2.1 [PDF 16]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P1"]
theorem kernel_series (Y z : ℂ) :
    HasSum (fun l : ℕ => iteratedDeriv (l+1) X Y / oddFactorial l * z^l) (K Y z) ∧
    HasSum (fun l : ℕ => 3 * iteratedDeriv (l+1) X Y / oddFactorial (l+1) * z^l) (H Y z) := by
  constructor
  · convert Complex.hasSum_taylorSeries_of_entire (K_differentiable Y) 0 z using 1
    ext n
    simp only [sub_zero,smul_eq_mul,iteratedDeriv_K_zero]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    <;> ring
  · convert Complex.hasSum_taylorSeries_of_entire (H_differentiable Y) 0 z using 1
    ext n
    simp only [sub_zero,smul_eq_mul,iteratedDeriv_H_zero]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    <;> ring


/- Eq.2.2; no restriction of the complex variables. -/
/- Blueprint label(s): eq:P2
Paper v3: 2.2 [PDF 16]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P2"]
theorem kernel_differential (Y z : ℂ) :
    K Y z = H Y z + 2/3 * z * deriv (H Y) z := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hd := (hasDerivAt_kernelIntegral (fun s : ℝ => (s : ℂ)^2)
    (by fun_prop) (deriv X) hg Y z).const_mul (3 : ℂ)
  have heq : deriv (H Y) z = 3*(∫ s : ℝ in (0)..1,
      (s : ℂ)^2*(1-(s : ℂ)^2)/2*deriv (deriv X) (Y+z/2*(1-(s : ℂ)^2))) := by
    exact hd.deriv
  rw [heq]
  unfold K H
  rw [kernelIntegral_relation (deriv X) hg Y z]
  ring

/-- First positive kernel zero. Its existence and simplicity are stated below. -/
def r (Y : ℝ) : ℝ := sInf {z : ℝ | 0 < z ∧ K Y z = 0}

lemma r_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : 0 < r Y := by
  have hs : {z : ℝ | 0 < z ∧ K Y z = 0}.Nonempty := by
    obtain ⟨z,hz,hroot⟩ := Analysis.rootKernel_positive_zero Y hY.1
      (fun u hu => a_pos u ⟨hu.1,lt_of_le_of_lt hu.2 hY.2⟩)
    exact ⟨z,hz,hroot⟩
  have h0 : K (Y : ℂ) 0 ≠ 0 := by
    rw [K_zero,derivX_ofReal]
    exact_mod_cast a_ne_zero Y hY
  exact Analysis.positive_zero_sInf_pos (fun z : ℝ => K Y z)
    (((K_differentiable Y).continuous.comp Complex.continuous_ofReal).continuousAt) h0 hs

/- Logarithmic coefficients of Lemma 2.2. -/
/- Blueprint label(s): lem:kernel-positivity
Paper v3: 2.2 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:kernel-positivity"]
def logKernelCoeff (m : ℕ) (Y : ℂ) : ℂ :=
  coeff (fun z => Complex.log (deriv X Y / H Y z)) m

/- The initial logarithmic coefficients are positive by a formal Riccati argument,
without a Hadamard product or an unproved assertion about the zeros of H. -/
namespace Analysis
open PowerSeries
lemma coeff_H_zero_eq_bessel (n : ℕ) :
    WP.coeff (H 0) n = Complex.ofReal (normalizedBesselCoeff 5 2 n) := by
  rw [normalizedBesselCoeff_five_two]
  unfold WP.coeff
  rw [iteratedDeriv_H_zero,iteratedDeriv_X_succ_zero]
  push_cast
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  <;> ring
lemma taylor_H_zero_eq_bessel :
    taylor (H 0) = PowerSeries.map Complex.ofRealHom (normalizedBesselSeries 5 2) := by
  ext n
  simp only [taylor_coeff,coeff_map,normalizedBesselSeries,coeff_mk,Complex.ofRealHom_eq_coe]
  exact coeff_H_zero_eq_bessel n
lemma realCoeff_H_zero_logSlope_pos (n : ℕ) :
    0 < realCoeff (fun z => -deriv (H 0) z/H 0 z) n := by
  apply realCoeff_logSlope_pos_of_bessel (H 0) 5 2 (by norm_num) (by norm_num)
    ((H_differentiable 0).analyticAt 0) _ taylor_H_zero_eq_bessel n
  rw [H_zero,derivX_zero]
  exact one_ne_zero
lemma logKernelCoeff_zero_succ_pos (n : ℕ) :
    0 < (logKernelCoeff (n+1) 0).re := by
  let f := H (0 : ℂ)
  let T (z : ℂ) := Complex.log ((f z)⁻¹)
  have hf0 : f 0 = 1 := by simp only [f,H_zero,derivX_zero]
  have hfn : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hf : Differentiable ℂ f := H_differentiable 0
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), (f z)⁻¹ ∈ Complex.slitPlane :=
    (hf.continuous.continuousAt.inv₀ hfn).eventually
      (Complex.isOpen_slitPlane.mem_nhds (by simp [hf0]))
  have hderiv : deriv T =ᶠ[𝓝 (0 : ℂ)] (fun z => -deriv f z/f z) := by
    filter_upwards [hslit,hf.continuous.continuousAt.eventually_ne hfn] with z hz hzne
    have hd := (((hf z).hasDerivAt.inv hzne).clog hz).deriv
    change deriv (fun t : ℂ => Complex.log (f⁻¹ t)) z = (-deriv f z/f z)
    rw [hd]
    simp only [Pi.inv_apply]
    field_simp [hzne]
    <;> ring
  have hc : WP.coeff (deriv T) n = WP.coeff (fun z => -deriv f z/f z) n := by
    unfold WP.coeff
    rw [hderiv.iteratedDeriv_eq n]
  have hd := congrArg (fun p : PowerSeries ℂ => (PowerSeries.coeff n p).re)
    (taylor_deriv (f := T))
  simp only [taylor_coeff,coeff_derivative,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
    zero_add,mul_zero,sub_zero] at hd
  change realCoeff (deriv T) n = realCoeff T (n+1)*(n+1 : ℝ) at hd
  have hp : 0 < realCoeff (deriv T) n := by
    unfold realCoeff
    rw [hc]
    exact realCoeff_H_zero_logSlope_pos n
  rw [hd] at hp
  have htpos := (mul_pos_iff_of_pos_right (by positivity : (0 : ℝ)<n+1)).mp hp
  change 0 < (WP.coeff (fun z => Complex.log (deriv X 0/H 0 z)) (n+1)).re
  simpa only [derivX_zero,one_div,f,T,realCoeff] using htpos

lemma logKernelCoeff_zero_pos (m : ℕ) (hm : 0 < m) : 0 < (logKernelCoeff m 0).re := by
  cases m with
  | zero => omega
  | succ n => exact logKernelCoeff_zero_succ_pos n
lemma coeff_H_formula (Y : ℂ) (n : ℕ) :
    WP.coeff (H Y) n = 3*iteratedDeriv (n+1) X Y/(oddFactorial (n+1) : ℂ) := by
  unfold WP.coeff
  rw [iteratedDeriv_H_zero]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  <;> ring
lemma coeff_H_analyticAt (n : ℕ) (Y : ℂ) : AnalyticAt ℂ (fun W => WP.coeff (H W) n) Y := by
  have he : (fun W => WP.coeff (H W) n) =
      fun W => 3*iteratedDeriv (n+1) X W/(oddFactorial (n+1) : ℂ) := funext (fun W => coeff_H_formula W n)
  rw [he]
  exact (analyticAt_const.mul ((iteratedDeriv_X_differentiable (n+1)).analyticAt Y)).div_const
lemma logKernelCoeff_zero (Y : ℂ) (ha : deriv X Y ≠ 0) : logKernelCoeff 0 Y = 0 := by
  simp [logKernelCoeff,WP.coeff,H_zero,ha]
lemma logKernelCoeff_finite_recursion (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    logKernelCoeff (m+1) Y =
      (-(m+1 : ℂ)*WP.coeff (H Y) (m+1)-
        ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) /
          ((m+1 : ℂ)*deriv X Y) := by
  have h := logarithmic_coeff_identity (H Y) ((H_differentiable Y).analyticAt 0)
    (by rw [H_zero]; exact ha) m
  simp only [H_zero] at h
  change (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) = _ at h
  rw [Finset.sum_range_succ,Nat.sub_self] at h
  have h0 : WP.coeff (H Y) 0 = deriv X Y := by simp [WP.coeff,H_zero]
  rw [h0] at h
  have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  apply (eq_div_iff (mul_ne_zero hn ha)).2
  linear_combination h
lemma logKernelCoeff_analyticAt (m : ℕ) (Y : ℂ) (ha : deriv X Y ≠ 0) :
    AnalyticAt ℂ (logKernelCoeff m) Y := by
  induction m using Nat.strong_induction_on generalizing Y with
  | h m ih =>
    have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
      ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
    cases m with
    | zero =>
      apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [hane] with W hW
      exact (logKernelCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (-(m+1 : ℂ)*WP.coeff (H W) (m+1)-
          ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) W*WP.coeff (H W) (m-i)) /
            ((m+1 : ℂ)*deriv X W)
      have hs : AnalyticAt ℂ
          (fun W => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) W*WP.coeff (H W) (m-i)) Y := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        exact (analyticAt_const.mul (ih (i+1) (by omega) Y ha)).mul (coeff_H_analyticAt (m-i) Y)
      have hE : AnalyticAt ℂ E Y := by
        have hd : AnalyticAt ℂ (fun W => (m+1 : ℂ)*deriv X W) Y :=
          analyticAt_const.mul (X_differentiable.analyticAt Y).deriv
        have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        exact ((analyticAt_const.mul (coeff_H_analyticAt (m+1) Y)).sub hs).div hd (mul_ne_zero hn ha)
      apply hE.congr
      filter_upwards [hane] with W hW
      exact (logKernelCoeff_finite_recursion W hW m).symm

lemma deriv_coeff_H_parameter (Y : ℂ) (n : ℕ) :
    deriv (fun W => WP.coeff (H W) n) Y = (2*n+5 : ℂ)*WP.coeff (H Y) (n+1) := by
  have he : (fun W => WP.coeff (H W) n) =
      fun W => 3*iteratedDeriv (n+1) X W/(oddFactorial (n+1) : ℂ) := funext (fun W => coeff_H_formula W n)
  rw [he,deriv_div_const,deriv_const_mul_field,← iteratedDeriv_succ,coeff_H_formula,
    oddFactorial_succ (n+1)]
  push_cast
  have ho : (oddFactorial (n+1) : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero (n+1)
  have hn : (2*n+5 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*n+5 ≠ 0)
  ring_nf at ho hn ⊢
  field_simp [ho,hn]
  have hc : (5+(n : ℂ)*2)*(5+(n : ℂ)*2)⁻¹ = 1 := mul_inv_cancel₀ hn
  linear_combination -3*iteratedDeriv (2+n) X Y*hc
lemma kernel_parameter_series (Y : ℂ) :
    coefficientDeriv (fun W => taylor (H W)) Y =
      2*PowerSeries.derivative (taylor (H Y))+PowerSeries.C (3 : ℂ)*shiftSeries (taylor (H Y)) := by
  ext n
  simp only [coefficientDeriv_coeff,taylor_coeff,map_add,PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_derivative,PowerSeries.coeff_C_mul,shiftSeries_coeff]
  rw [deriv_coeff_H_parameter]
  push_cast
  ring
lemma kernel_log_parameter_deriv (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) (hm : 0 < m) :
    deriv (logKernelCoeff m) Y =
      2*(m+1 : ℂ)*logKernelCoeff (m+1) Y+
        3*deriv X Y*WP.coeff (fun z => (H Y z)⁻¹) (m+1) := by
  let F (W : ℂ) := taylor (H W)
  let T (W : ℂ) := taylor (fun z => Complex.log (deriv X W/H W z))
  have hF : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (F W)) Y := by
    intro n
    simpa only [F,taylor_coeff] using coeff_H_analyticAt n Y
  have hT : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (T W)) Y := by
    intro n
    have he : (fun W => PowerSeries.coeff n (T W)) = logKernelCoeff n := by
      funext W
      simp only [T,taylor_coeff,logKernelCoeff]
    rw [he]
    exact logKernelCoeff_analyticAt n Y ha
  have hF0 : PowerSeries.constantCoeff (F Y) ≠ 0 := by simpa [F,H_zero] using ha
  have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
  have hlog : (fun W => PowerSeries.derivative (T W)*F W) =ᶠ[𝓝 Y]
      (fun W => -PowerSeries.derivative (F W)) := by
    filter_upwards [hane] with W hW
    simpa only [F,T,H_zero] using
      logarithmic_taylor_identity (H W) ((H_differentiable W).analyticAt 0) (by rw [H_zero]; exact hW)
  have hT0 : ∀ᶠ W in 𝓝 Y, PowerSeries.constantCoeff (T W) = 0 := by
    filter_upwards [hane] with W hW
    simp [T,H_zero,hW]
  have hparam : coefficientDeriv F Y =
      2*PowerSeries.derivative (F Y)+PowerSeries.C (3 : ℂ)*shiftSeries (F Y) := kernel_parameter_series Y
  have hpde := coefficientDeriv_log_pde F T Y 3 hF hT hF0 hlog hT0 hparam
  have hc := congrArg (PowerSeries.coeff m) hpde
  dsimp only [F,T] at hc
  simp only [coefficientDeriv_coeff,taylor_coeff,map_add,PowerSeries.coeff_C,
    if_neg (ne_of_gt hm),zero_add,PowerSeries.coeff_ofNat_mul,PowerSeries.coeff_derivative,
    PowerSeries.coeff_C_mul,shiftSeries_coeff,taylor_constant,H_zero] at hc
  rw [← taylor_inv ((H_differentiable Y).analyticAt 0) (by rw [H_zero]; exact ha)] at hc
  simp only [taylor_coeff] at hc
  change deriv (logKernelCoeff m) Y =
    2*(logKernelCoeff (m+1) Y*(m+1 : ℂ))+3*(deriv X Y*WP.coeff (fun z => (H Y z)⁻¹) (m+1)) at hc
  linear_combination hc

end Analysis

lemma a_inverse_coeff_pos (n : ℕ) : 0 < realCoeff (fun Y => (deriv X Y)⁻¹) n :=
  Analysis.realCoeff_inv_derivX_pos n

/- Eq.2.5 with the continuous endpoint prescribed in Eq.4.2. -/
/- Blueprint label(s): eq:P9
Paper v3: 2.5 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P9"]
def barK (Y : ℝ) (w : ℂ) : ℂ :=
  if Y = y₀ then 1 - w else K Y ((r Y : ℂ) * w) / a Y
/- Blueprint label(s): eq:P9
Paper v3: 2.5 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P9"]
def barH (Y : ℝ) (w : ℂ) : ℂ :=
  if Y = y₀ then 1 - 3/5 * w else H Y ((r Y : ℂ) * w) / a Y
/- Blueprint label(s): eq:P9
Paper v3: 2.5 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P9"]
def A (Y : ℝ) : ℝ := (barH Y 1).re / 3
/- Blueprint label(s): eq:P11, eq:H2
Paper v3: 2.7 [PDF 17]; 4.1 [PDF 19]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P11", blueprint "eq:H2"]
def theta (Y : ℝ) (l : ℕ) : ℝ := realCoeff (fun w => (barK Y w)⁻¹) l
lemma barK_zero (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : barK Y 0 = 1 := by
  have ha : (a Y : ℂ) ≠ 0 := by exact_mod_cast a_ne_zero Y hY
  simp [barK, ne_of_lt hY.2, K_zero, derivX_ofReal, ha]
lemma barK_differentiable (Y : ℝ) : Differentiable ℂ (barK Y) := by
  by_cases h : Y = y₀
  · have he : barK Y = fun w => 1-w := by funext w; simp [barK,h]
    rw [he]
    fun_prop
  · have he : barK Y = fun w => K Y ((r Y : ℂ)*w)/(a Y : ℂ) := by
      funext w
      simp [barK,h]
    rw [he]
    exact ((K_differentiable Y).comp (by fun_prop : Differentiable ℂ (fun w => (r Y : ℂ)*w))).div_const _
lemma theta_one (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    theta Y 1 = -(iteratedDeriv 2 X Y).re*r Y/(3*a Y) := by
  have he : barK Y = fun w => K Y ((r Y : ℂ)*w)/(a Y : ℂ) := by
    funext w
    simp [barK,ne_of_lt hY.2]
  have hd : deriv (barK Y) 0 = (r Y : ℂ)*iteratedDeriv 2 X Y/(3*a Y) := by
    rw [he,deriv_div_const,deriv_comp_mul_left,mul_zero]
    have h := iteratedDeriv_K_zero (Y : ℂ) 1
    norm_num [oddFactorial,Finset.prod_range_succ] at h
    rw [h]
    ring
  have hi : deriv (fun w => (barK Y w)⁻¹) 0 = -(r Y : ℂ)*iteratedDeriv 2 X Y/(3*a Y) := by
    change deriv (barK Y)⁻¹ 0 = _
    rw [deriv_inv'' ((barK_differentiable Y) 0) (by rw [barK_zero Y hY]; exact one_ne_zero),
      hd,barK_zero Y hY]
    ring
  unfold theta realCoeff coeff
  rw [iteratedDeriv_one,hi]
  norm_num [Complex.div_re]
  have ha := a_ne_zero Y hY
  field_simp [ha]
  <;> ring

/- Blueprint label(s): eq:P11
Paper v3: 2.7 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P11"]
def weight (Y : ℝ) (l : ℕ) : ℝ := theta Y l - if l = 0 then 0 else theta Y (l-1)

/- Eqs.4.1--4.2, including the nondefinitional differential identity and endpoint coefficients. -/
/- Blueprint label(s): eq:H2
Paper v3: 4.1 [PDF 19]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H2"]
theorem normalized_kernel_identity (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (z : ℂ) :
    barK Y z = barH Y z + 2/3*z*deriv (barH Y) z := by
  by_cases h : Y = y₀
  · subst Y
    have he : barH y₀ = fun w => 1-(3/5 : ℂ)*w := by funext w; simp [barH]
    rw [he]
    simp only [barK, ite_true]
    have hd : deriv (fun w : ℂ => 1-3/5*w) z = -(3/5 : ℂ) := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id z).const_mul (3/5 : ℂ)).const_sub 1).deriv
    rw [hd]
    ring
  · have he : barH Y = fun w => H Y ((r Y : ℂ)*w)/(a Y : ℂ) := by
      funext w
      simp [barH,h]
    rw [he]
    simp only [barK, ite_eq_right h]
    rw [deriv_div_const, deriv_comp_mul_left]
    rw [kernel_differential]
    ring

/- Blueprint label(s): eq:H3
Paper v3: 4.2 [PDF 19]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H3"]
theorem critical_kernels :
    (∀ w, barK y₀ w = 1 - w ∧ barH y₀ w = 1 - 3/5*w) ∧
    (∀ l, theta y₀ l = 1) := by
  constructor
  · intro w
    simp [barK, barH]
  · intro l
    unfold theta realCoeff coeff
    simp only [barK, ite_true]
    rw [iteratedDeriv_comp_const_sub]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_inv', smul_eq_mul,
      sub_zero, one_zpow, mul_one]
    have hf : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
    have hn : (-1 : ℂ)^l * ((-1 : ℂ)^l*l.factorial) = l.factorial := by
      rw [← mul_assoc, ← mul_pow]
      simp
    rw [hn, div_self hf]
    simp

/- Eq.2.8, probability generating function; probability assertions are separate. -/
/- Blueprint label(s): eq:P12
Paper v3: 2.8 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P12"]
def harmonicPGF (Y : ℝ) (w : ℂ) : ℂ := barH Y 1 / barH Y w
/- Blueprint label(s): eq:P12
Paper v3: 2.8 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P12"]
def harmonicMass (Y : ℝ) (m : ℕ) : ℝ := realCoeff (harmonicPGF Y) m
/- Blueprint label(s): eq:P12
Paper v3: 2.8 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:P12"]
def harmonicVariance (Y : ℝ) : ℝ :=
  ∑' m : ℕ, ((m : ℝ)-3/2)^2 * harmonicMass Y m
def harmonicSumMass (Y : ℝ) (h m : ℕ) : ℝ :=
  realCoeff (fun w => harmonicPGF Y w ^ h) m

/- The local logarithmic series in Eq.2.3, as an actual convergent sum. -/
/- Blueprint label(s): lem:kernel-positivity
Paper v3: 2.2 [PDF 17]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:kernel-positivity"]
theorem log_kernel_series (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z‖ < ρ →
      HasSum (fun m : ℕ => logKernelCoeff (m+1) Y*z^(m+1))
        (Complex.log ((a Y : ℂ)/H Y z)) := by
  have hne : deriv X (Y : ℂ) ≠ 0 := by
    rw [derivX_ofReal]
    exact_mod_cast a_ne_zero Y hY
  let f (z : ℂ) := Complex.log (deriv X Y / H Y z)
  have hf : AnalyticAt ℂ f 0 := by
    apply (analyticAt_const.div ((H_differentiable (Y : ℂ)).analyticAt 0)
      (by rw [H_zero]; exact hne)).clog
    simp [H_zero,hne]
  have hdiff := Complex.analyticAt_iff_eventually_differentiableAt.mp hf
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hdiff
  refine ⟨ρ,hρ,?_⟩
  intro z hz
  have hdon : DifferentiableOn ℂ f (Metric.ball 0 ρ) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    exact hball (by simpa using hw)
  have hs := Complex.hasSum_taylorSeries_on_ball hdon (by simpa using hz)
  have htail := (hasSum_nat_add_iff' 1).mpr hs
  have hfzero : f 0 = 0 := by simp [f,H_zero,hne]
  simp only [Finset.sum_range_one,sub_zero,pow_zero,one_smul,iteratedDeriv_zero,
    Nat.factorial_zero,Nat.cast_one,inv_one,hfzero,sub_zero] at htail
  convert htail using 1
  · ext m
    dsimp only [f]
    unfold logKernelCoeff coeff
    simp only [sub_zero,smul_eq_mul]
    ring
  · simp only [f,derivX_ofReal]

end WP
