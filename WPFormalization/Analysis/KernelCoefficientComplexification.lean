import WPFormalization.Analysis.NormalizedComplexExtension
import WPFormalization.Analysis.KKernelPositivity

/-! Every actual normalized kernel w-coefficient has a holomorphic parameter
extension on the same open neighborhood. The explicit removable R^n/a
factor retains the original WP.coeff values on the entire physical interval,
including the critical endpoint. This concerns w-coefficients, not the
paper's inverse-complexity expansion coefficients. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

def regularizedKernelCoeff (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  if n=0 then 1 else (z-(y₀:ℂ))^(n-1)*(dslope R (y₀:ℂ) z)^n*WP.coeff (B z) n/complexAUnit z

lemma regularizedKernelCoeff_analyticOnNhd (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : (y₀:ℂ) ∈ Ω) (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB : ∀ n : ℕ,AnalyticOnNhd ℂ (fun z => WP.coeff (B z) n) Ω)
    (hR : AnalyticOnNhd ℂ R Ω) (hunit : ∀ z ∈ Ω,complexAUnit z≠0) (n : ℕ) :
    AnalyticOnNhd ℂ (regularizedKernelCoeff B R n) Ω := by
  by_cases hn : n=0
  · subst n
    have he : regularizedKernelCoeff B R 0=(fun _ : ℂ => 1) := by funext z;simp [regularizedKernelCoeff]
    rw [he]
    exact analyticOnNhd_const
  · have he : regularizedKernelCoeff B R n=(fun z : ℂ =>
        (z-(y₀:ℂ))^(n-1)*(dslope R (y₀:ℂ) z)^n*WP.coeff (B z) n/complexAUnit z) := by
      funext z
      simp only [regularizedKernelCoeff,ite_eq_right hn]
    rw [he]
    intro z hz
    exact ((((analyticAt_id.sub analyticAt_const).pow (n-1)).mul
      ((dslope_analyticOnNhd_complex Ω hΩ R hR y₀ hc z hz).pow n)).mul (hB n z hz)).div
        (complexAUnit_analytic z (mem_univ _)) (hunit z hz)

lemma coeff_scaled_div (f : ℂ → ℂ) (c a : ℂ) (n : ℕ) :
    WP.coeff (fun w => f (c*w)/a) n=c^n*WP.coeff f n/a := by
  unfold WP.coeff
  rw [iteratedDeriv_div_const,iteratedDeriv_comp_mul_left,mul_zero]
  ring

lemma regularizedKernelCoeff_scale (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hR0 : R (y₀:ℂ)=0) (z : ℂ) (hz : z≠(y₀:ℂ)) (hunit : complexAUnit z≠0) :
    regularizedKernelCoeff B R n z=R z^n*WP.coeff (B z) n/deriv X z := by
  have hRf := sub_smul_dslope R (y₀:ℂ) z
  simp only [smul_eq_mul,hR0,sub_zero] at hRf
  have hAf := complexAUnit_factor z
  have hδ : z-(y₀:ℂ)≠0 := sub_ne_zero.mpr hz
  have hpow : (z-(y₀:ℂ))^n=(z-(y₀:ℂ))^(n-1)*(z-(y₀:ℂ)) := by
    rw [←pow_succ,Nat.sub_add_cancel hn]
  unfold regularizedKernelCoeff
  rw [ite_eq_right (by omega : n≠0),←hRf,←hAf,mul_pow,hpow]
  field_simp [hδ,hunit] <;> ring

lemma regularizedKernelCoeff_restrict_scaled (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (hR : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) (n : ℕ) :
    regularizedKernelCoeff B R n (Y:ℂ)=WP.coeff (fun w => B (Y:ℂ) ((r Y:ℂ)*w)/(a Y:ℂ)) n := by
  by_cases hn : n=0
  · subst n
    have ha : (a Y:ℂ)≠0 := by exact_mod_cast (a_pos Y hY).ne'
    simp only [regularizedKernelCoeff,ite_true,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,
      div_one,mul_zero,hB0,derivX_ofReal,div_self ha]
  · rw [regularizedKernelCoeff_scale B R n (by omega) hR0 (Y:ℂ)
      (by exact_mod_cast (ne_of_lt hY.2)) (complexAUnit_ne_zero_physical Y ⟨hY.1,hY.2.le⟩),
      coeff_scaled_div,hR Y hY,derivX_ofReal]

lemma physical_kernel_coeff_continuous (N : ℝ → ℂ → ℂ)
    (hN : ∀ Y ∈ Icc (0:ℝ) y₀,Differentiable ℂ (N Y))
    (hjoint : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => N (p.1:ℝ) p.2)) (n : ℕ) :
    ContinuousOn (fun Y => WP.coeff (N Y) n) (Icc (0:ℝ) y₀) := by
  apply continuousOn_iff_continuous_restrict.mpr
  exact parameter_coeff_continuous (fun Y : Icc (0:ℝ) y₀ => N (Y:ℝ)) 1 (by norm_num)
    (fun Y => (hN Y Y.property).differentiableOn)
    (hjoint.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) n

lemma regularizedKernelCoeff_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) (B : ℂ → ℂ → ℂ) (N : ℝ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB : ∀ n : ℕ,AnalyticOnNhd ℂ (fun z => WP.coeff (B z) n) Ω)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z ∈ Ω,complexAUnit z≠0)
    (hN : ∀ Y ∈ Icc (0:ℝ) y₀,Differentiable ℂ (N Y))
    (hjoint : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => N (p.1:ℝ) p.2))
    (hnormal : ∀ Y ∈ Ico (0:ℝ) y₀,N Y=(fun w => B (Y:ℂ) ((r Y:ℂ)*w)/(a Y:ℂ)))
    (n : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    regularizedKernelCoeff B R n (Y:ℂ)=WP.coeff (N Y) n := by
  have ha := regularizedKernelCoeff_analyticOnNhd Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) B R hB hR hunit n
  have hc : ContinuousOn (fun Y : ℝ => regularizedKernelCoeff B R n (Y:ℂ)) (Icc (0:ℝ) y₀) :=
    fun Y hY => ((ha _ (hcover Y hY)).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have he : EqOn (fun Y : ℝ => regularizedKernelCoeff B R n (Y:ℂ)) (fun Y => WP.coeff (N Y) n) (Ico (0:ℝ) y₀) := by
    intro Y hY
    dsimp only
    rw [hnormal Y hY]
    exact regularizedKernelCoeff_restrict_scaled B R hB0 hR0 hraw Y hY n
  exact he.of_subset_closure hc (physical_kernel_coeff_continuous N hN hjoint n) Ico_subset_Icc_self
    (by rw [closure_Ico y₀_pos.ne]) hY

lemma normalized_coefficients_holomorphic_on_common_domain (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z ∈ Ω,complexAUnit z≠0) :
    ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω ∧
      AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω ∧
      ∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n ∧
        regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n := by
  have hKcoeff (n : ℕ) : AnalyticOnNhd ℂ (fun z => WP.coeff (K z) n) Ω := fun z hz => coeff_K_analyticAt n z
  have hHcoeff (n : ℕ) : AnalyticOnNhd ℂ (fun z => WP.coeff (H z) n) Ω := fun z hz => coeff_H_analyticAt n z
  intro n
  refine ⟨regularizedKernelCoeff_analyticOnNhd Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) K R hKcoeff hR hunit n,
    regularizedKernelCoeff_analyticOnNhd Ω hΩ (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) H R hHcoeff hR hunit n,?_⟩
  intro Y hY
  constructor
  · apply regularizedKernelCoeff_restrict_closed Ω hΩ hcover K barK R hKcoeff K_zero hR hR0 hraw hunit
      (fun Y _ => barK_differentiable Y) barK_joint_continuous _ n Y hY
    intro Y hY
    funext w
    simp only [barK,ite_eq_right (ne_of_lt hY.2)]
  · apply regularizedKernelCoeff_restrict_closed Ω hΩ hcover H barH R hHcoeff H_zero hR hR0 hraw hunit
      (fun Y _ => barH_differentiable Y) barH_joint_continuous _ n Y hY
    intro Y hY
    funext w
    simp only [barH,ite_eq_right (ne_of_lt hY.2)]

lemma common_holomorphic_kernel_coefficients :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ w : ℂ,AnalyticOnNhd ℂ (fun z => regularizedKernel K R z w) Ω ∧
          AnalyticOnNhd ℂ (fun z => regularizedKernel H R z w) Ω) ∧
        (∀ Y ∈ Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ) ∧
          ∀ w : ℂ,regularizedKernel K R (Y:ℂ) w=barK Y w ∧ regularizedKernel H R (Y:ℂ) w=barH Y w) ∧
        (∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω ∧
          AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω ∧
          ∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n ∧
            regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n) ∧
        (∀ z ∈ Ω,complexAUnit z≠0) ∧
        (∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_normalized_kernel_data
  refine ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,?_,hunit,hraw,hR0,hR'⟩
  exact normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit

end WP.Analysis
