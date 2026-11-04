import WPFormalization.Analysis.KernelCoefficientComplexification

/-! The canonical inverse kernel coefficients extend on that same parameter
neighborhood. Mathlib formal inversion gives a finite recurrence; strong
induction proves holomorphy. The actual inverse Taylor series proves the
restriction identity with theta_l, hence also weight_l. Finite cutoff
weighted moments are included explicitly as partial moments; no infinite
moment analyticity or Appendix C algorithm compatibility is asserted. -/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

def complexKernelSeries (R : ℂ → ℂ) (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => regularizedKernelCoeff K R n z)

def complexThetaCoeff (R : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  PowerSeries.coeff n ((complexKernelSeries R z)⁻¹)

lemma complexKernelSeries_constant (R : ℂ → ℂ) (z : ℂ) :
    PowerSeries.constantCoeff (complexKernelSeries R z)=1 := by
  simp only [complexKernelSeries,PowerSeries.constantCoeff_mk,regularizedKernelCoeff,ite_true]

lemma complexThetaCoeff_recursion (R : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    complexThetaCoeff R n z = if n=0 then 1 else
      -∑ i ∈ Finset.HasAntidiagonal.antidiagonal n,if i.2<n then
        regularizedKernelCoeff K R i.1 z*complexThetaCoeff R i.2 z else 0 := by
  rw [complexThetaCoeff,PowerSeries.coeff_inv,complexKernelSeries_constant]
  simp only [inv_one,neg_one_mul,complexKernelSeries,PowerSeries.coeff_mk,complexThetaCoeff]

lemma complexThetaCoeff_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω) :
    ∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      have he : complexThetaCoeff R 0=(fun _ : ℂ => 1) := by
        funext z
        simpa only [ite_true] using complexThetaCoeff_recursion R 0 z
      rw [he]
      exact analyticOnNhd_const
    · have he : complexThetaCoeff R n=(fun z : ℂ =>
          -∑ i ∈ Finset.HasAntidiagonal.antidiagonal n,if i.2<n then
            regularizedKernelCoeff K R i.1 z*complexThetaCoeff R i.2 z else 0) := by
        funext z
        simpa only [ite_eq_right hn] using complexThetaCoeff_recursion R n z
      rw [he]
      intro z hz
      apply AnalyticAt.neg
      apply Finset.analyticAt_fun_sum
      intro i hi
      by_cases hlt : i.2<n
      · simp only [ite_eq_left hlt]
        exact (hK i.1 z hz).mul (ih i.2 hlt z hz)
      · simp only [ite_eq_right hlt]
        exact analyticAt_const

lemma complexThetaCoeff_restrict_closed (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (n : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) := by
  have he : complexKernelSeries R (Y:ℂ)=taylor (barK Y) := by
    ext m
    simp only [complexKernelSeries,PowerSeries.coeff_mk,taylor_coeff]
    exact hK m Y hY
  have hb : AnalyticAt ℂ (barK Y) 0 := (barK_differentiable Y).analyticAt 0
  have h0 : barK Y 0≠0 := by rw [barK_zero_closed Y hY];exact one_ne_zero
  rw [complexThetaCoeff,he,←taylor_inv hb h0,taylor_coeff]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using realCoefficients_inv hb h0 (barK_realCoefficients Y) n

def complexWeightCoeff (R : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  complexThetaCoeff R n z-if n=0 then 0 else complexThetaCoeff R (n-1) z

lemma complexWeightCoeff_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hθ : ∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω) (n : ℕ) :
    AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω := by
  intro z hz
  change AnalyticAt ℂ (fun ζ => complexThetaCoeff R n ζ-if n=0 then 0 else complexThetaCoeff R (n-1) ζ) z
  by_cases hn : n=0
  · simpa only [ite_eq_left hn,Pi.sub_def] using (hθ n z hz).sub (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) z)
  · simpa only [ite_eq_right hn,Pi.sub_def] using (hθ n z hz).sub (hθ (n-1) z hz)

lemma complexWeightCoeff_restrict_closed (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (n : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ) := by
  unfold complexWeightCoeff
  rw [complexThetaCoeff_restrict_closed R hK n Y hY]
  by_cases hn : n=0
  · simp only [ite_eq_left hn,weight,Complex.ofReal_sub,Complex.ofReal_zero]
  · rw [ite_eq_right hn,complexThetaCoeff_restrict_closed R hK (n-1) Y hY]
    simp only [weight,ite_eq_right hn,Complex.ofReal_sub]

def complexWeightPartialMoment (R : ℂ → ℂ) (N j : ℕ) (z : ℂ) : ℂ :=
  ∑ l ∈ Finset.range N,(l:ℂ)^j*complexWeightCoeff R l z

lemma complexWeightPartialMoment_analyticOnNhd (Ω : Set ℂ) (R : ℂ → ℂ)
    (hw : ∀ n : ℕ,AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω) (N j : ℕ) :
    AnalyticOnNhd ℂ (complexWeightPartialMoment R N j) Ω := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro l hl
  exact analyticAt_const.mul (hw l z hz)

lemma complexWeightPartialMoment_restrict_closed (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (N j : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    complexWeightPartialMoment R N j (Y:ℂ)=(((∑ l ∈ Finset.range N,(l:ℝ)^j*weight Y l):ℝ):ℂ) := by
  unfold complexWeightPartialMoment
  push_cast
  apply Finset.sum_congr rfl
  intro l hl
  rw [complexWeightCoeff_restrict_closed R hK l Y hY]

lemma common_holomorphic_kernel_inverse_coefficients :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y ∈ Icc (0:ℝ) y₀,(Y:ℂ) ∈ Ω) ∧
      ∃ R Q Ahat : ℂ → ℂ,AnalyticOnNhd ℂ R Ω ∧ AnalyticOnNhd ℂ Q Ω ∧ AnalyticOnNhd ℂ Ahat Ω ∧
        (∀ w : ℂ,AnalyticOnNhd ℂ (fun z => regularizedKernel K R z w) Ω ∧
          AnalyticOnNhd ℂ (fun z => regularizedKernel H R z w) Ω) ∧
        (∀ Y ∈ Icc (0:ℝ) y₀,Q (Y:ℂ)=(((∑'l : ℕ,weight Y l):ℝ):ℂ) ∧ Ahat (Y:ℂ)=(A Y:ℂ) ∧
          ∀ w : ℂ,regularizedKernel K R (Y:ℂ) w=barK Y w ∧ regularizedKernel H R (Y:ℂ) w=barH Y w) ∧
        (∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω ∧
          AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω ∧
          AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧
          ∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n ∧
            regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n ∧
            complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧ complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ)) ∧
        (∀ z ∈ Ω,complexAUnit z≠0) ∧
        (∀ Y ∈ Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 := by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_kernel_coefficients
  have hθ := complexThetaCoeff_analyticOnNhd Ω R (fun n => (hcoeff n).1)
  have hw := complexWeightCoeff_analyticOnNhd Ω R hθ
  have hclosed : ∀ n : ℕ,∀ Y ∈ Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n :=
    fun n Y hY => ((hcoeff n).2.2 Y hY).1
  refine ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,?_,hunit,hraw,hR0,hR'⟩
  intro n
  refine ⟨(hcoeff n).1,(hcoeff n).2.1,hθ n,hw n,?_⟩
  intro Y hY
  exact ⟨((hcoeff n).2.2 Y hY).1,((hcoeff n).2.2 Y hY).2,
    complexThetaCoeff_restrict_closed R hclosed n Y hY,complexWeightCoeff_restrict_closed R hclosed n Y hY⟩

end WP.Analysis
