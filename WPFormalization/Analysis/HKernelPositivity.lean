import WPFormalization.Analysis.PositiveSeriesODE
import WPFormalization.Analysis.BesselZeros
import WPFormalization.Statements.Kernels
import WPFormalization.Analysis.TaylorReality
import WPFormalization.Analysis.PositiveParameter
/-! Parameter reality and exact positive recurrences for the H-kernel.
These proofs use the actual integral kernel and its established coefficient identities. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma realCoefficients_real_const (c : ℝ) : RealCoefficients (fun _ : ℂ => (c : ℂ)) := by
  intro q
  cases q with
  | zero => simp [WP.coeff]
  | succ q => simp [WP.coeff,iteratedDeriv_const]
lemma realCoefficients_congr {f g : ℂ → ℂ} (hr : RealCoefficients f) (he : f =ᶠ[𝓝 0] g) :
    RealCoefficients g := by
  intro q
  unfold WP.coeff
  rw [← he.iteratedDeriv_eq q]
  exact hr q
lemma realCoefficients_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (hr : ∀ i ∈ s, RealCoefficients (f i)) :
    RealCoefficients (fun Y => ∑ i ∈ s, f i Y) := by
  intro q
  unfold WP.coeff
  rw [iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.sum_div]
  change Complex.imCLM (∑ i ∈ s, iteratedDeriv q (f i) 0/(q.factorial : ℂ)) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hr i hi q)
lemma realCoefficients_iteratedDeriv_X (n : ℕ) : RealCoefficients (iteratedDeriv n X) := by
  induction n with
  | zero =>
    intro q
    unfold WP.coeff
    have him : (iteratedDeriv q X (0 : ℂ)).im = 0 := by simpa using iteratedDeriv_X_im_ofReal q 0
    simp [Complex.div_im,him]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact realCoefficients_deriv ih
lemma coeff_H_parameter_real (n : ℕ) : RealCoefficients (fun Y => WP.coeff (H Y) n) := by
  have he : (fun Y => WP.coeff (H Y) n) =
      fun Y => (Complex.ofReal (3/(oddFactorial (n+1) : ℝ)))*iteratedDeriv (n+1) X Y := by
    funext Y
    rw [coeff_H_formula]
    push_cast
    ring
  rw [he]
  exact realCoefficients_const_mul _ (realCoefficients_iteratedDeriv_X (n+1))
lemma logKernelCoeff_parameter_real (m : ℕ) : RealCoefficients (logKernelCoeff m) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have hane : ∀ᶠ Y in 𝓝 (0 : ℂ), deriv X Y ≠ 0 :=
    ((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply realCoefficients_congr (realCoefficients_real_const 0)
      filter_upwards [hane] with Y hY
      exact (logKernelCoeff_zero Y hY).symm
    | succ m =>
      let E (Y : ℂ) :=
        (-(m+1 : ℂ)*WP.coeff (H Y) (m+1)-
          ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) /
            ((m+1 : ℂ)*deriv X Y)
      have hsA : AnalyticAt ℂ
          (fun Y => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) 0 := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) 0 ha)).mul (coeff_H_analyticAt (m-i) 0)
      have hsR : RealCoefficients
          (fun Y => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) := by
        apply realCoefficients_finset_sum
        · intro i hi
          exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) 0 ha)).mul (coeff_H_analyticAt (m-i) 0)
        · intro i hi
          have hi' : i < m := Finset.mem_range.mp hi
          have hmul := realCoefficients_mul (logKernelCoeff_analyticAt (i+1) 0 ha)
            (coeff_H_analyticAt (m-i) 0) (ih (i+1) (by omega)) (coeff_H_parameter_real (m-i))
          have hscalar := realCoefficients_const_mul (i+1 : ℝ) hmul
          push_cast at hscalar
          simpa only [mul_assoc] using hscalar
      have hnumR : RealCoefficients
          (fun Y => -(m+1 : ℂ)*WP.coeff (H Y) (m+1)-
            ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKernelCoeff (i+1) Y*WP.coeff (H Y) (m-i)) := by
        apply realCoefficients_sub (analyticAt_const.mul (coeff_H_analyticAt (m+1) 0)) hsA _ hsR
        have hscalar := realCoefficients_const_mul (-(m+1 : ℝ)) (coeff_H_parameter_real (m+1))
        push_cast at hscalar
        exact hscalar
      have hdenR : RealCoefficients (fun Y => (m+1 : ℂ)*deriv X Y) := by
        have hscalar := realCoefficients_const_mul (m+1 : ℝ) (realCoefficients_iteratedDeriv_X 1)
        simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,iteratedDeriv_one] using hscalar
      have hER : RealCoefficients E := by
        apply realCoefficients_div (g := fun Y => (m+1 : ℂ)*deriv X Y) ((analyticAt_const.mul (coeff_H_analyticAt (m+1) 0)).sub hsA)
          (analyticAt_const.mul (X_differentiable.analyticAt 0).deriv) _ hnumR hdenR
        have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        exact mul_ne_zero hn ha
      apply realCoefficients_congr hER
      filter_upwards [hane] with Y hY
      exact (logKernelCoeff_finite_recursion Y hY m).symm

lemma normalized_inverse_taylor_differential (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (ha : f 0 ≠ 0) :
    PowerSeries.derivative (PowerSeries.C (f 0)*(taylor f)⁻¹) =
      PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z)))*
        (PowerSeries.C (f 0)*(taylor f)⁻¹) := by
  have hp := logarithmic_taylor_identity f hf ha
  have hF0 : PowerSeries.constantCoeff (taylor f) ≠ 0 := by simpa using ha
  have ht : PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z))) =
      -PowerSeries.derivative (taylor f)*(taylor f)⁻¹ := by
    calc
      _ = (PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z)))*taylor f)*(taylor f)⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel _ hF0,mul_one]
      _ = _ := by rw [hp]
  rw [ht]
  simp only [Derivation.leibniz,PowerSeries.derivative_C,PowerSeries.derivative_inv',
    smul_eq_mul,mul_zero,zero_add]
  ring
def hInverseCoeff (m : ℕ) (Y : ℂ) : ℂ :=
  deriv X Y*WP.coeff (fun z => (H Y z)⁻¹) m
lemma hInverseCoeff_zero (Y : ℂ) (ha : deriv X Y ≠ 0) : hInverseCoeff 0 Y = 1 := by
  simp [hInverseCoeff,WP.coeff,H_zero,ha]
lemma hInverseCoeff_series (Y : ℂ) (ha : deriv X Y ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.C (deriv X Y)*(taylor (H Y))⁻¹) = hInverseCoeff n Y := by
  rw [PowerSeries.coeff_C_mul,← taylor_inv ((H_differentiable Y).analyticAt 0) (by rw [H_zero]; exact ha),taylor_coeff]
  rfl
lemma hInverseCoeff_recursion (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    (m+1 : ℂ)*hInverseCoeff (m+1) Y =
      ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y := by
  have hp := normalized_inverse_taylor_differential (H Y) ((H_differentiable Y).analyticAt 0)
    (by rw [H_zero]; exact ha)
  simp only [H_zero] at hp
  have hc := congrArg (PowerSeries.coeff m) hp
  rw [PowerSeries.coeff_derivative,hInverseCoeff_series Y ha (m+1)] at hc
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_derivative,taylor_coeff,hInverseCoeff_series Y ha] at hc
  change hInverseCoeff (m+1) Y*(m+1 : ℂ) =
    ∑ i ∈ Finset.range (m+1), (logKernelCoeff (i+1) Y*(i+1 : ℂ))*hInverseCoeff (m-i) Y at hc
  calc
    _ = hInverseCoeff (m+1) Y*(m+1 : ℂ) := by ring
    _ = _ := hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
lemma hInverseCoeff_recursion_div (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    hInverseCoeff (m+1) Y =
      (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y)/(m+1 : ℂ) := by
  have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  apply (eq_div_iff hn).2
  linear_combination hInverseCoeff_recursion Y ha m
lemma hInverseCoeff_analyticAt (m : ℕ) (Y : ℂ) (ha : deriv X Y ≠ 0) :
    AnalyticAt ℂ (hInverseCoeff m) Y := by
  have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply (analyticAt_const (v := (1 : ℂ))).congr
      filter_upwards [hane] with W hW
      exact (hInverseCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) W*hInverseCoeff (m-i) W)/(m+1 : ℂ)
      have hE : AnalyticAt ℂ E Y := by
        apply AnalyticAt.div_const
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) Y ha)).mul (ih (m-i) (by omega))
      apply hE.congr
      filter_upwards [hane] with W hW
      exact (hInverseCoeff_recursion_div W hW m).symm
lemma hInverseCoeff_parameter_real (m : ℕ) : RealCoefficients (hInverseCoeff m) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have hane : ∀ᶠ W in 𝓝 (0 : ℂ), deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply realCoefficients_congr (realCoefficients_real_const 1)
      filter_upwards [hane] with W hW
      exact (hInverseCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) W*hInverseCoeff (m-i) W)/(m+1 : ℂ)
      have hsA : AnalyticAt ℂ
          (fun W => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) W*hInverseCoeff (m-i) W) 0 := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) 0 ha)).mul
          (hInverseCoeff_analyticAt (m-i) 0 ha)
      have hsR : RealCoefficients
          (fun W => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) W*hInverseCoeff (m-i) W) := by
        apply realCoefficients_finset_sum
        · intro i hi
          exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) 0 ha)).mul
            (hInverseCoeff_analyticAt (m-i) 0 ha)
        · intro i hi
          have hp := realCoefficients_mul (logKernelCoeff_analyticAt (i+1) 0 ha)
            (hInverseCoeff_analyticAt (m-i) 0 ha) (logKernelCoeff_parameter_real (i+1))
            (ih (m-i) (by omega))
          have hc := realCoefficients_const_mul (i+1 : ℝ) hp
          push_cast at hc
          simpa only [mul_assoc] using hc
      have hER : RealCoefficients E := by
        have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have hp := realCoefficients_real_const (m+1 : ℝ)
        push_cast at hp
        exact realCoefficients_div hsA analyticAt_const hn hsR hp
      apply realCoefficients_congr hER
      filter_upwards [hane] with W hW
      exact (hInverseCoeff_recursion_div W hW m).symm
lemma realTaylor_congr_event {f g : ℂ → ℂ} (he : f =ᶠ[𝓝 0] g) : realTaylor f = realTaylor g := by
  ext q
  simp only [realTaylor_coeff,realCoeff,WP.coeff,he.iteratedDeriv_eq q]
lemma realTaylor_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    realTaylor (fun Y => ∑ i ∈ s, f i Y) = ∑ i ∈ s, realTaylor (f i) := by
  ext q
  simp only [realTaylor_coeff,map_sum,realCoeff,WP.coeff]
  rw [iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.sum_div]
  change Complex.reCLM (∑ i ∈ s, iteratedDeriv q (f i) 0/(q.factorial : ℂ)) = _
  rw [map_sum]
  rfl
lemma hInverseCoeff_realTaylor_zero : realTaylor (hInverseCoeff 0) = 1 := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : hInverseCoeff 0 =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    exact hInverseCoeff_zero Y hY
  apply realTaylor_of_taylor_map
  rw [taylor_congr he,taylor_const]
  simp
lemma hInverseCoeff_realTaylor_recursion (m : ℕ) :
    PowerSeries.C (m+1 : ℝ)*realTaylor (hInverseCoeff (m+1)) =
      ∑ i ∈ Finset.range (m+1), PowerSeries.C (i+1 : ℝ)*
        (realTaylor (logKernelCoeff (i+1))*realTaylor (hInverseCoeff (m-i))) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : (fun Y => Complex.ofReal (m+1 : ℝ)*hInverseCoeff (m+1) Y) =ᶠ[𝓝 0]
      (fun Y => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    push_cast
    exact hInverseCoeff_recursion Y hY m
  have ht := realTaylor_congr_event he
  rw [realTaylor_const_mul,realTaylor_finset_sum] at ht
  · calc
      _ = ∑ i ∈ Finset.range (m+1), realTaylor (fun Y => (i+1 : ℂ)*logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y) := ht
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfi : (fun Y => (i+1 : ℂ)*logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y) =
            fun Y => Complex.ofReal (i+1 : ℝ)*(logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y) := by
          funext Y
          push_cast
          ring
        rw [hfi,realTaylor_const_mul (i+1 : ℝ) (fun Y => logKernelCoeff (i+1) Y*hInverseCoeff (m-i) Y),
          realTaylor_mul (logKernelCoeff_analyticAt (i+1) 0 ha) (hInverseCoeff_analyticAt (m-i) 0 ha)
            (logKernelCoeff_parameter_real (i+1)) (hInverseCoeff_parameter_real (m-i))]
  · intro i hi
    exact (analyticAt_const.mul (logKernelCoeff_analyticAt (i+1) 0 ha)).mul (hInverseCoeff_analyticAt (m-i) 0 ha)
lemma logKernelCoeff_realTaylor_parameter (m : ℕ) :
    PowerSeries.derivative (realTaylor (logKernelCoeff (m+1))) =
      PowerSeries.C (2*(m+2) : ℝ)*realTaylor (logKernelCoeff (m+2))+
        PowerSeries.C (3 : ℝ)*realTaylor (hInverseCoeff (m+2)) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : deriv (logKernelCoeff (m+1)) =ᶠ[𝓝 0]
      (fun Y => Complex.ofReal (2*(m+2) : ℝ)*logKernelCoeff (m+2) Y+
        Complex.ofReal (3 : ℝ)*hInverseCoeff (m+2) Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    have h := kernel_log_parameter_deriv Y hY (m+1) (Nat.succ_pos m)
    dsimp only [hInverseCoeff]
    push_cast at h ⊢
    linear_combination h
  have ht := realTaylor_congr_event he
  rw [realTaylor_deriv,realTaylor_add
    (f := fun Y => Complex.ofReal (2*(m+2) : ℝ)*logKernelCoeff (m+2) Y)
    (g := fun Y => Complex.ofReal (3 : ℝ)*hInverseCoeff (m+2) Y)
    (analyticAt_const.mul (logKernelCoeff_analyticAt (m+2) 0 ha))
    (analyticAt_const.mul (hInverseCoeff_analyticAt (m+2) 0 ha)),
    realTaylor_const_mul,realTaylor_const_mul] at ht
  exact ht
lemma H_kernel_parameter_nonneg :
    (∀ q m, 0 ≤ PowerSeries.coeff q (realTaylor (logKernelCoeff (m+1)))) ∧
      (∀ q m, 0 ≤ PowerSeries.coeff q (realTaylor (hInverseCoeff m))) := by
  apply logarithmic_parameter_coeff_nonneg (fun m => realTaylor (logKernelCoeff m))
    (fun m => realTaylor (hInverseCoeff m)) 3 (by norm_num) _ hInverseCoeff_realTaylor_zero
    hInverseCoeff_realTaylor_recursion logKernelCoeff_realTaylor_parameter
  intro m
  simpa [realTaylor_coeff,realCoeff,WP.coeff] using (logKernelCoeff_zero_succ_pos m).le
lemma logKernelCoeff_derivative_nonneg (m : ℕ) (hm : 0 < m) (q : ℕ) :
    0 ≤ (iteratedDeriv q (logKernelCoeff m) 0).re := by
  cases m with
  | zero => omega
  | succ m =>
    have hc := H_kernel_parameter_nonneg.1 q m
    simp only [realTaylor_coeff] at hc
    have hf : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    have he : iteratedDeriv q (logKernelCoeff (m+1)) 0 = WP.coeff (logKernelCoeff (m+1)) q*q.factorial := by
      unfold WP.coeff
      field_simp
    rw [he]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,mul_zero,sub_zero]
    exact mul_nonneg hc (Nat.cast_nonneg q.factorial)

lemma logKernelCoeff_hasSum (m : ℕ) (Y : ℂ) (hY : ‖Y‖ < y₀) :
    HasSum (fun q => WP.coeff (logKernelCoeff m) q*Y^q) (logKernelCoeff m Y) := by
  have hf : DifferentiableOn ℂ (logKernelCoeff m) (Metric.ball 0 y₀) := by
    intro W hW
    apply DifferentiableAt.differentiableWithinAt
    exact (logKernelCoeff_analyticAt m W (derivX_ne_zero_of_norm_lt W (by simpa using hW))).differentiableAt
  have hs := Complex.hasSum_taylorSeries_on_ball hf (by simpa using hY)
  convert hs using 1
  ext q
  simp only [WP.coeff,sub_zero,smul_eq_mul]
  ring
lemma logKernelCoeff_real_hasSum (m : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    HasSum (fun q => realCoeff (logKernelCoeff m) q*Y^q) (logKernelCoeff m Y).re := by
  have hn : ‖(Y : ℂ)‖ < y₀ := by simpa [abs_of_nonneg hY.1] using hY.2
  have hs := Complex.reCLM.hasSum (logKernelCoeff_hasSum m Y hn)
  convert hs using 1
  · ext q
    change realCoeff (logKernelCoeff m) q*Y^q = (WP.coeff (logKernelCoeff m) q*(Y : ℂ)^q).re
    rw [← Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,realCoeff]
  · rfl
lemma logKernelCoeff_real_value (m : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    (logKernelCoeff m Y).im = 0 := by
  have hn : ‖(Y : ℂ)‖ < y₀ := by simpa [abs_of_nonneg hY.1] using hY.2
  have hs := Complex.imCLM.hasSum (logKernelCoeff_hasSum m Y hn)
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) (logKernelCoeff m Y).im := by
    convert hs using 1
    · ext q
      change 0 = (WP.coeff (logKernelCoeff m) q*(Y : ℂ)^q).im
      rw [← Complex.ofReal_pow,Complex.mul_im]
      simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,logKernelCoeff_parameter_real m q,zero_mul,add_zero]
    · rfl
  exact hz.unique (hasSum_zero)
lemma logKernelCoeff_real_pos (m : ℕ) (hm : 0 < m) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    0 < (logKernelCoeff m Y).re := by
  have hs := logKernelCoeff_real_hasSum m Y hY
  have hcoef : ∀ q, 0 ≤ realCoeff (logKernelCoeff m) q := by
    intro q
    cases m with
    | zero => omega
    | succ m => simpa only [realTaylor_coeff] using H_kernel_parameter_nonneg.1 q m
  have hnonneg : ∀ q, 0 ≤ realCoeff (logKernelCoeff m) q*Y^q :=
    fun q => mul_nonneg (hcoef q) (pow_nonneg hY.1 q)
  have hzero : 0 < realCoeff (logKernelCoeff m) 0*Y^0 := by
    simpa [realCoeff,WP.coeff] using logKernelCoeff_zero_pos m hm
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos hnonneg 0 hzero

lemma H_negative_power_coeff_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (h : ℝ) (hh : 0 < h) (m : ℕ) :
    0 < realCoeff (fun z => Complex.exp (-(h : ℂ)*Complex.log (H Y z))) m := by
  let f := H (Y : ℂ)
  let T (z : ℂ) := Complex.log (deriv X Y/f z)
  let G (z : ℂ) := Complex.exp (-(h : ℂ)*Complex.log (f z))
  let F := taylor f
  let L := taylor T
  let E := taylor G
  let p := PowerSeries.C (h : ℂ)*PowerSeries.derivative L
  have haP := a_pos Y hY
  have haN : f 0 ≠ 0 := by
    simp only [f,H_zero,derivX_ofReal]
    exact_mod_cast (ne_of_gt haP)
  have hf : AnalyticAt ℂ f 0 := (H_differentiable Y).analyticAt 0
  have hfPlane : f 0 ∈ Complex.slitPlane := by
    dsimp only [f]
    rw [H_zero,derivX_ofReal]
    exact Complex.ofReal_mem_slitPlane.mpr haP
  have hG : AnalyticAt ℂ G 0 := (analyticAt_const.mul (hf.clog hfPlane)).cexp
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), f z ∈ Complex.slitPlane :=
    hf.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hfPlane)
  have he : (fun z => deriv G z*f z) =ᶠ[𝓝 0] (fun z => -(h : ℂ)*deriv f z*G z) := by
    filter_upwards [hslit] with z hz
    have hd := (((((H_differentiable Y) z).hasDerivAt.clog hz).const_mul (-(h : ℂ))).cexp).deriv
    have hd' : deriv G z = G z*(-(h : ℂ)*(deriv f z/f z)) := hd
    rw [hd']
    field_simp [Complex.slitPlane_ne_zero hz]
    <;> ring
  have ht := taylor_congr he
  rw [taylor_mul hG.deriv hf,taylor_deriv] at ht
  have hfun : (fun z => -(h : ℂ)*deriv f z*G z) = fun z => -(h : ℂ)*(deriv f z*G z) := by funext z; ring
  rw [hfun,taylor_const_mul,taylor_mul hf.deriv hG,taylor_deriv] at ht
  have hlog : PowerSeries.derivative L*F = -PowerSeries.derivative F := by
    simpa only [L,T,F,f,H_zero] using logarithmic_taylor_identity f hf haN
  have hF0 : PowerSeries.constantCoeff F ≠ 0 := by simpa [F] using haN
  have hFn : F ≠ 0 := by intro hzero; simpa [hzero] using hF0
  have hE : PowerSeries.derivative E = p*E := by
    apply mul_right_cancel₀ hFn
    calc
      PowerSeries.derivative E*F = PowerSeries.C (-(h : ℂ))*(PowerSeries.derivative F*E) := ht
      _ = PowerSeries.C (h : ℂ)*(PowerSeries.derivative L*F)*E := by
        rw [hlog]
        simp only [map_neg]
        ring
      _ = (p*E)*F := by dsimp [p]; ring
  have hE0 : PowerSeries.constantCoeff E = Complex.ofReal (Real.exp (-h*Real.log (a Y))) := by
    rw [taylor_constant]
    dsimp only [G,f]
    rw [H_zero,derivX_ofReal,← Complex.ofReal_log haP.le]
    push_cast
    <;> rfl
  have hp : ∀ n, (PowerSeries.coeff n p).im = 0 ∧ 0 < (PowerSeries.coeff n p).re := by
    intro n
    simp only [p,L,T,f,PowerSeries.coeff_C_mul,PowerSeries.coeff_derivative,taylor_coeff]
    change ((h : ℂ)*(logKernelCoeff (n+1) Y*(n+1 : ℂ))).im = 0 ∧
      0 < ((h : ℂ)*(logKernelCoeff (n+1) Y*(n+1 : ℂ))).re
    have hi := logKernelCoeff_real_value (n+1) Y hY
    have hp := logKernelCoeff_real_pos (n+1) (Nat.succ_pos n) Y hY
    constructor
    · simp [Complex.mul_im,hi]
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,
        Complex.natCast_re,Complex.natCast_im,Complex.one_re,Complex.one_im,zero_add,mul_zero,zero_mul,sub_zero,hi]
      exact mul_pos hh (mul_pos hp (by positivity : (0 : ℝ) < (n : ℝ)+1))
  have hpos := complex_series_ode_coeff_pos p E (Real.exp (-h*Real.log (a Y)))
    (Real.exp_pos _) hp hE0 hE m
  simpa only [E,taylor_coeff,realCoeff,G,f] using hpos.2

lemma logarithmic_slope_taylor (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (ha : f 0 ≠ 0) :
    taylor (fun z => -deriv f z/f z) =
      PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z))) := by
  have he : (fun z => -deriv f z/f z) = fun z => ((-1 : ℂ)*deriv f z)*(f z)⁻¹ := by funext z; ring
  have hleft : taylor (fun z => -deriv f z/f z) = -PowerSeries.derivative (taylor f)*(taylor f)⁻¹ := by
    rw [he,taylor_mul (f := fun z => (-1 : ℂ)*deriv f z) (g := fun z => (f z)⁻¹)
      (analyticAt_const.mul hf.deriv) (hf.inv ha),taylor_const_mul,taylor_deriv,taylor_inv hf ha]
    simp only [map_neg,map_one,neg_one_mul]
  rw [hleft]
  have hp := logarithmic_taylor_identity f hf ha
  have hF0 : PowerSeries.constantCoeff (taylor f) ≠ 0 := by simpa using ha
  calc
    _ = (PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z)))*taylor f)*(taylor f)⁻¹ := by rw [hp]
    _ = _ := by rw [mul_assoc,PowerSeries.mul_inv_cancel _ hF0,mul_one]
lemma H_logarithmic_coeff_pos (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (m : ℕ) :
    0 < realCoeff (fun z => -deriv (H Y) z/H Y z) m := by
  have ha : H (Y : ℂ) 0 ≠ 0 := by
    rw [H_zero,derivX_ofReal]
    exact_mod_cast a_ne_zero Y hY
  have h := congrArg (PowerSeries.coeff m)
    (logarithmic_slope_taylor (H Y) ((H_differentiable Y).analyticAt 0) ha)
  simp only [taylor_coeff,PowerSeries.coeff_derivative,H_zero] at h
  change WP.coeff (fun z => -deriv (H Y) z/H Y z) m = logKernelCoeff (m+1) Y*(m+1 : ℂ) at h
  unfold realCoeff
  rw [h,Complex.mul_re]
  simp only [Complex.add_re,Complex.add_im,Complex.natCast_re,Complex.natCast_im,
    Complex.one_re,Complex.one_im,zero_add,mul_zero,sub_zero]
  exact mul_pos (logKernelCoeff_real_pos (m+1) (Nat.succ_pos m) Y hY) (by positivity)

end WP.Analysis
