import WPFormalization.Analysis.HKernelPositivity

/-! The actual K-kernel logarithmic and inverse coefficient positivity.
The finite parameter recurrences use α=1 and the proved sinc/Bessel initial jets. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
def logKCoeff (m : ℕ) (Y : ℂ) : ℂ := WP.coeff (fun z => Complex.log (deriv X Y/K Y z)) m
lemma coeff_K_formula (Y : ℂ) (n : ℕ) :
    WP.coeff (K Y) n = iteratedDeriv (n+1) X Y/(oddFactorial n : ℂ) := by
  unfold WP.coeff
  rw [iteratedDeriv_K_zero]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  <;> ring
lemma coeff_K_analyticAt (n : ℕ) (Y : ℂ) : AnalyticAt ℂ (fun W => WP.coeff (K W) n) Y := by
  have he : (fun W => WP.coeff (K W) n) =
      fun W => iteratedDeriv (n+1) X W/(oddFactorial n : ℂ) := funext (fun W => coeff_K_formula W n)
  rw [he]
  exact ((iteratedDeriv_X_differentiable (n+1)).analyticAt Y).div_const
lemma logKCoeff_zero (Y : ℂ) (ha : deriv X Y ≠ 0) : logKCoeff 0 Y = 0 := by
  simp [logKCoeff,WP.coeff,K_zero,ha]
lemma logKCoeff_finite_recursion (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    logKCoeff (m+1) Y =
      (-(m+1 : ℂ)*WP.coeff (K Y) (m+1)-
        ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) /
          ((m+1 : ℂ)*deriv X Y) := by
  have h := logarithmic_coeff_identity (K Y) ((K_differentiable Y).analyticAt 0)
    (by rw [K_zero]; exact ha) m
  simp only [K_zero] at h
  change (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) = _ at h
  rw [Finset.sum_range_succ,Nat.sub_self] at h
  have h0 : WP.coeff (K Y) 0 = deriv X Y := by simp [WP.coeff,K_zero]
  rw [h0] at h
  have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  apply (eq_div_iff (mul_ne_zero hn ha)).2
  linear_combination h
lemma logKCoeff_analyticAt (m : ℕ) (Y : ℂ) (ha : deriv X Y ≠ 0) :
    AnalyticAt ℂ (logKCoeff m) Y := by
  induction m using Nat.strong_induction_on generalizing Y with
  | h m ih =>
    have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
      ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
    cases m with
    | zero =>
      apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [hane] with W hW
      exact (logKCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (-(m+1 : ℂ)*WP.coeff (K W) (m+1)-
          ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) W*WP.coeff (K W) (m-i)) /
            ((m+1 : ℂ)*deriv X W)
      have hs : AnalyticAt ℂ
          (fun W => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) W*WP.coeff (K W) (m-i)) Y := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        exact (analyticAt_const.mul (ih (i+1) (by omega) Y ha)).mul (coeff_K_analyticAt (m-i) Y)
      have hE : AnalyticAt ℂ E Y := by
        have hd : AnalyticAt ℂ (fun W => (m+1 : ℂ)*deriv X W) Y :=
          analyticAt_const.mul (X_differentiable.analyticAt Y).deriv
        have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        exact ((analyticAt_const.mul (coeff_K_analyticAt (m+1) Y)).sub hs).div hd (mul_ne_zero hn ha)
      apply hE.congr
      filter_upwards [hane] with W hW
      exact (logKCoeff_finite_recursion W hW m).symm

lemma deriv_coeff_K_parameter (Y : ℂ) (n : ℕ) :
    deriv (fun W => WP.coeff (K W) n) Y = (2*n+3 : ℂ)*WP.coeff (K Y) (n+1) := by
  have he : (fun W => WP.coeff (K W) n) =
      fun W => iteratedDeriv (n+1) X W/(oddFactorial n : ℂ) := funext (fun W => coeff_K_formula W n)
  rw [he,deriv_div_const,← iteratedDeriv_succ,coeff_K_formula,
    oddFactorial_succ n]
  push_cast
  have ho : (oddFactorial n : ℂ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero n
  have hn : (2*n+3 : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2*n+3 ≠ 0)
  ring_nf at ho hn ⊢
  field_simp [ho,hn]
  have hc : (3+(n : ℂ)*2)*(3+(n : ℂ)*2)⁻¹ = 1 := mul_inv_cancel₀ hn
  linear_combination -iteratedDeriv (2+n) X Y*hc
lemma k_kernel_parameter_series (Y : ℂ) :
    coefficientDeriv (fun W => taylor (K W)) Y =
      2*PowerSeries.derivative (taylor (K Y))+PowerSeries.C (1 : ℂ)*shiftSeries (taylor (K Y)) := by
  ext n
  simp only [coefficientDeriv_coeff,taylor_coeff,map_add,PowerSeries.coeff_ofNat_mul,
    PowerSeries.coeff_derivative,PowerSeries.coeff_C_mul,shiftSeries_coeff]
  rw [deriv_coeff_K_parameter]
  push_cast
  ring
lemma k_kernel_log_parameter_deriv (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) (hm : 0 < m) :
    deriv (logKCoeff m) Y =
      2*(m+1 : ℂ)*logKCoeff (m+1) Y+
        1*deriv X Y*WP.coeff (fun z => (K Y z)⁻¹) (m+1) := by
  let F (W : ℂ) := taylor (K W)
  let T (W : ℂ) := taylor (fun z => Complex.log (deriv X W/K W z))
  have hF : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (F W)) Y := by
    intro n
    simpa only [F,taylor_coeff] using coeff_K_analyticAt n Y
  have hT : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (T W)) Y := by
    intro n
    have he : (fun W => PowerSeries.coeff n (T W)) = logKCoeff n := by
      funext W
      simp only [T,taylor_coeff,logKCoeff]
    rw [he]
    exact logKCoeff_analyticAt n Y ha
  have hF0 : PowerSeries.constantCoeff (F Y) ≠ 0 := by simpa [F,K_zero] using ha
  have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
  have hlog : (fun W => PowerSeries.derivative (T W)*F W) =ᶠ[𝓝 Y]
      (fun W => -PowerSeries.derivative (F W)) := by
    filter_upwards [hane] with W hW
    simpa only [F,T,K_zero] using
      logarithmic_taylor_identity (K W) ((K_differentiable W).analyticAt 0) (by rw [K_zero]; exact hW)
  have hT0 : ∀ᶠ W in 𝓝 Y, PowerSeries.constantCoeff (T W) = 0 := by
    filter_upwards [hane] with W hW
    simp [T,K_zero,hW]
  have hparam : coefficientDeriv F Y =
      2*PowerSeries.derivative (F Y)+PowerSeries.C (1 : ℂ)*shiftSeries (F Y) := k_kernel_parameter_series Y
  have hpde := coefficientDeriv_log_pde F T Y 1 hF hT hF0 hlog hT0 hparam
  have hc := congrArg (PowerSeries.coeff m) hpde
  dsimp only [F,T] at hc
  simp only [coefficientDeriv_coeff,taylor_coeff,map_add,PowerSeries.coeff_C,
    if_neg (ne_of_gt hm),zero_add,PowerSeries.coeff_ofNat_mul,PowerSeries.coeff_derivative,
    PowerSeries.coeff_C_mul,shiftSeries_coeff,taylor_constant,K_zero] at hc
  rw [← taylor_inv ((K_differentiable Y).analyticAt 0) (by rw [K_zero]; exact ha)] at hc
  simp only [taylor_coeff] at hc
  change deriv (logKCoeff m) Y =
    2*(logKCoeff (m+1) Y*(m+1 : ℂ))+1*(deriv X Y*WP.coeff (fun z => (K Y z)⁻¹) (m+1)) at hc
  linear_combination hc


lemma normalizedBesselCoeff_three_two (n : ℕ) :
    normalizedBesselCoeff 3 2 n = (-1 : ℝ)^n/((n.factorial : ℝ)*(oddFactorial n : ℝ)) := by
  induction n with
  | zero => norm_num [normalizedBesselCoeff,oddFactorial,Finset.prod_range_succ]
  | succ n ih =>
    rw [normalizedBesselCoeff,ih,Nat.factorial_succ,oddFactorial_succ n]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    have ho : (oddFactorial n : ℝ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero n
    have ht : (2*n+3 : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    <;> ring
lemma coeff_K_zero_eq_bessel (n : ℕ) :
    WP.coeff (K 0) n = Complex.ofReal (normalizedBesselCoeff 3 2 n) := by
  rw [normalizedBesselCoeff_three_two,coeff_K_formula,iteratedDeriv_X_succ_zero]
  push_cast
  ring
lemma taylor_K_zero_eq_bessel :
    taylor (K 0) = PowerSeries.map Complex.ofRealHom (normalizedBesselSeries 3 2) := by
  ext n
  simp only [taylor_coeff,PowerSeries.coeff_map,normalizedBesselSeries,PowerSeries.coeff_mk,Complex.ofRealHom_eq_coe]
  exact coeff_K_zero_eq_bessel n
lemma logKCoeff_zero_succ_pos (n : ℕ) : 0 < (logKCoeff (n+1) 0).re := by
  have ha : K (0 : ℂ) 0 ≠ 0 := by rw [K_zero,derivX_zero]; exact one_ne_zero
  have hp := realCoeff_logSlope_pos_of_bessel (K 0) 3 2 (by norm_num) (by norm_num)
    ((K_differentiable 0).analyticAt 0) ha taylor_K_zero_eq_bessel n
  have h := congrArg (PowerSeries.coeff n)
    (logarithmic_slope_taylor (K 0) ((K_differentiable 0).analyticAt 0) ha)
  simp only [taylor_coeff,PowerSeries.coeff_derivative,K_zero] at h
  change WP.coeff (fun z => -deriv (K 0) z/K 0 z) n = logKCoeff (n+1) 0*(n+1 : ℂ) at h
  unfold realCoeff at hp
  rw [h,Complex.mul_re] at hp
  simp only [Complex.add_re,Complex.add_im,Complex.natCast_re,Complex.natCast_im,
    Complex.one_re,Complex.one_im,zero_add,mul_zero,sub_zero] at hp
  exact (mul_pos_iff_of_pos_right (by positivity : (0 : ℝ) < n+1)).mp hp
lemma coeff_K_parameter_real (n : ℕ) : RealCoefficients (fun Y => WP.coeff (K Y) n) := by
  have he : (fun Y => WP.coeff (K Y) n) =
      fun Y => (Complex.ofReal (1/(oddFactorial n : ℝ)))*iteratedDeriv (n+1) X Y := by
    funext Y
    rw [coeff_K_formula]
    push_cast
    ring
  rw [he]
  exact realCoefficients_const_mul _ (realCoefficients_iteratedDeriv_X (n+1))
lemma logKCoeff_parameter_real (m : ℕ) : RealCoefficients (logKCoeff m) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have hane : ∀ᶠ Y in 𝓝 (0 : ℂ), deriv X Y ≠ 0 :=
    ((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply realCoefficients_congr (realCoefficients_real_const 0)
      filter_upwards [hane] with Y hY
      exact (logKCoeff_zero Y hY).symm
    | succ m =>
      let E (Y : ℂ) :=
        (-(m+1 : ℂ)*WP.coeff (K Y) (m+1)-
          ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) /
            ((m+1 : ℂ)*deriv X Y)
      have hsA : AnalyticAt ℂ
          (fun Y => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) 0 := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) 0 ha)).mul (coeff_K_analyticAt (m-i) 0)
      have hsR : RealCoefficients
          (fun Y => ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) := by
        apply realCoefficients_finset_sum
        · intro i hi
          exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) 0 ha)).mul (coeff_K_analyticAt (m-i) 0)
        · intro i hi
          have hi' : i < m := Finset.mem_range.mp hi
          have hmul := realCoefficients_mul (logKCoeff_analyticAt (i+1) 0 ha)
            (coeff_K_analyticAt (m-i) 0) (ih (i+1) (by omega)) (coeff_K_parameter_real (m-i))
          have hscalar := realCoefficients_const_mul (i+1 : ℝ) hmul
          push_cast at hscalar
          simpa only [mul_assoc] using hscalar
      have hnumR : RealCoefficients
          (fun Y => -(m+1 : ℂ)*WP.coeff (K Y) (m+1)-
            ∑ i ∈ Finset.range m, (i+1 : ℂ)*logKCoeff (i+1) Y*WP.coeff (K Y) (m-i)) := by
        apply realCoefficients_sub (analyticAt_const.mul (coeff_K_analyticAt (m+1) 0)) hsA _ hsR
        have hscalar := realCoefficients_const_mul (-(m+1 : ℝ)) (coeff_K_parameter_real (m+1))
        push_cast at hscalar
        exact hscalar
      have hdenR : RealCoefficients (fun Y => (m+1 : ℂ)*deriv X Y) := by
        have hscalar := realCoefficients_const_mul (m+1 : ℝ) (realCoefficients_iteratedDeriv_X 1)
        simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,iteratedDeriv_one] using hscalar
      have hER : RealCoefficients E := by
        apply realCoefficients_div (g := fun Y => (m+1 : ℂ)*deriv X Y) ((analyticAt_const.mul (coeff_K_analyticAt (m+1) 0)).sub hsA)
          (analyticAt_const.mul (X_differentiable.analyticAt 0).deriv) _ hnumR hdenR
        have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        exact mul_ne_zero hn ha
      apply realCoefficients_congr hER
      filter_upwards [hane] with Y hY
      exact (logKCoeff_finite_recursion Y hY m).symm

def kInverseCoeff (m : ℕ) (Y : ℂ) : ℂ :=
  deriv X Y*WP.coeff (fun z => (K Y z)⁻¹) m
lemma kInverseCoeff_zero (Y : ℂ) (ha : deriv X Y ≠ 0) : kInverseCoeff 0 Y = 1 := by
  simp [kInverseCoeff,WP.coeff,K_zero,ha]
lemma kInverseCoeff_series (Y : ℂ) (ha : deriv X Y ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.C (deriv X Y)*(taylor (K Y))⁻¹) = kInverseCoeff n Y := by
  rw [PowerSeries.coeff_C_mul,← taylor_inv ((K_differentiable Y).analyticAt 0) (by rw [K_zero]; exact ha),taylor_coeff]
  rfl
lemma kInverseCoeff_recursion (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    (m+1 : ℂ)*kInverseCoeff (m+1) Y =
      ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) Y*kInverseCoeff (m-i) Y := by
  have hp := normalized_inverse_taylor_differential (K Y) ((K_differentiable Y).analyticAt 0)
    (by rw [K_zero]; exact ha)
  simp only [K_zero] at hp
  have hc := congrArg (PowerSeries.coeff m) hp
  rw [PowerSeries.coeff_derivative,kInverseCoeff_series Y ha (m+1)] at hc
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_derivative,taylor_coeff,kInverseCoeff_series Y ha] at hc
  change kInverseCoeff (m+1) Y*(m+1 : ℂ) =
    ∑ i ∈ Finset.range (m+1), (logKCoeff (i+1) Y*(i+1 : ℂ))*kInverseCoeff (m-i) Y at hc
  calc
    _ = kInverseCoeff (m+1) Y*(m+1 : ℂ) := by ring
    _ = _ := hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
lemma kInverseCoeff_recursion_div (Y : ℂ) (ha : deriv X Y ≠ 0) (m : ℕ) :
    kInverseCoeff (m+1) Y =
      (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) Y*kInverseCoeff (m-i) Y)/(m+1 : ℂ) := by
  have hn : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  apply (eq_div_iff hn).2
  linear_combination kInverseCoeff_recursion Y ha m
lemma kInverseCoeff_analyticAt (m : ℕ) (Y : ℂ) (ha : deriv X Y ≠ 0) :
    AnalyticAt ℂ (kInverseCoeff m) Y := by
  have hane : ∀ᶠ W in 𝓝 Y, deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply (analyticAt_const (v := (1 : ℂ))).congr
      filter_upwards [hane] with W hW
      exact (kInverseCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) W*kInverseCoeff (m-i) W)/(m+1 : ℂ)
      have hE : AnalyticAt ℂ E Y := by
        apply AnalyticAt.div_const
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) Y ha)).mul (ih (m-i) (by omega))
      apply hE.congr
      filter_upwards [hane] with W hW
      exact (kInverseCoeff_recursion_div W hW m).symm
lemma kInverseCoeff_parameter_real (m : ℕ) : RealCoefficients (kInverseCoeff m) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have hane : ∀ᶠ W in 𝓝 (0 : ℂ), deriv X W ≠ 0 :=
    ((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      apply realCoefficients_congr (realCoefficients_real_const 1)
      filter_upwards [hane] with W hW
      exact (kInverseCoeff_zero W hW).symm
    | succ m =>
      let E (W : ℂ) :=
        (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) W*kInverseCoeff (m-i) W)/(m+1 : ℂ)
      have hsA : AnalyticAt ℂ
          (fun W => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) W*kInverseCoeff (m-i) W) 0 := by
        apply Finset.analyticAt_fun_sum
        intro i hi
        exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) 0 ha)).mul
          (kInverseCoeff_analyticAt (m-i) 0 ha)
      have hsR : RealCoefficients
          (fun W => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) W*kInverseCoeff (m-i) W) := by
        apply realCoefficients_finset_sum
        · intro i hi
          exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) 0 ha)).mul
            (kInverseCoeff_analyticAt (m-i) 0 ha)
        · intro i hi
          have hp := realCoefficients_mul (logKCoeff_analyticAt (i+1) 0 ha)
            (kInverseCoeff_analyticAt (m-i) 0 ha) (logKCoeff_parameter_real (i+1))
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
      exact (kInverseCoeff_recursion_div W hW m).symm
lemma kInverseCoeff_realTaylor_zero : realTaylor (kInverseCoeff 0) = 1 := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : kInverseCoeff 0 =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    exact kInverseCoeff_zero Y hY
  apply realTaylor_of_taylor_map
  rw [taylor_congr he,taylor_const]
  simp
lemma kInverseCoeff_realTaylor_recursion (m : ℕ) :
    PowerSeries.C (m+1 : ℝ)*realTaylor (kInverseCoeff (m+1)) =
      ∑ i ∈ Finset.range (m+1), PowerSeries.C (i+1 : ℝ)*
        (realTaylor (logKCoeff (i+1))*realTaylor (kInverseCoeff (m-i))) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : (fun Y => Complex.ofReal (m+1 : ℝ)*kInverseCoeff (m+1) Y) =ᶠ[𝓝 0]
      (fun Y => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logKCoeff (i+1) Y*kInverseCoeff (m-i) Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    push_cast
    exact kInverseCoeff_recursion Y hY m
  have ht := realTaylor_congr_event he
  rw [realTaylor_const_mul,realTaylor_finset_sum] at ht
  · calc
      _ = ∑ i ∈ Finset.range (m+1), realTaylor (fun Y => (i+1 : ℂ)*logKCoeff (i+1) Y*kInverseCoeff (m-i) Y) := ht
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfi : (fun Y => (i+1 : ℂ)*logKCoeff (i+1) Y*kInverseCoeff (m-i) Y) =
            fun Y => Complex.ofReal (i+1 : ℝ)*(logKCoeff (i+1) Y*kInverseCoeff (m-i) Y) := by
          funext Y
          push_cast
          ring
        rw [hfi,realTaylor_const_mul (i+1 : ℝ) (fun Y => logKCoeff (i+1) Y*kInverseCoeff (m-i) Y),
          realTaylor_mul (logKCoeff_analyticAt (i+1) 0 ha) (kInverseCoeff_analyticAt (m-i) 0 ha)
            (logKCoeff_parameter_real (i+1)) (kInverseCoeff_parameter_real (m-i))]
  · intro i hi
    exact (analyticAt_const.mul (logKCoeff_analyticAt (i+1) 0 ha)).mul (kInverseCoeff_analyticAt (m-i) 0 ha)
lemma logKCoeff_realTaylor_parameter (m : ℕ) :
    PowerSeries.derivative (realTaylor (logKCoeff (m+1))) =
      PowerSeries.C (2*(m+2) : ℝ)*realTaylor (logKCoeff (m+2))+
        PowerSeries.C (1 : ℝ)*realTaylor (kInverseCoeff (m+2)) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : deriv (logKCoeff (m+1)) =ᶠ[𝓝 0]
      (fun Y => Complex.ofReal (2*(m+2) : ℝ)*logKCoeff (m+2) Y+
        Complex.ofReal (1 : ℝ)*kInverseCoeff (m+2) Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    have h := k_kernel_log_parameter_deriv Y hY (m+1) (Nat.succ_pos m)
    dsimp only [kInverseCoeff]
    push_cast at h ⊢
    linear_combination h
  have ht := realTaylor_congr_event he
  rw [realTaylor_deriv,realTaylor_add
    (f := fun Y => Complex.ofReal (2*(m+2) : ℝ)*logKCoeff (m+2) Y)
    (g := fun Y => Complex.ofReal (1 : ℝ)*kInverseCoeff (m+2) Y)
    (analyticAt_const.mul (logKCoeff_analyticAt (m+2) 0 ha))
    (analyticAt_const.mul (kInverseCoeff_analyticAt (m+2) 0 ha)),
    realTaylor_const_mul,realTaylor_const_mul] at ht
  exact ht
lemma K_kernel_parameter_nonneg :
    (∀ q m, 0 ≤ PowerSeries.coeff q (realTaylor (logKCoeff (m+1)))) ∧
      (∀ q m, 0 ≤ PowerSeries.coeff q (realTaylor (kInverseCoeff m))) := by
  apply logarithmic_parameter_coeff_nonneg (fun m => realTaylor (logKCoeff m))
    (fun m => realTaylor (kInverseCoeff m)) 1 (by norm_num) _ kInverseCoeff_realTaylor_zero
    kInverseCoeff_realTaylor_recursion logKCoeff_realTaylor_parameter
  intro m
  simpa [realTaylor_coeff,realCoeff,WP.coeff] using (logKCoeff_zero_succ_pos m).le


lemma normalized_K_inverse_parameter_nonneg (l q : ℕ) :
    0 ≤ realCoeff (fun Y => deriv X Y*WP.coeff (fun z => (K Y z)⁻¹) l) q := by
  have he : (fun Y => deriv X Y*WP.coeff (fun z => (K Y z)⁻¹) l) = kInverseCoeff l := by
    funext Y
    rfl
  rw [he]
  simpa only [realTaylor_coeff] using K_kernel_parameter_nonneg.2 q l
lemma reciprocal_K_parameter_nonneg (l q : ℕ) :
    0 ≤ realCoeff (fun Y => WP.coeff (fun z => (K Y z)⁻¹) l) q := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : (fun Y => WP.coeff (fun z => (K Y z)⁻¹) l) =ᶠ[𝓝 0]
      (fun Y => (deriv X Y)⁻¹*kInverseCoeff l Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    dsimp only [kInverseCoeff]
    rw [← mul_assoc,inv_mul_cancel₀ hY,one_mul]
  have hRA : RealCoefficients (deriv X) := by
    simpa only [iteratedDeriv_one] using realCoefficients_iteratedDeriv_X 1
  have ht := realTaylor_congr_event he
  rw [realTaylor_mul (f := fun Y => (deriv X Y)⁻¹) (g := kInverseCoeff l) ((X_differentiable.analyticAt 0).deriv.inv ha)
    (kInverseCoeff_analyticAt l 0 ha) (realCoefficients_inv (X_differentiable.analyticAt 0).deriv ha hRA)
      (kInverseCoeff_parameter_real l)] at ht
  rw [← realTaylor_coeff,ht,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_nonneg
  intro i hi
  have hA : 0 ≤ PowerSeries.coeff i (realTaylor (fun Y => (deriv X Y)⁻¹)) := by
    simpa only [realTaylor_coeff] using (realCoeff_inv_derivX_pos i).le
  exact mul_nonneg hA (K_kernel_parameter_nonneg.2 (q-i) l)
end WP.Analysis
