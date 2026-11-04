import WPFormalization.Statements.Basic

/-! Taylor jets of scalar analytic functions. These finite algebraic identities
connect the paper's iterated-derivative coefficients to Mathlib formal series.
No paper-specific estimate or unproved analytic input is assumed here. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology

def taylor (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (WP.coeff f)

@[simp] theorem taylor_coeff (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylor f) = WP.coeff f n := by simp [taylor]

@[simp] theorem taylor_constant (f : ℂ → ℂ) :
    PowerSeries.constantCoeff (taylor f) = f 0 := by simp [taylor, WP.coeff]

theorem taylor_congr {f g : ℂ → ℂ} (he : f =ᶠ[𝓝 0] g) : taylor f = taylor g := by
  ext n
  simp only [taylor_coeff, WP.coeff, he.iteratedDeriv_eq]

@[simp] theorem taylor_const (c : ℂ) : taylor (fun _ => c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [taylor, WP.coeff]
  | succ n => simp [taylor, WP.coeff, iteratedDeriv_const]

theorem taylor_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (fun z => f z+g z) = taylor f+taylor g := by
  ext n
  simp only [taylor_coeff, map_add, WP.coeff,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylor_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (fun z => f z-g z) = taylor f-taylor g := by
  ext n
  simp only [taylor_coeff, map_sub, WP.coeff,
    iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_div]

theorem taylor_const_mul (c : ℂ) (f : ℂ → ℂ) :
    taylor (fun z => c*f z) = PowerSeries.C c*taylor f := by
  ext n
  simp only [taylor_coeff, PowerSeries.coeff_C_mul, WP.coeff,
    iteratedDeriv_const_mul_field]
  ring

theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (fun z => f z*g z) = taylor f*taylor g := by
  ext n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [taylor_coeff, WP.coeff]
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hb : (n.choose i : ℂ)*(i.factorial : ℂ)*((n-i).factorial : ℂ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hif : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hdf : ((n-i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n-i).factorial_ne_zero
  field_simp
  linear_combination iteratedDeriv i f 0 * iteratedDeriv (n-i) g 0 * hb

theorem taylor_deriv {f : ℂ → ℂ} :
    taylor (deriv f) = PowerSeries.derivative (taylor f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, taylor_coeff, WP.coeff, ← iteratedDeriv_succ',
    Nat.factorial_succ, Nat.cast_mul]
  have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hns : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

@[simp] theorem taylor_id : taylor (fun z : ℂ => z) = PowerSeries.X := by
  ext n
  by_cases h : n = 1
  · subst n; norm_num [taylor, WP.coeff, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  · simp [taylor, WP.coeff, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X, h]

theorem taylor_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylor (fun z => f z^n) = taylor f^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ]
      rw [taylor_mul (f := fun z => f z^n) (g := f) (hf.pow n) hf, ih]

theorem taylor_inv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hzero : f 0 ≠ 0) :
    taylor (fun z => (f z)⁻¹) = (taylor f)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa using hzero)).2
  rw [← taylor_mul (f := fun z => (f z)⁻¹) (g := f) (hf.inv hzero) hf]
  calc
    _ = taylor (fun _ => 1) := by
      apply taylor_congr
      filter_upwards [hf.continuousAt.eventually (eventually_ne_nhds hzero)] with z hz
      simp [hz]
    _ = 1 := by simp

theorem taylor_euler {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    taylor (fun z => z*deriv f z) = PowerSeries.X*PowerSeries.derivative (taylor f) := by
  rw [taylor_mul (f := fun z : ℂ => z) (g := deriv f) analyticAt_id hf.deriv, taylor_id, taylor_deriv]

/-- Coefficientwise reality, without any positivity assertion. -/
def RealCoefficients (f : ℂ → ℂ) : Prop := ∀ n, (WP.coeff f n).im = 0

theorem taylor_real_lift {f : ℂ → ℂ} (hr : RealCoefficients f) :
    taylor f = PowerSeries.map Complex.ofRealHom (PowerSeries.mk (WP.realCoeff f)) := by
  ext n
  simp only [taylor_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    Complex.ofRealHom_eq_coe, WP.realCoeff]
  apply Complex.ext
  · simp
  · simpa using hr n

theorem map_inv_ofReal (p : PowerSeries ℝ) (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.map Complex.ofRealHom p⁻¹ = (PowerSeries.map Complex.ofRealHom p)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff]
    change ((PowerSeries.constantCoeff p : ℝ) : ℂ) ≠ 0
    exact_mod_cast hp)).2
  rw [← map_mul, PowerSeries.inv_mul_cancel p hp, map_one]

theorem realCoefficients_inv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hzero : f 0 ≠ 0) (hr : RealCoefficients f) :
    RealCoefficients (fun z => (f z)⁻¹) := by
  have hp : PowerSeries.constantCoeff (PowerSeries.mk (WP.realCoeff f)) ≠ 0 := by
    intro h
    have he := congrArg PowerSeries.constantCoeff (taylor_real_lift hr)
    simp only [taylor_constant, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map] at he
    have hpzero : PowerSeries.coeff 0 (PowerSeries.mk (WP.realCoeff f)) = 0 := by simpa using h
    rw [hpzero, map_zero] at he
    exact hzero he
  intro n
  have he := congrArg (PowerSeries.coeff n)
    (show taylor (fun z => (f z)⁻¹) =
      PowerSeries.map Complex.ofRealHom (PowerSeries.mk (WP.realCoeff f))⁻¹ by
        rw [taylor_inv hf hzero, taylor_real_lift hr, map_inv_ofReal _ hp])
  simpa only [taylor_coeff, PowerSeries.coeff_map, Complex.ofRealHom_eq_coe,
    Complex.ofReal_im] using congrArg Complex.im he

theorem realCoefficients_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hr : RealCoefficients f) (k : ℕ) : RealCoefficients (fun z => f z^k) := by
  intro n
  have he := congrArg (PowerSeries.coeff n)
    (show taylor (fun z => f z^k) =
      PowerSeries.map Complex.ofRealHom (PowerSeries.mk (WP.realCoeff f)^k) by
        rw [taylor_pow hf, taylor_real_lift hr, map_pow])
  simpa only [taylor_coeff, PowerSeries.coeff_map, Complex.ofRealHom_eq_coe,
    Complex.ofReal_im] using congrArg Complex.im he

abbrev realTaylor (f : ℂ → ℂ) : PowerSeries ℝ := PowerSeries.mk (WP.realCoeff f)

@[simp] theorem realTaylor_coeff (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (realTaylor f) = WP.realCoeff f n := by simp [realTaylor]

@[simp] theorem realTaylor_constant (f : ℂ → ℂ) :
    PowerSeries.constantCoeff (realTaylor f) = (f 0).re := by
  simp [realTaylor, WP.realCoeff, WP.coeff]

theorem realTaylor_of_taylor_map {f : ℂ → ℂ} {p : PowerSeries ℝ}
    (he : taylor f = PowerSeries.map Complex.ofRealHom p) : realTaylor f = p := by
  ext n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).re) he
  simpa only [taylor_coeff, realTaylor_coeff, PowerSeries.coeff_map,
    Complex.ofRealHom_eq_coe, Complex.ofReal_re, WP.realCoeff] using hn

theorem realTaylor_inv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hzero : f 0 ≠ 0) (hr : RealCoefficients f) :
    realTaylor (fun z => (f z)⁻¹) = (realTaylor f)⁻¹ := by
  have hp : PowerSeries.constantCoeff (realTaylor f) ≠ 0 := by
    intro h
    apply hzero
    apply Complex.ext
    · simpa [WP.realCoeff, WP.coeff] using h
    · simpa [WP.coeff] using hr 0
  apply realTaylor_of_taylor_map
  rw [taylor_inv hf hzero, taylor_real_lift hr, map_inv_ofReal _ hp]

theorem realTaylor_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hr : RealCoefficients f) (k : ℕ) : realTaylor (fun z => f z^k) = (realTaylor f)^k := by
  apply realTaylor_of_taylor_map
  rw [taylor_pow hf, taylor_real_lift hr, map_pow]

theorem realTaylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hrf : RealCoefficients f) (hrg : RealCoefficients g) :
    realTaylor (fun z => f z*g z) = realTaylor f*realTaylor g := by
  apply realTaylor_of_taylor_map
  rw [taylor_mul hf hg, taylor_real_lift hrf, taylor_real_lift hrg, map_mul]

theorem realTaylor_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    realTaylor (fun z => f z+g z) = realTaylor f+realTaylor g := by
  ext n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).re) (taylor_add hf hg)
  simpa only [map_add, taylor_coeff, realTaylor_coeff, Complex.add_re, WP.realCoeff] using hn

theorem realTaylor_const_mul (c : ℝ) (f : ℂ → ℂ) :
    realTaylor (fun z => (c : ℂ)*f z) = PowerSeries.C c*realTaylor f := by
  ext n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).re) (taylor_const_mul (c : ℂ) f)
  simpa only [taylor_coeff, realTaylor_coeff, PowerSeries.coeff_C_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, WP.realCoeff] using hn

theorem realTaylor_euler {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    realTaylor (fun z => z*deriv f z) = PowerSeries.X*PowerSeries.derivative (realTaylor f) := by
  ext n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).re) (taylor_euler hf)
  cases n with
  | zero => simpa [realTaylor, WP.realCoeff] using hn
  | succ n =>
      simpa [WP.realCoeff, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        using hn

end WP.Analysis
