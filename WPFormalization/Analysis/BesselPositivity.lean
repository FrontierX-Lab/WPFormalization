import WPFormalization.Analysis.RayleighPositivity
import WPFormalization.Analysis.Taylor
import WPFormalization.Statements.KernelCalculus
/-! Positivity of the reciprocal Bessel series used by the paper.
The connection to the actual X function uses its proved defining-series jets. -/
noncomputable section
namespace WP.Analysis
open PowerSeries
lemma normalizedBesselCoeff_one_one (n : ℕ) :
    normalizedBesselCoeff 1 1 n = (-1 : ℝ)^n/(n.factorial : ℝ)^2 := by
  induction n with
  | zero => norm_num [normalizedBesselCoeff]
  | succ n ih =>
    rw [normalizedBesselCoeff,ih,Nat.factorial_succ]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    <;> ring
lemma coeff_derivX_eq_bessel (n : ℕ) :
    WP.coeff (deriv X) n = Complex.ofReal (normalizedBesselCoeff 1 1 n) := by
  rw [normalizedBesselCoeff_one_one]
  unfold WP.coeff
  rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
  push_cast
  ring
lemma taylor_derivX_eq_bessel :
    taylor (deriv X) = PowerSeries.map Complex.ofRealHom (normalizedBesselSeries 1 1) := by
  ext n
  simp only [taylor_coeff,coeff_map,normalizedBesselSeries,coeff_mk,Complex.ofRealHom_eq_coe]
  exact coeff_derivX_eq_bessel n
lemma derivX_zero : deriv X (0 : ℂ) = 1 := by
  simpa using iteratedDeriv_X_succ_zero 0
lemma realCoeff_inv_derivX_pos (n : ℕ) :
    0 < realCoeff (fun Y => (deriv X Y)⁻¹) n := by
  let f := normalizedBesselSeries 1 1
  have hf0 : constantCoeff f ≠ 0 := by
    rw [normalizedBessel_constant]
    exact one_ne_zero
  have he : taylor (fun Y => (deriv X Y)⁻¹) = PowerSeries.map Complex.ofRealHom f⁻¹ := by
    rw [taylor_inv (X_differentiable.analyticAt 0).deriv (by rw [derivX_zero]; exact one_ne_zero),
      taylor_derivX_eq_bessel,← map_inv_ofReal _ hf0]
  have hc := congrArg (PowerSeries.coeff n) he
  have hre : realCoeff (fun Y => (deriv X Y)⁻¹) n = PowerSeries.coeff n f⁻¹ := by
    simpa only [taylor_coeff,coeff_map,Complex.ofRealHom_eq_coe,realCoeff,Complex.ofReal_re] using
      congrArg Complex.re hc
  rw [hre]
  exact normalizedBessel_inv_pos 1 1 (by norm_num) (by norm_num) n
lemma map_derivative_ofReal (p : PowerSeries ℝ) :
    PowerSeries.map Complex.ofRealHom (derivative p) = derivative (PowerSeries.map Complex.ofRealHom p) := by
  ext n
  simp only [coeff_map,coeff_derivative,Complex.ofRealHom_eq_coe]
  push_cast
  <;> rfl
lemma realCoeff_logSlope_pos_of_bessel (f : ℂ → ℂ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0)
    (he : taylor f = PowerSeries.map Complex.ofRealHom (normalizedBesselSeries α β)) (n : ℕ) :
    0 < realCoeff (fun z => -deriv f z/f z) n := by
  let F := normalizedBesselSeries α β
  have hF0 : constantCoeff F ≠ 0 := by rw [normalizedBessel_constant]; exact one_ne_zero
  have hfn : (fun z => -deriv f z/f z) = fun z => ((-1 : ℂ)*deriv f z)*(f z)⁻¹ := by
    funext z
    ring
  have ht : taylor (fun z => -deriv f z/f z) =
      PowerSeries.map Complex.ofRealHom (-derivative F*F⁻¹) := by
    rw [hfn,taylor_mul (f := fun z => (-1 : ℂ)*deriv f z) (g := fun z => (f z)⁻¹)
      (analyticAt_const.mul hf.deriv) (hf.inv hf0),taylor_const_mul,taylor_deriv,
      taylor_inv hf hf0,he]
    simp only [map_mul,map_neg]
    rw [map_inv_ofReal _ hF0,map_derivative_ofReal]
    simp [F]
  have hc := congrArg (PowerSeries.coeff n) ht
  have hre : realCoeff (fun z => -deriv f z/f z) n = PowerSeries.coeff n (-derivative F*F⁻¹) := by
    simpa only [taylor_coeff,coeff_map,Complex.ofRealHom_eq_coe,realCoeff,Complex.ofReal_re] using
      congrArg Complex.re hc
  rw [hre]
  exact normalizedBessel_logSlope_pos α β hα hβ n
lemma normalizedBesselCoeff_five_two (n : ℕ) :
    normalizedBesselCoeff 5 2 n =
      3*(-1 : ℝ)^n/((n.factorial : ℝ)*(oddFactorial (n+1) : ℝ)) := by
  induction n with
  | zero => norm_num [normalizedBesselCoeff,oddFactorial,Finset.prod_range_succ]
  | succ n ih =>
    rw [normalizedBesselCoeff,ih,Nat.factorial_succ,oddFactorial_succ (n+1)]
    push_cast
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    have ho : (oddFactorial (n+1) : ℝ) ≠ 0 := by exact_mod_cast oddFactorial_ne_zero (n+1)
    have ht : (2*n+5 : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    <;> ring


end WP.Analysis
