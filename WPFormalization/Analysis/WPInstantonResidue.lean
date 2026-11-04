import WPFormalization.Analysis.WPInstantonAction
import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Coefficients.UniformSaddleProbability

/-! Actual circular residues and convergent Laurent expansions of the ordinary
WP instanton integrand. The residue is defined independently through circle
integrals; Cauchy's formula identifies it with the appropriate Taylor jet. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

def normalizedCircleIntegral (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(0, R), f z

/-- Circular residue at zero, whenever the small positive-radius limit exists. -/
def residueAtZero (f : ℂ → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (normalizedCircleIntegral f)

lemma residueAtZero_eq_of_eventually (f : ℂ → ℂ) (a : ℂ)
    (h : ∀ᶠ R in 𝓝[>] (0 : ℝ), normalizedCircleIntegral f R = a) :
    residueAtZero f = a := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with R hR
  exact hR.symm

lemma normalizedCircleIntegral_div_pow (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (n : ℕ) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ),
      normalizedCircleIntegral (fun z => f z / z^(n+1)) R = WP.coeff f n := by
  obtain ⟨ε, hε, ha⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  filter_upwards [Ioo_mem_nhdsGT hε] with R hR
  have hD : DifferentiableOn ℂ f (Metric.closedBall 0 R) := by
    intro z hz
    exact (ha (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hR.2)).differentiableAt.differentiableWithinAt
  have hc := hD.circleIntegral_one_div_sub_center_pow_smul hR.1 n
  have he : (fun z : ℂ => (1 / (z-0)^(n+1)) • f z) =
      (fun z => f z / z^(n+1)) := by funext z; simp [div_eq_mul_inv, mul_comm]
  rw [he] at hc
  unfold normalizedCircleIntegral WP.coeff
  rw [hc]
  simp only [smul_eq_mul]
  have hp := Complex.two_pi_I_ne_zero
  field_simp

lemma residueAtZero_div_pow (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    residueAtZero (fun z => f z / z^(n+1)) = WP.coeff f n :=
  residueAtZero_eq_of_eventually _ _ (normalizedCircleIntegral_div_pow f hf n)

lemma normalizedCircleIntegral_congr_punctured (f g : ℂ → ℂ)
    (h : ∀ z, z ≠ 0 → f z = g z) (R : ℝ) (hR : 0 < R) :
    normalizedCircleIntegral f R = normalizedCircleIntegral g R := by
  unfold normalizedCircleIntegral
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z hz
  apply h z
  intro hz0
  subst z
  have he : (0 : ℝ) = R := by simpa only [Metric.mem_sphere, dist_self] using hz
  linarith

lemma residueAtZero_congr_punctured (f g : ℂ → ℂ)
    (h : ∀ z, z ≠ 0 → f z = g z) : residueAtZero f = residueAtZero g := by
  have he : normalizedCircleIntegral f =ᶠ[𝓝[>] (0 : ℝ)] normalizedCircleIntegral g := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    exact normalizedCircleIntegral_congr_punctured f g h R hR
  unfold residueAtZero Filter.limUnder
  rw [Filter.map_congr he]

lemma coeff_pow (n k : ℕ) : WP.coeff (fun z : ℂ => z^n) k = if n = k then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff k) (taylor_pow (f := fun z : ℂ => z) analyticAt_id n)
  simpa only [taylor_id, taylor_coeff, PowerSeries.coeff_X_pow, eq_comm] using h

lemma coeff_comp_scaled_square (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (c : ℂ) (m : ℕ) :
    WP.coeff (fun z => f (c*z^2)) (2*m) = c^m * WP.coeff f m := by
  obtain ⟨R, hR, hTaylor⟩ := hf.exists_eventuallyEq_sum_add_pow_mul (m+1)
  let Z : ℂ → ℂ := fun z => c*z^2
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_const.mul (analyticAt_id.pow 2)
  have hZ0 : Z 0 = 0 := by simp [Z]
  have hZt : Tendsto Z (𝓝 0) (𝓝 0) := by simpa only [hZ0] using hZ.continuousAt.tendsto
  let term : ℕ → ℂ → ℂ := fun i z => (WP.coeff f i * c^i) * z^(2*i)
  have hterm (i : ℕ) : AnalyticAt ℂ (term i) 0 := analyticAt_const.mul (analyticAt_id.pow _)
  let tail : ℂ → ℂ := fun z => c^(m+1) * R (Z z)
  have hRc : AnalyticAt ℂ (fun z => R (Z z)) 0 := by
    apply AnalyticAt.comp _ hZ
    simpa only [hZ0] using hR
  have htail : AnalyticAt ℂ tail 0 := analyticAt_const.mul hRc
  have he : (fun z => f (c*z^2)) =ᶠ[𝓝 0]
      (fun z => (∑ i ∈ Finset.range (m+1), term i z) + z^(2*(m+1))*tail z) := by
    filter_upwards [hZt.eventually hTaylor] with z hz
    change f (Z z) = _
    rw [hz]
    simp only [smul_eq_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      dsimp [Z, term, WP.coeff]
      rw [mul_pow, ← pow_mul]
      ring
    · dsimp [Z, tail]
      rw [mul_pow, ← pow_mul]
      ring
  have hsum : AnalyticAt ℂ (fun z => ∑ i ∈ Finset.range (m+1), term i z) 0 :=
    Finset.analyticAt_fun_sum _ (fun i _ => hterm i)
  have hrem : AnalyticAt ℂ (fun z => z^(2*(m+1))*tail z) 0 :=
    (analyticAt_id.pow _).mul htail
  rw [coeff_congr_of_eventuallyEq _ _ he]
  have hadd := congrArg (PowerSeries.coeff (2*m)) (taylor_add hsum hrem)
  simp only [taylor_coeff, map_add] at hadd
  rw [hadd, coeff_id_pow_mul tail htail, ite_eq_right (by omega : ¬ 2*(m+1) ≤ 2*m), add_zero,
    coeff_finite_sum _ _ (fun i _ => hterm i)]
  calc
    _ = ∑ i ∈ Finset.range (m+1), (WP.coeff f i * c^i) * (if i = m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_const_mul, coeff_pow]
      have heq : 2*i = 2*m ↔ i = m := by omega
      simp only [heq]
    _ = _ := by simp [mul_comm]

def instantonIntegrand (h k : ℕ) (w : ℂ) : ℂ :=
  w^(2*k) * (instantonAction w)⁻¹^h

def instantonHolomorphicFactor (h : ℕ) (w : ℂ) : ℂ :=
  (3/2 : ℂ)^h * (H 0 (2 * (Real.pi : ℂ)^2 * w^2))⁻¹^h

lemma instantonHolomorphicFactor_analytic (h : ℕ) :
    AnalyticAt ℂ (instantonHolomorphicFactor h) 0 := by
  have harg : AnalyticAt ℂ (fun w : ℂ => 2 * (Real.pi : ℂ)^2 * w^2) 0 := by fun_prop
  have hH : AnalyticAt ℂ (fun w : ℂ => H 0 (2 * (Real.pi : ℂ)^2 * w^2)) 0 := by
    exact ((H_differentiable 0).analyticAt _).comp harg
  have hH0 : H 0 (2 * (Real.pi : ℂ)^2 * (0 : ℂ)^2) ≠ 0 := by
    simp [H_zero, derivX_zero]
  exact analyticAt_const.mul ((hH.inv hH0).pow h)

lemma instantonIntegrand_factor (h k m : ℕ) (hdeg : 3*h = 2*k + 2*m + 1)
    (w : ℂ) (hw : w ≠ 0) :
    instantonIntegrand h k w = instantonHolomorphicFactor h w / w^(2*m+1) := by
  unfold instantonIntegrand instantonHolomorphicFactor
  rw [instantonAction_eq_H]
  calc
    _ = (3/2 : ℂ)^h * (H 0 (2 * (Real.pi : ℂ)^2 * w^2))⁻¹^h *
        (w^(2*k) / w^(3*h)) := by
      simp only [mul_inv, mul_pow, inv_pow, ← pow_mul]
      rw [← inv_pow (2/3 : ℂ) h, show (2/3 : ℂ)⁻¹ = 3/2 by norm_num]
      ring
    _ = _ := by
      rw [hdeg, show 2*k+2*m+1 = 2*k+(2*m+1) by omega, pow_add]
      field_simp

theorem instanton_normalizedCircleIntegral (h k m : ℕ) (hdeg : 3*h = 2*k + 2*m + 1) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), normalizedCircleIntegral (instantonIntegrand h k) R =
      (3/2 : ℂ)^h * (2 * (Real.pi : ℂ)^2)^m * (unscaledCoeff h m : ℂ) := by
  have hc := normalizedCircleIntegral_div_pow (instantonHolomorphicFactor h)
    (instantonHolomorphicFactor_analytic h) (2*m)
  filter_upwards [hc, self_mem_nhdsWithin] with R hR hRpos
  rw [normalizedCircleIntegral_congr_punctured _ _ (instantonIntegrand_factor h k m hdeg) R hRpos,
    hR]
  unfold instantonHolomorphicFactor
  rw [coeff_const_mul]
  have hH0 : H 0 0 ≠ 0 := by simp [H_zero, derivX_zero]
  have hfun : AnalyticAt ℂ (fun z : ℂ => (H 0 z)⁻¹^h) 0 :=
    (((H_differentiable 0).analyticAt 0).inv hH0).pow h
  rw [coeff_comp_scaled_square _ hfun, WP.Coefficients.unscaledCoeff_complex]
  ring

theorem instanton_residue (h k m : ℕ) (hdeg : 3*h = 2*k + 2*m + 1) :
    residueAtZero (instantonIntegrand h k) =
      (3/2 : ℂ)^h * (2 * (Real.pi : ℂ)^2)^m * (unscaledCoeff h m : ℂ) :=
  residueAtZero_eq_of_eventually _ _ (instanton_normalizedCircleIntegral h k m hdeg)

/-- A genuinely convergent Laurent expansion on a punctured disk. Its indices
are integers, and the residue exponent is exactly `-1` when `j=m`. -/
theorem instantonIntegrand_laurent_hasSum (h k m : ℕ)
    (hdeg : 3*h = 2*k + 2*m + 1) (w : ℂ) (hw : w ≠ 0)
    (hsmall : ‖2 * (Real.pi : ℂ)^2 * w^2‖ ≤ r 0) :
    HasSum (fun j : ℕ => (3/2 : ℂ)^h * (2 * (Real.pi : ℂ)^2)^j *
      (unscaledCoeff h j : ℂ) * w^(2*(j : ℤ) - (2*(m : ℤ)+1)))
      (instantonIntegrand h k w) := by
  have hs := (WP.Coefficients.unscaledCoeff_hasSum h
    (2 * (Real.pi : ℂ)^2 * w^2) hsmall).mul_left ((3/2 : ℂ)^h / w^(2*m+1))
  rw [instantonIntegrand_factor h k m hdeg w hw]
  unfold instantonHolomorphicFactor
  convert hs using 1
  · ext j
    rw [zpow_sub₀ hw]
    have hj : (2*(j : ℤ)) = (2*j : ℕ) := by omega
    have hm : (2*(m : ℤ)+1) = (2*m+1 : ℕ) := by omega
    rw [hj, hm]
    simp only [zpow_natCast, mul_pow, ← pow_mul]
    ring
  · ring

lemma instantonLaurent_residue_index (j m : ℕ) :
    (2*(j : ℤ) - (2*(m : ℤ)+1)) = -1 ↔ j = m := by omega

theorem instantonIntegrand_laurent_half_disk (h k m : ℕ)
    (hdeg : 3*h = 2*k + 2*m + 1) (w : ℂ) (hw : w ≠ 0)
    (hsmall : ‖w‖ ≤ 1/2) :
    HasSum (fun j : ℕ => (3/2 : ℂ)^h * (2 * (Real.pi : ℂ)^2)^j *
      (unscaledCoeff h j : ℂ) * w^(2*(j : ℤ) - (2*(m : ℤ)+1)))
      (instantonIntegrand h k w) := by
  apply instantonIntegrand_laurent_hasSum h k m hdeg w hw
  have hc : ‖2 * (Real.pi : ℂ)^2 * w^2‖ = 2 * Real.pi^2 * ‖w‖^2 := by
    simp [norm_pow, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc, WP.Coefficients.r_zero_value]
  have hs : ‖w‖^2 ≤ (1/2 : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hs)]

end WP.Analysis
