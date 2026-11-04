import WPFormalization.Coefficients.InstantonCorrespondence
import WPFormalization.Analysis.WPInstantonResidue
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The boundary-length coefficient of the actual instanton contour expression.
The small-circle integral is first proved to be a polynomial in the boundary
length. `dslope` supplies its genuine removable division by that length at zero;
coefficients are then ordinary derivative-defined Taylor coefficients. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

lemma analyticAt_dslope_zero (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (dslope f 0) 0 := by
  obtain ⟨p,hp⟩ := hf
  exact hp.has_fpower_series_dslope_fslope.analyticAt

lemma coeff_dslope_zero (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    WP.coeff (dslope f 0) n = WP.coeff f (n+1) := by
  have hd := analyticAt_dslope_zero f hf
  have he : (fun z : ℂ => z * dslope f 0 z) = (fun z => f z - f 0) := by
    funext z
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope f 0 z
  have hc := coeff_id_pow_mul (dslope f 0) hd 1 (n+1)
  simp only [pow_one, ite_eq_left (by omega : 1 ≤ n+1), Nat.add_sub_cancel] at hc
  rw [he] at hc
  have hs := congrArg (PowerSeries.coeff (n+1)) (taylor_sub hf (analyticAt_const (v := f 0)))
  simp only [taylor_coeff, map_sub, taylor_const, PowerSeries.coeff_C,
    ite_eq_right (Nat.succ_ne_zero n), sub_zero] at hs
  exact hc.symm.trans hs

lemma coeff_exp_mul (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (L : ℂ) (N : ℕ) :
    WP.coeff (fun w => Complex.exp (L*w) * F w) N =
      ∑ i ∈ Finset.range (N+1), WP.coeff F (N-i)/(i.factorial : ℂ)*L^i := by
  have he : AnalyticAt ℂ (fun w : ℂ => Complex.exp (L*w)) 0 := by fun_prop
  have hc := congrArg (PowerSeries.coeff N) (taylor_mul he hF)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [taylor_coeff] at hc
  rw [hc]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [WP.coeff, iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one]
  ring

/-- The normalized small-circle integral before dividing by the boundary length. -/
def instantonContourNumerator (h : ℕ) (L : ℂ) : ℂ :=
  residueAtZero (fun w => Complex.exp (L*w)/(w*(instantonAction w)^h))

lemma instantonContour_integrand_factor (h : ℕ) (L w : ℂ) (_hw : w ≠ 0) :
    Complex.exp (L*w)/(w*(instantonAction w)^h) =
      (Complex.exp (L*w)*instantonHolomorphicFactor h w)/w^(3*h+1) := by
  rw [instantonAction_eq_H]
  unfold instantonHolomorphicFactor
  simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow, pow_add, pow_one, ← pow_mul]
  simp only [inv_inv]
  ring

lemma instantonContourNumerator_eq_coeff (h : ℕ) (L : ℂ) :
    instantonContourNumerator h L =
      WP.coeff (fun w => Complex.exp (L*w)*instantonHolomorphicFactor h w) (3*h) := by
  unfold instantonContourNumerator
  rw [residueAtZero_congr_punctured _ _ (instantonContour_integrand_factor h L)]
  exact residueAtZero_div_pow _
    ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (L*w)) 0).mul
      (instantonHolomorphicFactor_analytic h)) (3*h)

/-- One radius bound works for every complex boundary length. In particular
the same actual contour can be held fixed while taking Taylor coefficients. -/
theorem instantonContour_small_circles (h : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioo (0 : ℝ) ε, ∀ L : ℂ,
      normalizedCircleIntegral
        (fun w => Complex.exp (L*w)/(w*(instantonAction w)^h)) R =
        instantonContourNumerator h L := by
  obtain ⟨ε,hε,ha⟩ := Metric.eventually_nhds_iff.mp
    (instantonHolomorphicFactor_analytic h).eventually_analyticAt
  refine ⟨ε,hε,?_⟩
  intro R hR L
  have hF : DifferentiableOn ℂ (instantonHolomorphicFactor h) (Metric.closedBall 0 R) := by
    intro w hw
    exact (ha (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hR.2)).differentiableAt.differentiableWithinAt
  have hExp : Differentiable ℂ (fun w : ℂ => Complex.exp (L*w)) := by fun_prop
  have hD : DifferentiableOn ℂ
      (fun w => Complex.exp (L*w)*instantonHolomorphicFactor h w)
      (Metric.closedBall 0 R) := hExp.differentiableOn.mul hF
  have hc := hD.circleIntegral_one_div_sub_center_pow_smul hR.1 (3*h)
  have he : (fun w : ℂ => (1/(w-0)^(3*h+1)) •
      (Complex.exp (L*w)*instantonHolomorphicFactor h w)) =
      (fun w => (Complex.exp (L*w)*instantonHolomorphicFactor h w)/w^(3*h+1)) := by
    funext w
    simp [div_eq_mul_inv,mul_comm]
  rw [he] at hc
  rw [normalizedCircleIntegral_congr_punctured _ _
      (instantonContour_integrand_factor h L) R hR.1,
    instantonContourNumerator_eq_coeff]
  unfold normalizedCircleIntegral WP.coeff
  rw [hc]
  simp only [smul_eq_mul]
  have hp := Complex.two_pi_I_ne_zero
  field_simp

lemma instantonContourNumerator_polynomial (h : ℕ) (L : ℂ) :
    instantonContourNumerator h L = ∑ i ∈ Finset.range (3*h+1),
      WP.coeff (instantonHolomorphicFactor h) (3*h-i)/(i.factorial : ℂ)*L^i := by
  rw [instantonContourNumerator_eq_coeff, coeff_exp_mul _ (instantonHolomorphicFactor_analytic h)]

lemma instantonContourNumerator_analytic (h : ℕ) (L : ℂ) :
    AnalyticAt ℂ (instantonContourNumerator h) L := by
  have he : instantonContourNumerator h = fun L => ∑ i ∈ Finset.range (3*h+1),
      WP.coeff (instantonHolomorphicFactor h) (3*h-i)/(i.factorial : ℂ)*L^i :=
    funext (instantonContourNumerator_polynomial h)
  rw [he]
  fun_prop

lemma instantonContourNumerator_coeff (h n : ℕ) (hn : n ≤ 3*h) :
    WP.coeff (instantonContourNumerator h) n =
      WP.coeff (instantonHolomorphicFactor h) (3*h-n)/(n.factorial : ℂ) := by
  have he : instantonContourNumerator h = fun L => ∑ i ∈ Finset.range (3*h+1),
      WP.coeff (instantonHolomorphicFactor h) (3*h-i)/(i.factorial : ℂ)*L^i :=
    funext (instantonContourNumerator_polynomial h)
  rw [he, coeff_finite_sum _ _ (fun i _ => by fun_prop)]
  simp_rw [coeff_const_mul, coeff_pow]
  simp [Finset.mem_range, Nat.lt_succ_iff.mpr hn]

lemma coeff_even_function_odd (F : ℂ → ℂ) (hEven : ∀ w, F (-w)=F w)
    (n : ℕ) (hn : Odd n) : WP.coeff F n = 0 := by
  have hd := iteratedDeriv_comp_neg n F (0 : ℂ)
  have he : (fun w => F (-w))=F := funext hEven
  rw [he, neg_zero, hn.neg_one_pow] at hd
  simp only [neg_one_smul] at hd
  have hz : iteratedDeriv n F 0 = 0 := by linear_combination (1/2 : ℂ)*hd
  simp [WP.coeff, hz]

lemma instantonContourNumerator_zero (h : ℕ) (hh : Odd h) :
    instantonContourNumerator h 0 = 0 := by
  rw [instantonContourNumerator_eq_coeff]
  simp only [zero_mul, Complex.exp_zero, one_mul]
  apply coeff_even_function_odd
  · intro w
    simp only [instantonHolomorphicFactor, neg_sq]
  · exact Odd.mul (by decide : Odd 3) hh

/-- Analytic removal of the boundary-length denominator. The value at zero is
the derivative of the independently defined contour numerator. -/
def instantonContourAmplitude (h : ℕ) (L : ℂ) : ℂ :=
  (Real.Gamma h : ℂ) * dslope (instantonContourNumerator h) 0 L

lemma instantonContourAmplitude_analytic (h : ℕ) :
    AnalyticAt ℂ (instantonContourAmplitude h) 0 :=
  analyticAt_const.mul (analyticAt_dslope_zero _ (instantonContourNumerator_analytic h 0))

lemma instantonContourAmplitude_of_ne (h : ℕ) (hh : Odd h) (L : ℂ) (hL : L ≠ 0) :
    instantonContourAmplitude h L = (Real.Gamma h : ℂ)/L *
      residueAtZero (fun w => Complex.exp (L*w)/(w*(instantonAction w)^h)) := by
  rw [instantonContourAmplitude, dslope_of_ne _ hL, slope_def_field,
    instantonContourNumerator_zero h hh]
  simp only [sub_zero, instantonContourNumerator]
  ring

lemma instantonIntegrand_residue_coeff (h k m : ℕ) (hdeg : 3*h=2*k+2*m+1) :
    residueAtZero (instantonIntegrand h k) =
      WP.coeff (instantonHolomorphicFactor h) (2*m) := by
  rw [residueAtZero_congr_punctured _ _ (instantonIntegrand_factor h k m hdeg)]
  exact residueAtZero_div_pow _ (instantonHolomorphicFactor_analytic h) (2*m)

/-- The precise coefficient assertion following the contour expression in
§13.7, using the genuine analytic removal at L=0 and circular residue. -/
theorem instantonContourAmplitude_coefficient (h k m : ℕ)
    (hdeg : 3*h=2*k+2*m+1) :
    ((2*k+1).factorial : ℂ) * WP.coeff (instantonContourAmplitude h) (2*k) =
      (Real.Gamma h : ℂ) * residueAtZero (instantonIntegrand h k) := by
  unfold instantonContourAmplitude
  rw [coeff_const_mul,
    coeff_dslope_zero _ (instantonContourNumerator_analytic h 0),
    instantonContourNumerator_coeff h (2*k+1) (by omega),
    show 3*h-(2*k+1)=2*m by omega, instantonIntegrand_residue_coeff h k m hdeg]
  have hf : ((2*k+1).factorial : ℂ) ≠ 0 := by exact_mod_cast (2*k+1).factorial_ne_zero
  field_simp

/-- The unnormalized contour convention used in the paper. -/
def instantonRawContourAmplitude (h : ℕ) (L : ℂ) : ℂ :=
  (2*(Real.pi : ℂ)*Complex.I) * instantonContourAmplitude h L

lemma instantonRawContourAmplitude_analytic (h : ℕ) :
    AnalyticAt ℂ (instantonRawContourAmplitude h) 0 :=
  analyticAt_const.mul (instantonContourAmplitude_analytic h)

/-- Away from zero the analytic extension agrees with the literal Γ(h)/L
circle integral, for any sufficiently small fixed positive circle. -/
theorem instantonRawContourAmplitude_eq_circle (h : ℕ) (hh : Odd h) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioo (0 : ℝ) ε, ∀ L : ℂ, L ≠ 0 →
      instantonRawContourAmplitude h L = (Real.Gamma h : ℂ)/L *
        ∮ w in C(0,R), Complex.exp (L*w)/(w*(instantonAction w)^h) := by
  obtain ⟨ε,hε,hcircle⟩ := instantonContour_small_circles h
  refine ⟨ε,hε,?_⟩
  intro R hR L hL
  rw [instantonRawContourAmplitude, instantonContourAmplitude_of_ne h hh L hL]
  change (2*(Real.pi : ℂ)*Complex.I)*((Real.Gamma h : ℂ)/L *
    instantonContourNumerator h L) = _
  rw [← hcircle R hR L, normalizedCircleIntegral]
  have hp := Complex.two_pi_I_ne_zero
  field_simp

/-- The proportionality factor for the paper's unnormalized contour is
exactly 2πi, independent of the boundary coefficient degree. -/
theorem instantonRawContourAmplitude_coefficient (h k m : ℕ)
    (hdeg : 3*h=2*k+2*m+1) :
    ((2*k+1).factorial : ℂ) * WP.coeff (instantonRawContourAmplitude h) (2*k) =
      (2*(Real.pi : ℂ)*Complex.I) * (Real.Gamma h : ℂ) *
        residueAtZero (instantonIntegrand h k) := by
  unfold instantonRawContourAmplitude
  rw [coeff_const_mul]
  calc
    _ = (2*(Real.pi : ℂ)*Complex.I) *
        (((2*k+1).factorial : ℂ) * WP.coeff (instantonContourAmplitude h) (2*k)) := by ring
    _ = _ := by rw [instantonContourAmplitude_coefficient h k m hdeg]; ring

/- The actual original boundary-length contour, its analytic removal at zero,
and the coefficient/residue dictionary with both contour conventions. The
radius is chosen before every complex length and every coefficient degree. -/
@[blueprint "eq:instanton-correspondence"]
theorem instanton_contour_coefficient_dictionary (g : ℕ) (hg : 1 ≤ g) :
    AnalyticAt ℂ (instantonRawContourAmplitude (complexity g 1)) 0 ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioo (0 : ℝ) ε, ∀ L : ℂ, L ≠ 0 →
      instantonRawContourAmplitude (complexity g 1) L =
        (Real.Gamma (complexity g 1) : ℂ)/L *
          ∮ w in C(0,R), Complex.exp (L*w)/(w*(instantonAction w)^(complexity g 1))) ∧
    (∀ k : ℕ, k ≤ 3*g-2 →
      ((2*k+1).factorial : ℂ) * WP.coeff (instantonContourAmplitude (complexity g 1)) (2*k) =
        (Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k)) ∧
    (∀ k : ℕ, k ≤ 3*g-2 →
      ((2*k+1).factorial : ℂ) * WP.coeff (instantonRawContourAmplitude (complexity g 1)) (2*k) =
        (2*(Real.pi : ℂ)*Complex.I) * (Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k)) := by
  have hh : Odd (complexity g 1) := by
    refine ⟨g-1,?_⟩
    unfold complexity
    omega
  refine ⟨instantonRawContourAmplitude_analytic _,
    instantonRawContourAmplitude_eq_circle _ hh,?_,?_⟩
  · intro k hk
    apply instantonContourAmplitude_coefficient (complexity g 1) k (3*g-2-k)
    unfold complexity
    omega
  · intro k hk
    apply instantonRawContourAmplitude_coefficient (complexity g 1) k (3*g-2-k)
    unfold complexity
    omega

end WP.Analysis
