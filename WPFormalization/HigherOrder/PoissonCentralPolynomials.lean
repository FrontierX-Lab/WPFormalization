import WPFormalization.Analysis.GevreyOneLog
import WPFormalization.HigherOrder.Extraction
/-! Exact central polynomials from the paper's generating function
`exp(-k*t)*(1+t)^k`. The finite recipe, half-degree bound, zero positive-order
constant and uniform coefficient estimate are proved here. The normalized
Poisson coefficient operator identity and Lemma D.6's uniform analytic
remainder are separate obligations, not hypotheses of these statements. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def poissonCentralLog : Series := PowerSeries.log ℝ-PowerSeries.X

def poissonCentralPolynomial (m : ℕ) : Polynomial ℝ :=
  ∑ a ∈ Finset.range (m/2+1), Polynomial.monomial a
    ((m.factorial:ℝ)*PowerSeries.coeff m (poissonCentralLog^a)/(a.factorial:ℝ))

lemma poissonCentralLog_div_X_two : ∃ Q : Series, poissonCentralLog=PowerSeries.X^2*Q := by
  have h0 : PowerSeries.constantCoeff poissonCentralLog=0 := by simp [poissonCentralLog]
  obtain ⟨Q,hQ⟩ := PowerSeries.X_dvd_iff.mpr h0
  have h1 : PowerSeries.coeff 1 poissonCentralLog=0 := by norm_num [poissonCentralLog,PowerSeries.coeff_log]
  have hQ0 : PowerSeries.constantCoeff Q=0 := by
    have ht := congrArg (PowerSeries.coeff 1) hQ
    rw [h1] at ht
    simpa using ht.symm
  obtain ⟨R,hR⟩ := PowerSeries.X_dvd_iff.mpr hQ0
  refine ⟨R,?_⟩
  rw [hQ,hR]
  ring

lemma poissonCentralLog_pow_coeff_zero (m a : ℕ) (h : m < 2*a) :
    PowerSeries.coeff m (poissonCentralLog^a)=0 := by
  obtain ⟨Q,hQ⟩ := poissonCentralLog_div_X_two
  rw [hQ,mul_pow,←pow_mul,PowerSeries.coeff_X_pow_mul',ite_eq_right (by omega)]

lemma poissonCentralPolynomial_natDegree (m : ℕ) :
    (poissonCentralPolynomial m).natDegree ≤ m/2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  exact (Polynomial.natDegree_monomial_le _).trans (by have ht := Finset.mem_range.mp ha;omega)

@[simp] lemma poissonCentralPolynomial_zero : poissonCentralPolynomial 0=1 := by
  simp [poissonCentralPolynomial]

@[simp] lemma poissonCentralPolynomial_one : poissonCentralPolynomial 1=0 := by
  simp [poissonCentralPolynomial]

lemma poissonCentralPolynomial_constant (m : ℕ) (hm : 1 ≤ m) :
    (poissonCentralPolynomial m).coeff 0=0 := by
  simp only [poissonCentralPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases ha0 : a=0
  · subst a
    simp [PowerSeries.coeff_one,show m ≠ 0 by omega]
  · simp [ha0]

lemma poissonCentralPolynomial_eval_full (m : ℕ) (k : ℝ) :
    (poissonCentralPolynomial m).eval k=
      (m.factorial:ℝ)*∑ a ∈ Finset.range (m+1),PowerSeries.coeff m (poissonCentralLog^a)*k^a/(a.factorial:ℝ) := by
  simp only [poissonCentralPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,Finset.mul_sum]
  rw [Finset.sum_subset (show Finset.range (m/2+1) ⊆ Finset.range (m+1) by intro a ha;simp only [Finset.mem_range] at ha ⊢;omega)]
  · apply Finset.sum_congr rfl
    intro a ha
    ring
  · intro a ha hnot
    have hn : m < 2*a := by simp only [Finset.mem_range] at hnot;omega
    rw [poissonCentralLog_pow_coeff_zero m a hn]
    simp
end WP.HigherOrder
namespace WP.HigherOrder
open PowerSeries Filter
open scoped Topology
lemma poissonCentralPolynomial_generating_real (m : ℕ) (k : ℝ) :
    (((poissonCentralPolynomial m).eval k:ℝ):ℂ)=
      (m.factorial:ℂ)*WP.coeff (fun z : ℂ => Complex.exp ((k:ℂ)*(Complex.log (1+z)-z))) m := by
  let q : ℂ → ℂ := fun z => (k:ℂ)*(Complex.log (1+z)-z)
  have hunit : AnalyticAt ℂ (fun z : ℂ => 1+z) 0 := analyticAt_const.add analyticAt_id
  have hplane : (fun z : ℂ => 1+z) 0 ∈ Complex.slitPlane := by simp
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (1+z)) 0 := (analyticAt_clog hplane).comp hunit
  have hq : AnalyticAt ℂ q 0 := analyticAt_const.mul (hlog.sub analyticAt_id)
  have hq0 : q 0=0 := by simp [q]
  have ht : Analysis.taylor q=PowerSeries.C (k:ℂ)*PowerSeries.map Complex.ofRealHom poissonCentralLog := by
    rw [Analysis.taylor_const_mul,Analysis.taylor_sub (g := fun z : ℂ => z) hlog analyticAt_id,
      Analysis.taylor_log_comp_unit _ hunit (by simp),Analysis.taylor_add (g := fun z : ℂ => z) analyticAt_const analyticAt_id,
      Analysis.taylor_const,Analysis.taylor_id,map_one,PowerSeries.logOf_one_add_X]
    rw [poissonCentralLog,map_sub,PowerSeries.map_log,PowerSeries.map_X]
  have hp (a : ℕ) : PowerSeries.coeff m ((Analysis.taylor q)^a)=
      (k:ℂ)^a*((PowerSeries.coeff m (poissonCentralLog^a):ℝ):ℂ) := by
    rw [ht,mul_pow,←map_pow,PowerSeries.coeff_C_mul,←map_pow,PowerSeries.coeff_map]
    rfl
  have he : WP.coeff (fun z : ℂ => Complex.exp (q z)) m=
      ((∑ a ∈ Finset.range (m+1),PowerSeries.coeff m (poissonCentralLog^a)*k^a/(a.factorial:ℝ)):ℂ) := by
    rw [Analysis.taylor_exp_coeff_finite q hq hq0]
    simp_rw [hp]
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    ring
  change (((poissonCentralPolynomial m).eval k:ℝ):ℂ)=(m.factorial:ℂ)*WP.coeff (fun z : ℂ => Complex.exp (q z)) m
  rw [he,poissonCentralPolynomial_eval_full]
  push_cast
  rfl

lemma poissonCentralPolynomial_generating_nat (m k : ℕ) :
    (((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)=
      (m.factorial:ℂ)*WP.coeff (fun z : ℂ => Complex.exp (-(k:ℂ)*z)*(1+z)^k) m := by
  have heq : (fun z : ℂ => Complex.exp (((k:ℝ):ℂ)*(Complex.log (1+z)-z))) =ᶠ[𝓝 0]
      (fun z : ℂ => Complex.exp (-(k:ℂ)*z)*(1+z)^k) := by
    have hp : ContinuousAt (fun z : ℂ => 1+z) 0 := by fun_prop
    filter_upwards [hp.eventually_ne (by simp : (1:ℂ)+(0:ℂ) ≠ 0)] with z hz
    push_cast
    rw [show (k:ℂ)*(Complex.log (1+z)-z)=-(k:ℂ)*z+(k:ℂ)*Complex.log (1+z) by ring,
      Complex.exp_add,Complex.exp_nat_mul,Complex.exp_log hz]
  rw [poissonCentralPolynomial_generating_real,Analysis.coeff_congr_of_eventuallyEq _ _ heq]
end WP.HigherOrder
namespace WP.HigherOrder
open PowerSeries
lemma poissonCentralLog_complex_taylor :
    Analysis.taylor (fun z : ℂ => Complex.log (1+z)-z)=PowerSeries.map Complex.ofRealHom poissonCentralLog := by
  have hunit : AnalyticAt ℂ (fun z : ℂ => 1+z) 0 := analyticAt_const.add analyticAt_id
  have hplane : (fun z : ℂ => 1+z) 0 ∈ Complex.slitPlane := by simp
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (1+z)) 0 := (analyticAt_clog hplane).comp hunit
  rw [Analysis.taylor_sub (g := fun z : ℂ => z) hlog analyticAt_id,
    Analysis.taylor_log_comp_unit _ hunit (by simp),
    Analysis.taylor_add (g := fun z : ℂ => z) analyticAt_const analyticAt_id,
    Analysis.taylor_const,Analysis.taylor_id,map_one,PowerSeries.logOf_one_add_X,
    poissonCentralLog,map_sub,PowerSeries.map_log,PowerSeries.map_X]

lemma poissonCentralLog_pow_coeff_abs (m a : ℕ) :
    |PowerSeries.coeff m (poissonCentralLog^a)| ≤ (2:ℝ)^m := by
  let f : ℂ → ℂ := fun z => (Complex.log (1+z)-z)^a
  have ha (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) (1/2:ℝ)) : AnalyticAt ℂ f z := by
    have hn : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hplane : (1+z) ∈ Complex.slitPlane := by
      apply Analysis.slitPlane_of_norm_sub_one_half
      simpa only [add_sub_cancel_left] using hn
    exact (((analyticAt_clog hplane).comp (analyticAt_const.add analyticAt_id)).sub analyticAt_id).pow a
  have hbound (z : ℂ) (hz : z ∈ Metric.sphere (0:ℂ) (1/2:ℝ)) : ‖f z‖ ≤ 1 := by
    have hn : ‖z‖=1/2 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    have hlog := Complex.norm_log_one_add_sub_self_le (show ‖z‖ < 1 by rw [hn];norm_num)
    rw [hn] at hlog
    norm_num at hlog
    have hu : ‖Complex.log (1+z)-z‖ ≤ 1 := by linarith
    simpa only [f,norm_pow,one_pow] using pow_le_pow_left₀ (norm_nonneg _) hu a
  have hc := Analysis.coeff_norm_le_circle_bound f (1/2) 1 (by norm_num)
    (fun z hz => (ha z hz).differentiableAt.differentiableWithinAt) hbound m
  have hco : WP.coeff f m=((PowerSeries.coeff m (poissonCentralLog^a):ℝ):ℂ) := by
    have hz : (0:ℂ) ∈ Metric.closedBall (0:ℂ) (1/2:ℝ) := by simp
    have hl : AnalyticAt ℂ (fun z : ℂ => Complex.log (1+z)-z) 0 := by
      have hp : (fun z : ℂ => 1+z) 0 ∈ Complex.slitPlane := by simp
      exact ((analyticAt_clog hp).comp (analyticAt_const.add analyticAt_id)).sub analyticAt_id
    rw [←Analysis.taylor_coeff,Analysis.taylor_pow hl,poissonCentralLog_complex_taylor,←map_pow,PowerSeries.coeff_map]
    rfl
  rw [hco,Complex.norm_real,Real.norm_eq_abs] at hc
  convert hc using 1
  rw [div_pow,one_pow,one_div_div,div_one]

lemma poissonCentralPolynomial_coeff_abs (m a : ℕ) :
    |(poissonCentralPolynomial m).coeff a| ≤ (2:ℝ)^m*(m.factorial:ℝ)/(a.factorial:ℝ) := by
  have hcoef : (poissonCentralPolynomial m).coeff a=
      if a ≤ m/2 then (m.factorial:ℝ)*PowerSeries.coeff m (poissonCentralLog^a)/(a.factorial:ℝ) else 0 := by
    simp only [poissonCentralPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
      Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]
  rw [hcoef]
  split_ifs
  · rw [abs_div,abs_of_pos (by positivity : (0 : ℝ) < a.factorial),abs_mul,abs_of_pos (by positivity : (0 : ℝ) < m.factorial)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc _ ≤ (m.factorial:ℝ)*(2:ℝ)^m := mul_le_mul_of_nonneg_left (poissonCentralLog_pow_coeff_abs m a) (by positivity)
         _ = _ := by ring
  · simp only [abs_zero]
    positivity
end WP.HigherOrder
