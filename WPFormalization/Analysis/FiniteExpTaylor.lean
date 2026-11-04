import WPFormalization.Analysis.Taylor
import WPFormalization.HigherOrder.FiniteSeries
/-! Exact finite Taylor coefficients of exponentials with zero constant exponent. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma linear_differential_series_unique (U V A : PowerSeries ℂ)
    (hU : PowerSeries.derivative U=U*A) (hV : PowerSeries.derivative V=V*A)
    (h0 : PowerSeries.constantCoeff U=PowerSeries.constantCoeff V) : U=V := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have hu := congrArg (PowerSeries.coeff n) hU
      have hv := congrArg (PowerSeries.coeff n) hV
      rw [PowerSeries.coeff_derivative] at hu hv
      have hs : PowerSeries.coeff n (U*A)=PowerSeries.coeff n (V*A) := by
        rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro i hi
        have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
        rw [ih i.1 (by omega)]
      have hn : (n:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
      exact mul_right_cancel₀ hn (hu.trans (hs.trans hv.symm))

lemma taylor_exp_comp_zero (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (h0 : f 0=0) :
    taylor (fun z=>Complex.exp (f z))=(PowerSeries.exp ℂ).subst (taylor f) := by
  have hE : AnalyticAt ℂ (fun z=>Complex.exp (f z)) 0 := by fun_prop
  have hder : deriv (fun z=>Complex.exp (f z)) =ᶠ[𝓝 0] (fun z=>Complex.exp (f z)*deriv f z) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    exact ((Complex.hasDerivAt_exp (f z)).comp z hz.differentiableAt.hasDerivAt).deriv
  have hU : PowerSeries.derivative (taylor (fun z=>Complex.exp (f z)))=
      taylor (fun z=>Complex.exp (f z))*PowerSeries.derivative (taylor f) := by
    rw [←taylor_deriv,taylor_congr hder,taylor_mul hE hf.deriv,taylor_deriv]
  have hP0 : PowerSeries.constantCoeff (taylor f)=0 := by rw [taylor_constant,h0]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hP0
  have hV : PowerSeries.derivative ((PowerSeries.exp ℂ).subst (taylor f))=
      ((PowerSeries.exp ℂ).subst (taylor f))*PowerSeries.derivative (taylor f) := by
    rw [PowerSeries.derivative_subst hs,PowerSeries.derivative_exp]
  apply linear_differential_series_unique _ _ _ hU hV
  rw [taylor_constant,h0,Complex.exp_zero]
  have hc : PowerSeries.constantCoeff ((PowerSeries.exp ℂ).subst (taylor f))=
      PowerSeries.constantCoeff (PowerSeries.exp ℂ) :=
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero hP0 (PowerSeries.exp ℂ)
  exact (hc.trans PowerSeries.constantCoeff_exp).symm

lemma exp_subst_coeff_finite (P : PowerSeries ℂ) (hP : PowerSeries.constantCoeff P=0) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℂ).subst P)=
      ∑k∈Finset.range (n+1),PowerSeries.coeff n (P^k)/(k.factorial:ℂ) := by
  have hz (k : ℕ) (hnk : n<k) : PowerSeries.coeff n (P^k)=0 := by
    obtain ⟨Q,hQ⟩ := PowerSeries.X_dvd_iff.mpr hP
    rw [hQ,mul_pow,PowerSeries.coeff_X_pow_mul',ite_eq_right (by omega)]
  have hs : Function.support (fun k:ℕ=>PowerSeries.coeff k (PowerSeries.exp ℂ) • PowerSeries.coeff n (P^k))⊆
      (Finset.range (n+1):Set ℕ) := by
    intro k hk
    by_contra hn
    have hnk : n<k := by
      have hnot : ¬k<n+1 := by simpa only [Finset.mem_coe,Finset.mem_range] using hn
      omega
    exact hk (by dsimp only;rw [hz k hnk,smul_zero])
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hP),finsum_eq_sum_of_support_subset _ hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [PowerSeries.coeff_exp,smul_eq_mul,map_inv₀,map_natCast,one_div]
  ring

lemma taylor_exp_coeff_finite (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (h0 : f 0=0) (n : ℕ) :
    WP.coeff (fun z=>Complex.exp (f z)) n=
      ∑k∈Finset.range (n+1),PowerSeries.coeff n ((taylor f)^k)/(k.factorial:ℂ) := by
  rw [←taylor_coeff,taylor_exp_comp_zero f hf h0]
  exact exp_subst_coeff_finite _ (by rw [taylor_constant,h0]) n


lemma coeff_pow_eq_of_coeff_eq {R : Type*} [Semiring R] (f g : PowerSeries R) (N : ℕ)
    (hfg : ∀n:ℕ,n≤N → PowerSeries.coeff n f=PowerSeries.coeff n g)
    (j n : ℕ) (hn : n≤N) : PowerSeries.coeff n (f^j)=PowerSeries.coeff n (g^j) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ,pow_succ,PowerSeries.coeff_mul,PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    rw [ih i.1 (by omega),hfg i.2 (by omega)]

lemma finiteExp_coeff_congr (f g : WP.HigherOrder.Series) (N : ℕ)
    (hfg : ∀n:ℕ,n≤N → PowerSeries.coeff n f=PowerSeries.coeff n g) :
    PowerSeries.coeff N (WP.HigherOrder.finiteExp f)=PowerSeries.coeff N (WP.HigherOrder.finiteExp g) := by
  simp only [WP.HigherOrder.finiteExp,PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_pow_eq_of_coeff_eq f g N hfg j N le_rfl]

lemma taylor_exp_coeff_of_real_jets (f : WP.HigherOrder.Series) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g 0) (h0 : g 0=0) (N : ℕ)
    (hjets : ∀i:ℕ,i≤N → WP.coeff g i=((PowerSeries.coeff i f:ℝ):ℂ))
    (n : ℕ) (hn : n≤N) :
    WP.coeff (fun z=>Complex.exp (g z)) n=
      ((PowerSeries.coeff n (WP.HigherOrder.finiteExp f):ℝ):ℂ) := by
  have hs : ∀i:ℕ,i≤N → PowerSeries.coeff i (taylor g)=
      PowerSeries.coeff i (PowerSeries.map Complex.ofRealHom f) := by
    intro i hi
    simpa only [taylor_coeff,PowerSeries.coeff_map,Complex.ofRealHom_eq_coe] using hjets i hi
  rw [taylor_exp_coeff_finite g hg h0]
  calc
    _ = ∑j∈Finset.range (n+1),((PowerSeries.coeff n (f^j):ℝ):ℂ)/(j.factorial:ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_pow_eq_of_coeff_eq _ _ N hs j n hn,←map_pow,PowerSeries.coeff_map]
      rfl
    _ = _ := by
      simp only [WP.HigherOrder.finiteExp,PowerSeries.coeff_mk]
      push_cast
      rfl


lemma taylor_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀i∈s,AnalyticAt ℂ (f i) 0) :
    taylor (fun z=>∑i∈s,f i z)=∑i∈s,taylor (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,taylor_const,map_zero]
  | @insert i s hi ih =>
    have hsum : AnalyticAt ℂ (fun z=>∑j∈s,f j z) 0 := by
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)
    have he : (fun z=>∑j∈insert i s,f j z)=(fun z=>f i z+∑j∈s,f j z) := by
      funext z
      rw [Finset.sum_insert hi]
    rw [he,taylor_add (hf i (Finset.mem_insert_self _ _)) hsum,Finset.sum_insert hi,
      ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))]

lemma taylor_monomial (c : ℂ) (j : ℕ) :
    taylor (fun z=>c*z^j)=PowerSeries.C c*PowerSeries.X^j := by
  rw [taylor_const_mul,taylor_pow (f:=fun z:ℂ=>z) analyticAt_id j,taylor_id]

def truncatedSeriesPolynomial (f : WP.HigherOrder.Series) (K : ℕ) (z : ℂ) : ℂ :=
  ∑j∈Finset.range (K+1),((PowerSeries.coeff j f:ℝ):ℂ)*z^j

lemma truncatedSeriesPolynomial_analytic (f : WP.HigherOrder.Series) (K : ℕ) (z : ℂ) :
    AnalyticAt ℂ (truncatedSeriesPolynomial f K) z := by
  unfold truncatedSeriesPolynomial
  apply Finset.analyticAt_fun_sum
  intro j hj
  fun_prop

lemma truncatedSeriesPolynomial_coeff (f : WP.HigherOrder.Series) (K n : ℕ) :
    WP.coeff (truncatedSeriesPolynomial f K) n=
      if n≤K then ((PowerSeries.coeff n f:ℝ):ℂ) else 0 := by
  have ht := taylor_finset_sum (Finset.range (K+1))
    (fun j z=>((PowerSeries.coeff j f:ℝ):ℂ)*z^j) (by intro j hj;fun_prop)
  have hc := congrArg (PowerSeries.coeff n) ht
  change WP.coeff (fun z=>∑j∈Finset.range (K+1),((PowerSeries.coeff j f:ℝ):ℂ)*z^j) n = _
  simpa only [taylor_coeff,map_sum,taylor_monomial,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_range,Nat.lt_succ_iff] using hc

lemma truncatedSeriesPolynomial_zero (f : WP.HigherOrder.Series) (hf : PowerSeries.constantCoeff f=0) (K : ℕ) :
    truncatedSeriesPolynomial f K 0=0 := by
  have hc := truncatedSeriesPolynomial_coeff f K 0
  simpa only [WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,
    ite_eq_left (Nat.zero_le K),PowerSeries.coeff_zero_eq_constantCoeff,hf,Complex.ofReal_zero] using hc

lemma finiteExp_truncated_polynomial_coeff (f : WP.HigherOrder.Series)
    (hf : PowerSeries.constantCoeff f=0) (K n : ℕ) (hn : n≤K) :
    WP.coeff (fun z=>Complex.exp (truncatedSeriesPolynomial f K z)) n=
      ((PowerSeries.coeff n (WP.HigherOrder.finiteExp f):ℝ):ℂ) := by
  apply taylor_exp_coeff_of_real_jets f (truncatedSeriesPolynomial f K)
    (truncatedSeriesPolynomial_analytic f K 0) (truncatedSeriesPolynomial_zero f hf K) K _ n hn
  intro i hi
  rw [truncatedSeriesPolynomial_coeff,ite_eq_left hi]


end WP.Analysis
