import WPFormalization.Analysis.FactorialTail
/-! Uniform finite loss-power tails and absorption of macroscopic exponential decay for every truncation loss L <= sqrt(h). These are real scalar estimates with no paper-specific hypotheses. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma shifted_power_step_exp (x : ℝ) (r : ℕ) (hx : 0 < x) (hr : (r:ℝ) ≤ x) :
    (x+1)^r ≤ Real.exp 1*x^r := by
  have hu : 1+1/x ≤ Real.exp (1/x) := by linarith [Real.add_one_le_exp (1/x)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+1/x) hu r
  have hp : (1+1/x)^r ≤ Real.exp ((r:ℝ)/x) := by
    simpa only [←Real.exp_nat_mul,div_eq_mul_inv,one_mul] using hpow
  have he : Real.exp ((r:ℝ)/x) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((div_le_one hx).mpr hr)
  calc
    _ = x^r*(1+1/x)^r := by rw [←mul_pow];congr 1;field_simp
    _ ≤ x^r*Real.exp 1 := mul_le_mul_of_nonneg_left (hp.trans he) (by positivity)
    _ = _ := by ring

lemma loss_power_successor (p B h : ℝ) (r : ℕ) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hh : 0 < h) (hr : 1 ≤ r) :
    (B*(p+(r+1:ℕ))/h)^(r+1) ≤
      (Real.exp 1*B*(p+r+1)/h)*(B*(p+r)/h)^r := by
  have hx : 0 < p+(r:ℝ) := by
    have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hg := shifted_power_step_exp (p+r) r hx (by linarith)
  calc
    _ = (B*(p+r+1)/h)*((B/h)^r*(p+r+1)^r) := by
      push_cast
      simp only [pow_succ,div_pow,mul_pow]
      ring
    _ ≤ (B*(p+r+1)/h)*((B/h)^r*(Real.exp 1*(p+r)^r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by simp only [mul_pow,div_pow];ring

lemma finite_half_tail_from (a : ℕ→ℝ) (L N : ℕ) (ha : 0 ≤ a L)
    (hstep : ∀ k : ℕ, k<N → a (L+k+1) ≤ a (L+k)/2) :
    (∑ k ∈ Finset.range N, a (L+k)) ≤ 2*a L := by
  have hterm : ∀ k : ℕ, k<N → a (L+k) ≤ a L*(1/2:ℝ)^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      calc
        _ ≤ a (L+k)/2 := by simpa only [Nat.add_assoc] using hstep k (by omega)
        _ ≤ (a L*(1/2:ℝ)^k)/2 := div_le_div_of_nonneg_right (ih (by omega)) (by norm_num)
        _ = _ := by rw [pow_succ];ring
  calc
    _ ≤ ∑ k ∈ Finset.range N, a L*(1/2:ℝ)^k := Finset.sum_le_sum (fun k hk=>hterm k (Finset.mem_range.mp hk))
    _ = a L*∑ k ∈ Finset.range N,(1/2:ℝ)^k := by rw [Finset.mul_sum]
    _ ≤ 2*a L := by nlinarith [sum_geometric_two_le N]

lemma finite_loss_power_tail (p B h : ℝ) (L N : ℕ) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hh : 0 < h) (hL : 1 ≤ L)
    (hcut : 2*Real.exp 1*B*(p+(L+N:ℕ)+1) ≤ h) :
    (∑ k ∈ Finset.range N, (B*(p+(L+k:ℕ))/h)^(L+k)) ≤
      2*(B*(p+L)/h)^L := by
  apply finite_half_tail_from (fun r=>(B*(p+r)/h)^r) L N (by positivity)
  intro k hk
  have hs := loss_power_successor p B h (L+k) hp hB hh (by omega)
  have hcoeff : Real.exp 1*B*(p+(L+k:ℕ)+1)/h ≤ 1/2 := by
    apply (div_le_iff₀ hh).mpr
    have hr : ((L+k:ℕ):ℝ) ≤ (L+N:ℕ) := by exact_mod_cast (show L+k ≤ L+N by omega)
    have he := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.exp 1*B by positivity)
    nlinarith only [hcut,he]
  have hm := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (B*(p+(L+k:ℕ))/h)^(L+k) by positivity)
  exact hs.trans (by nlinarith only [hm])

lemma loss_scale_dominates_stretched_exponential (h p : ℝ) (L : ℕ)
    (hh : 1 ≤ h) (hp : 1 ≤ p) (hL : (L:ℝ) ≤ Real.sqrt h) :
    Real.exp (-Real.sqrt h*Real.log h) ≤ ((p+L)/h)^L := by
  have hh0 : 0 < h := by linarith
  have hl : 0 ≤ Real.log h := Real.log_nonneg hh
  have hlog : -Real.sqrt h*Real.log h ≤ -((L:ℝ)*Real.log h) := by nlinarith
  have heq : Real.exp (-((L:ℝ)*Real.log h)) = (h⁻¹)^L := by
    rw [neg_mul_eq_mul_neg,Real.exp_nat_mul,Real.exp_neg,Real.exp_log hh0]
  calc
    _ ≤ Real.exp (-((L:ℝ)*Real.log h)) := Real.exp_le_exp.mpr hlog
    _ = (h⁻¹)^L := heq
    _ ≤ _ := by
      apply pow_le_pow_left₀ (inv_nonneg.mpr hh0.le) _ L
      rw [←one_div]
      exact div_le_div_of_nonneg_right (by linarith [show (0:ℝ) ≤ L from Nat.cast_nonneg L]) hh0.le

lemma macroscopic_exponential_le_uniform_loss_scale (c : ℝ) (hc : 0 < c) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ p : ℝ, 1 ≤ p → ∀ L : ℕ,
      (L:ℝ) ≤ Real.sqrt h → Real.exp (-c*h) ≤ ((p+L)/h)^L := by
  have he := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound hc
  obtain ⟨H,hH⟩ := (eventually_atTop.mp he)
  refine ⟨max 1 H,le_max_left _ _,?_⟩
  intro h hh p hp L hL
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hh
  have hh0 : 0 ≤ h := by linarith
  have hbound : Real.log h ≤ c*Real.sqrt h := by
    have hb := hH h ((le_max_right _ _).trans hh)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hh1),
      abs_of_nonneg (Real.rpow_nonneg hh0 _),Real.sqrt_eq_rpow] using hb
  have hm := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg h)
  have hm' : Real.sqrt h*Real.log h ≤ c*h := by
    calc
      _ ≤ Real.sqrt h*(c*Real.sqrt h) := hm
      _ = c*(Real.sqrt h)^2 := by ring
      _ = c*h := by rw [Real.sq_sqrt hh0]
  have he : -c*h ≤ -Real.sqrt h*Real.log h := by linarith only [hm']
  exact (Real.exp_le_exp.mpr he).trans (loss_scale_dominates_stretched_exponential h p L hh1 hp hL)
end WP.Analysis
