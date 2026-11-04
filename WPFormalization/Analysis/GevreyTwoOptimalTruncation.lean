import WPFormalization.Analysis.FiniteExpGevreyTwo
/-! Square-root optimal truncation of a genuine Gevrey-two error bound.
Positive constants are chosen before h; the actual floor and first omitted
factorial are retained. This is a numerical postprocessing lemma only. -/

noncomputable section
namespace WP.Analysis
lemma gevreyTwo_optimal_scalar (B c:ℝ) (hB:0<B) (hc:0<c):
    ∃c' a H:ℝ,0<c' ∧ c' ≤ c ∧ 0<a ∧ 0<H ∧∀h:ℝ,H ≤ h→
      let N:=⌊c'*Real.sqrt h⌋₊+1
      B^N*(N.factorial:ℝ)^2/h^N ≤ Real.exp (-a*Real.sqrt h):=by
  let c':ℝ:=min c (1/(4*(B+1)))
  have hc':0<c':=lt_min hc (by positivity)
  have hcap:4*(B+1)*c' ≤ 1:=by
    have he:=(le_div_iff₀ (by positivity:0<4*(B+1))).mp (min_le_right c (1/(4*(B+1))))
    dsimp[c']
    nlinarith
  have hBc:0 ≤ B*c':=mul_nonneg hB.le hc'.le
  have hcp4:4*c' ≤ 1:=by nlinarith
  have hBc4:4*B*c' ≤ 1:=by nlinarith
  have hmul:=mul_le_mul_of_nonneg_right hcp4 hBc
  have hbase:4*B*c'^2 ≤ 1/2:=by nlinarith
  let a:=c'*Real.log 2
  have ha:0<a:=mul_pos hc' (Real.log_pos (by norm_num))
  let H:ℝ:=max 1 ((c'⁻¹)^2)
  have hH:0<H:=by dsimp[H];exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c',a,H,hc',min_le_left _ _,ha,hH,?_⟩
  intro h hhH
  have hh:0<h:=hH.trans_le hhH
  let S:=Real.sqrt h
  have hS:0 ≤ S:=Real.sqrt_nonneg _
  have hSsq:S^2=h:=Real.sq_sqrt hh.le
  have hhInv:(c'⁻¹)^2 ≤ h:=(le_max_right _ _).trans hhH
  have hlarge:=mul_le_mul_of_nonneg_left hhInv (sq_nonneg c')
  have heInv:c'^2*(c'⁻¹)^2=1:=by field_simp[hc'.ne']
  rw[heInv] at hlarge
  have ht0:0 ≤ c'*S:=mul_nonneg hc'.le hS
  have ht1:1 ≤ c'*S:=by nlinarith
  let N:=⌊c'*S⌋₊+1
  have hNup:(N:ℝ) ≤ c'*S+1:=by
    have hn:=Nat.floor_le ht0
    dsimp[N]
    push_cast
    linarith
  have hNup2:(N:ℝ) ≤ 2*c'*S:=by linarith
  have hNlo:c'*S ≤ (N:ℝ):=by
    have hn:=Nat.lt_floor_add_one (c'*S)
    dsimp[N]
    simpa only[Nat.cast_add,Nat.cast_one] using hn.le
  have hN2:(N:ℝ)^2 ≤ 4*c'^2*h:=by
    have hp:=pow_le_pow_left₀ (Nat.cast_nonneg N : (0:ℝ) ≤ N) hNup2 2
    nlinarith
  have hratio:B*(N:ℝ)^2/h ≤ 1/2:=by
    apply (div_le_iff₀ hh).mpr
    have hn:=mul_le_mul_of_nonneg_left hN2 hB.le
    have hb:=mul_le_mul_of_nonneg_right hbase hh.le
    nlinarith
  have hfac:(N.factorial:ℝ) ≤ (N:ℝ)^N:=by exact_mod_cast Nat.factorial_le_pow N
  have hexp:(1/(2:ℝ))^N=Real.exp (-(N:ℝ)*Real.log 2):=by
    rw[neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num:(0:ℝ)<2),div_pow,one_pow]
    simp only[one_div]
  change B^N*(N.factorial:ℝ)^2/h^N ≤ _
  calc
    _ ≤ B^N*((N:ℝ)^N)^2/h^N:=div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hfac 2) (pow_nonneg hB.le _)) (by positivity)
    _=(B*(N:ℝ)^2/h)^N:=by
      rw[div_pow,mul_pow]
      have hp:((N:ℝ)^2)^N=((N:ℝ)^N)^2:=by rw[←pow_mul,←pow_mul];congr 1;omega
      rw[hp]
    _ ≤ (1/(2:ℝ))^N:=pow_le_pow_left₀ (by positivity) hratio _
    _=Real.exp (-(N:ℝ)*Real.log 2):=hexp
    _ ≤ Real.exp (-a*Real.sqrt h):=by
      apply Real.exp_le_exp.mpr
      dsimp[a,S] at *
      nlinarith[Real.log_pos (by norm_num:(1:ℝ)<2)]
end WP.Analysis
