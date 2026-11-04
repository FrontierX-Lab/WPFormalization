import WPFormalization.Intersection.PainleveComparison
import WPFormalization.Analysis.HarmonicCoefficientMajorant
import WPFormalization.Intersection.CriticalComparison
/-! The actual uniform lower bound at terminal harmonic-comparison states.
Positive-recursion induction gives the PI comparison, and a proved coefficient
majorant compares the true model with its critical counterpart. The genuine
pure-intersection bound then yields an exponential loss only in the zero count. -/
noncomputable section
namespace WP
open Set
lemma ratio_pi_coefficient_lower (B:ℝ)(hB:1≤B)
    (hbound:∀Y∈Icc (0:ℝ) y₀,∀h m:ℕ,harmonicCoeff Y h m≤(h.ascFactorial m:ℝ)*B^m/m.factorial)
    (P:PsiTheory)(g:ℕ)(d:List ℕ)(hn:1≤d.length)(hs:Stable g d.length)
    (hd:d.sum≤dimension g d.length)(Y:ℝ)(hY:Y∈Icc 0 y₀):
    ratio P g d y₀*(3/(5*B))^(deficit g d)≤ratio P g d Y := by
  let h:=complexity g d.length
  let m:=deficit g d
  let S:ℝ:=(3:ℝ)^h*Real.Gamma h/4^g
  have hh:0<h:=by dsimp[h];unfold complexity;unfold Stable at hs;omega
  have hS:0<S:=by
    dsimp[S]
    exact div_pos (mul_pos (by positivity) (Real.Gamma_pos_of_pos (by exact_mod_cast hh))) (by positivity)
  have hBpos:0<B:=lt_of_lt_of_le zero_lt_one hB
  have hC:0<harmonicCoeff y₀ h m:=harmonicCoeff_pos y₀ h m hh ⟨y₀_pos.le,le_rfl⟩
  have hA:0<harmonicCoeff Y h m:=harmonicCoeff_pos Y h m hh hY
  have hFactor:0≤(3/(5*B))^m:=by positivity
  have hCoef:harmonicCoeff Y h m*(3/(5*B))^m≤harmonicCoeff y₀ h m := by
    calc _≤((h.ascFactorial m:ℝ)*B^m/m.factorial)*(3/(5*B))^m:=
           mul_le_mul_of_nonneg_right (hbound Y hY h m) hFactor
         _=harmonicCoeff y₀ h m:=by
           rw[harmonicCoeff_critical]
           simp only[div_pow,mul_pow]
           field_simp
           <;>ring
  have hpi:=normalized_pi_le P g d hn Y hY
  have hnc:=normalized_critical_nonneg P g d
  unfold ratio
  change normalized P g d y₀/(S*harmonicCoeff y₀ h m)*(3/(5*B))^m≤
    normalized P g d Y/(S*harmonicCoeff Y h m)
  rw[div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (mul_pos hS hC) (mul_pos hS hA)).mpr
  have h1:=mul_le_mul_of_nonneg_left hCoef hnc
  have h2:=mul_le_mul_of_nonneg_right hpi hC.le
  convert mul_le_mul_of_nonneg_left (h1.trans h2) hS.le using 1 <;> ring

lemma ratio_pi_uniform_lower :∃B:ℝ,1≤B ∧∀P:PsiTheory,∀g:ℕ,∀d:List ℕ,1≤d.length→
    Stable g d.length→d.sum≤dimension g d.length→∀Y∈Icc (0:ℝ) y₀,
      ratio P g d y₀*(3/(5*B))^(deficit g d)≤ratio P g d Y := by
  obtain ⟨B,hB,hbound⟩:=Analysis.harmonicCoeff_uniform_majorant
  exact ⟨B,hB,fun P g d hn hs hd Y hY=>ratio_pi_coefficient_lower B hB hbound P g d hn hs hd Y hY⟩
lemma length_le_sum_add_count_zero (d:List ℕ):d.length≤d.sum+d.count 0 := by
  induction d with
  | nil => simp
  | cons a d ih =>
    by_cases ha:a=0
    · subst a
      simp only[List.length_cons,List.sum_cons,List.count_cons_self,zero_add]
      omega
    · simp only[List.length_cons,List.sum_cons,List.count_cons,beq_iff_eq,ha,ite_false,add_zero]
      omega
lemma count_zero_filter_length (d:List ℕ):d.count 0=(d.filter (fun k=>k=0)).length := by
  induction d with
  | nil => simp
  | cons a d ih =>
    by_cases ha:a=0
    · subst a
      simp[ih]
    · simp[ha,ih]
lemma terminal_deficit_le_zero_count (g:ℕ)(d:List ℕ)(hs:Stable g d.length)
    (ht: deficit g d=0 ∨g≤1):deficit g d≤d.count 0 := by
  rcases ht with ht|hg
  · rw[ht]
    exact Nat.zero_le _
  · have hlength:=length_le_sum_add_count_zero d
    unfold deficit dimension
    unfold Stable at hs
    omega

/-- Lemma 5.2(ii), from the actual amplitudes and model. -/
@[blueprint "lem:terminal"]
lemma terminal_ratio_lower (P:PsiTheory):∃c C:ℝ,0<c ∧0<C ∧∀g:ℕ,∀d:List ℕ,
    1≤d.length→Stable g d.length→d.sum≤dimension g d.length→∀Y∈Icc (0:ℝ) y₀,
      (deficit g d=0 ∨g≤1)→c*Real.exp (-C*(d.count 0))≤ratio P g d Y := by
  obtain ⟨B,hB,hPI⟩:=ratio_pi_uniform_lower
  let q:ℝ:=3/(5*B)
  let b:ℝ:=2/(5*B)
  let C:ℝ:= -Real.log b
  have hBpos:0<B:=lt_of_lt_of_le zero_lt_one hB
  have hq:0<q:=by dsimp[q];positivity
  have hq1:q≤1:=by dsimp[q];apply (div_le_one (by positivity)).mpr;nlinarith
  have hb:0<b:=by dsimp[b];positivity
  have hb1:b<1:=by dsimp[b];apply (div_lt_one (by positivity)).mpr;nlinarith
  have hC:0<C:=by dsimp[C];exact neg_pos.mpr (Real.log_neg hb hb1)
  refine ⟨1/6,C,by norm_num,hC,?_⟩
  intro g d hn hs hd Y hY ht
  let Z:=d.count 0
  have hm:deficit g d≤Z:=terminal_deficit_le_zero_count g d hs ht
  have hpibound:=hPI P g d hn hs hd Y hY
  have hcrit:=(critical_ratio_zero_bounds P g d hs hd).1
  have hqpow:q^Z≤q^(deficit g d):=pow_le_pow_of_le_one hq.le hq1 hm
  have hprod:(1/6:ℝ)*(2/3:ℝ)^Z*q^Z≤ratio P g d y₀*q^(deficit g d):=
    mul_le_mul hcrit hqpow (by positivity) ((by positivity : (0:ℝ)≤(1/6)*(2/3:ℝ)^Z).trans hcrit)
  have hbase:(2/3:ℝ)*q=b:=by dsimp[q,b];ring
  have hExp:Real.exp (-C*(Z:ℝ))=b^Z:=by
    dsimp[C]
    rw[neg_neg,mul_comm,Real.exp_nat_mul,Real.exp_log hb]
  change (1/6:ℝ)*Real.exp (-C*(Z:ℝ))≤ratio P g d Y
  rw[hExp]
  calc _=(1/6:ℝ)*(2/3:ℝ)^Z*q^Z:=by rw[←hbase,mul_pow];ring
       _≤ratio P g d y₀*q^(deficit g d):=hprod
       _≤ratio P g d Y:=hpibound
end WP
