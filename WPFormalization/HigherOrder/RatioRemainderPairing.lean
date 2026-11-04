import WPFormalization.HigherOrder.ActualRatioProduct
import WPFormalization.HigherOrder.BudgetShiftRemainder
import WPFormalization.HigherOrder.TriangularLocality
/-! Actual C.14 product defects reduce exactly to their finite dimensionless
core. An arbitrary finite product has an explicit single-remainder expansion
with known formal prefixes and actual suffixes. The normalized norm bound is
linear in the displayed individual remainder bounds and retains every order;
no product of unknown errors or whole-ratio estimate is assumed. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries Set

lemma ratioSeries_prefactor_core (Y:ℝ)(F:HierarchyJet)(p j s:ℕ) :
    ratioSeries Y F p j s=PowerSeries.C ((A Y)^(2*j+s))*
      (PowerSeries.X^(2*j+s)*ratioCoreSeries F p j s) := by
  dsimp only [ratioSeries,ratioCoreSeries]
  rw [mul_pow,←map_pow]
  ring

lemma loss_prefactored_defect (a h x:ℝ)(f:Series)(L r:ℕ)(hr:r ≤ L) :
    (a/h)^r*x-truncationValue (PowerSeries.C (a^r)*(PowerSeries.X^r*f)) L (1/h)=
      (a/h)^r*(x-truncationValue f (L-r) (1/h)) := by
  rw [truncationValue_C_mul,truncationValue_X_pow_mul _ _ _ hr]
  simp only [div_pow,one_pow]
  ring

lemma large_component_product_remainder_pairing (P:PsiTheory)(g p j s L:ℕ)
    (F:HierarchyJet)(u:Series)(x:ℝ)(hr:2*j+s ≤ L)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(hj:j ≤ g)(hs:s<p)(hstable:Stable (g-j) (p-s)) :
    |(W P (g-j) (p-s) Y/W P g p Y)*x-
      truncationValue (ratioSeries Y F p j s*u) L (1/(complexity g p:ℝ))|=
      (|A Y|^(2*j+s)/(complexity g p:ℝ)^(2*j+s))*
        |actualLargeRatioCore P g p j s Y*x-
          truncationValue (ratioCoreSeries F p j s*u) (L-(2*j+s)) (1/(complexity g p:ℝ))| := by
  have hh:0<(complexity g p:ℝ) := by
    have hn:0<complexity g p := by unfold complexity Stable at *;omega
    exact_mod_cast hn
  rw [large_component_ratio_exact_core P g p j s Y hY hj hs hstable,
    ratioSeries_prefactor_core]
  have he:(PowerSeries.C ((A Y)^(2*j+s))*(PowerSeries.X^(2*j+s)*ratioCoreSeries F p j s))*u=
      PowerSeries.C ((A Y)^(2*j+s))*(PowerSeries.X^(2*j+s)*(ratioCoreSeries F p j s*u)) := by ring
  rw [he]
  have hactual:(A Y/(complexity g p:ℝ))^(2*j+s)*actualLargeRatioCore P g p j s Y*x=
      (A Y/(complexity g p:ℝ))^(2*j+s)*(actualLargeRatioCore P g p j s Y*x) := by ring
  rw [hactual,loss_prefactored_defect _ _ _ _ _ _ hr,abs_mul,abs_pow,abs_div,abs_of_pos hh,div_pow]

lemma exact_finite_product_single_remainder {R:Type*}[CommRing R]
    (x:ℕ→R)(f:ℕ→PowerSeries R)(n q:ℕ)(hq:1 ≤ q)(t:R) :
    (∏k∈Finset.range n,x k)-truncationValue (∏k∈Finset.range n,f k) q t=
      ∑s∈Finset.range n,∑i∈Finset.range q,
        PowerSeries.coeff i (∏k∈Finset.range s,f k)*t^i*
          (x s-truncationValue (f s) (q-i) t)*(∏k∈Finset.Ico (s+1) n,x k) := by
  induction n with
  | zero=>simp only [Finset.prod_range_zero,truncationValue_one q hq,sub_self,Finset.sum_range_zero]
  | succ n ih=>
    rw [Finset.prod_range_succ,Finset.prod_range_succ,exact_product_remainder_identity,ih,
      Finset.sum_range_succ]
    have hfirst:(∑s∈Finset.range n,∑i∈Finset.range q,
        PowerSeries.coeff i (∏k∈Finset.range s,f k)*t^i*
          (x s-truncationValue (f s) (q-i) t)*(∏k∈Finset.Ico (s+1) n,x k))*x n=
      ∑s∈Finset.range n,∑i∈Finset.range q,
        PowerSeries.coeff i (∏k∈Finset.range s,f k)*t^i*
          (x s-truncationValue (f s) (q-i) t)*(∏k∈Finset.Ico (s+1) (n+1),x k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_Ico_succ_top (by have :=Finset.mem_range.mp hs;omega)]
      ring
    rw [hfirst]
    simp only [Finset.Ico_self,Finset.prod_empty,mul_one]

lemma finite_product_single_remainder_norm (x:ℕ→ℝ)(f:ℕ→Series)(n q:ℕ)(hq:1 ≤ q)(t:ℝ) :
    |(∏k∈Finset.range n,x k)-truncationValue (∏k∈Finset.range n,f k) q t| ≤
      ∑s∈Finset.range n,∑i∈Finset.range q,
        |PowerSeries.coeff i (∏k∈Finset.range s,f k)| * |t|^i*
          |x s-truncationValue (f s) (q-i) t| * (∏k∈Finset.Ico (s+1) n,|x k|) := by
  rw [exact_finite_product_single_remainder x f n q hq t]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simp only [abs_mul,abs_pow,Finset.abs_prod]
  exact le_rfl

lemma finite_product_remainder_scaled_bound (x:ℕ→ℝ)(f:ℕ→Series)(P E:ℕ→ℕ→ℝ)
    (n q:ℕ)(hq:1 ≤ q)(S h V:ℝ)(hS:0 ≤ S)(hh:0<h)(hV:0 ≤ V)
    (hP:∀s i,0 ≤ P s i)(hE:∀s i,0 ≤ E s i)
    (hX:∀k<n,|x k| ≤ V)
    (hcoeff:∀s<n,∀i<q,|PowerSeries.coeff i (∏k∈Finset.range s,f k)| ≤ P s i*S^(2*i))
    (herr:∀s<n,∀m:ℕ,1 ≤ m → m ≤ q →
      |x s-truncationValue (f s) m (1/h)| ≤ E s m*S^(2*m)/h^m) :
    |(∏k∈Finset.range n,x k)-truncationValue (∏k∈Finset.range n,f k) q (1/h)| ≤
      (S^(2*q)/h^q)*(∑s∈Finset.range n,∑i∈Finset.range q,
        P s i*E s (q-i)*V^(n-(s+1))) := by
  have htail(s:ℕ):∏k∈Finset.Ico (s+1) n,|x k| ≤ V^(n-(s+1)) := by
    calc
      _ ≤ ∏k∈Finset.Ico (s+1) n,V := by
        apply Finset.prod_le_prod₀
        · intro k hk;exact abs_nonneg _
        · intro k hk;exact hX k (Finset.mem_Ico.mp hk).2
      _=_ := by simp
  have hterm(s i:ℕ)(hs:s<n)(hi:i<q):
      |PowerSeries.coeff i (∏k∈Finset.range s,f k)| * |1/h|^i*
        |x s-truncationValue (f s) (q-i) (1/h)| * (∏k∈Finset.Ico (s+1) n,|x k|) ≤
      (S^(2*q)/h^q)*(P s i*E s (q-i)*V^(n-(s+1))) := by
    have hPi:=hP s i
    have hEi:=hE s (q-i)
    have hci:|PowerSeries.coeff i (∏k∈Finset.range s,f k)| * |1/h|^i ≤ P s i*S^(2*i)/h^i := by
      rw [abs_of_pos (one_div_pos.mpr hh)]
      convert mul_le_mul_of_nonneg_right (hcoeff s hs i hi) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
        rw [div_pow,one_pow] <;> ring
    have hri:=herr s hs (q-i) (by omega) (by omega)
    have hp:S^(2*i)*S^(2*(q-i))=S^(2*q) := by rw [←pow_add];congr 1;omega
    have hn:h^i*h^(q-i)=h^q := by rw [←pow_add,Nat.add_sub_of_le hi.le]
    have hb:|PowerSeries.coeff i (∏k∈Finset.range s,f k)| * |1/h|^i*
        |x s-truncationValue (f s) (q-i) (1/h)| ≤
        (S^(2*q)/h^q)*(P s i*E s (q-i)) := by
      apply (mul_le_mul hci hri (abs_nonneg _) (by positivity:0 ≤ P s i*S^(2*i)/h^i)).trans_eq
      calc
        _=(P s i*E s (q-i))*(S^(2*i)*S^(2*(q-i)))/(h^i*h^(q-i)) := by ring
        _=_ := by rw [hp,hn];ring
    have ht:=mul_le_mul hb (htail s) (Finset.prod_nonneg (fun k hk=>abs_nonneg _))
      (by positivity:0 ≤ (S^(2*q)/h^q)*(P s i*E s (q-i)))
    convert ht using 1 <;> ring
  apply (finite_product_single_remainder_norm x f n q hq (1/h)).trans
  calc
    _ ≤ ∑s∈Finset.range n,∑i∈Finset.range q,
        (S^(2*q)/h^q)*(P s i*E s (q-i)*V^(n-(s+1))) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro i hi
      exact hterm s i (Finset.mem_range.mp hs) (Finset.mem_range.mp hi)
    _=_ := by simp_rw [Finset.mul_sum]

end WP.HigherOrder
