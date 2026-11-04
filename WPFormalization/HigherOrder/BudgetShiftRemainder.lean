import WPFormalization.HigherOrder.ShiftRemainder
import WPFormalization.HigherOrder.LinearRemainderAlgebra
import WPFormalization.HigherOrder.LossOneRemainder
/-! Uniform finite shift estimates distinguish the retained cutoff q from
the total parent order L. A parent loss prefactor remains at h rather than
being moved to the child complexity. Earlier scalar remainders and genuine
finite known-coefficient tails combine linearly, with no product of unknown
errors and no convergence of the formal hierarchy assumed. -/
noncomputable section
namespace WP.HigherOrder

lemma shift_truncation_remainder_bound_budget (f:Series)(e:ℕ→ℝ)(q L:ℕ)
    (hL:1 ≤ L)(hq:q ≤ L)(c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |truncationValue f q (1/(h-c))-truncationValue (complexityShift c f) q (1/h)| ≤
      (Real.exp (2*δ)*S^(2*q)/h^q)*(∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := by
  have hLR:(1:ℝ) ≤ L := by exact_mod_cast hL
  have hS0:0 ≤ S := by linarith
  have hhSq:S^2 ≤ h := (div_le_one hh).mp (hsmall.trans hδ)
  have hch:|c|<h := by nlinarith [abs_nonneg c]
  have hhc:0<h-c := by linarith [le_abs_self c]
  have ht:(1/h)/(1-c*(1/h))=1/(h-c) := by field_simp [hh.ne',hhc.ne']
  have hdef:=exact_shift_truncation_defect f c (1/h) q
  rw [ht] at hdef
  rw [hdef]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑i∈Finset.range q,(Real.exp (2*δ)*S^(2*q)/h^q)*(e i/((q-i).factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hei:0 ≤ e i := he i
      have hiq:i<q := Finset.mem_range.mp hi
      have hqi:1 ≤ q-i := by omega
      have hpow:=inverse_linear_power_truncation_error_normalized i (q-i) L hqi
        (by omega) c S h δ hc hS hh hsmall hδ
      have hiBound:|PowerSeries.coeff i f| * |1/h|^i ≤ e i*S^(2*i)/h^i := by
        rw [abs_of_pos (one_div_pos.mpr hh)]
        convert mul_le_mul_of_nonneg_right (hf i hiq) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
          rw [div_pow,one_pow] <;> ring
      have hp1:S^(2*i)*S^(2*(q-i))=S^(2*q) := by rw [←pow_add];congr 1;omega
      have hp2:h^i*h^(q-i)=h^q := by rw [←pow_add,Nat.add_sub_of_le hiq.le]
      rw [abs_mul,abs_mul,abs_pow]
      simp only [mul_one_div]
      have hb:=mul_le_mul hiBound hpow (abs_nonneg _) (by positivity:0 ≤ e i*S^(2*i)/h^i)
      apply hb.trans_eq
      calc
        _=Real.exp (2*δ)*e i*(S^(2*i)*S^(2*(q-i)))/(((q-i).factorial:ℝ)*(h^i*h^(q-i))) := by ring
        _=_ := by rw [hp1,hp2];ring
    _=_ := by rw [Finset.mul_sum]

lemma truncationValue_X_pow_mul (f:Series)(L r:ℕ)(hr:r ≤ L)(t:ℝ) :
    truncationValue (PowerSeries.X^r*f) L t=t^r*truncationValue f (L-r) t := by
  induction r generalizing L with
  | zero=>simp [truncationValue]
  | succ r ih=>
    rw [pow_succ',mul_assoc,truncationValue_X_mul _ _ (by omega),ih _ (by omega)]
    have hs:L-1-r=L-(r+1) := by omega
    rw [hs,pow_succ']
    ring

/-- The parent h^-r stays outside the shifted child; this differs from shifting
an entire order-r-prefactored series at the child complexity. -/
lemma parent_loss_shift_truncation_bound (f:Series)(e:ℕ→ℝ)(L r:ℕ)(hL:1 ≤ L)(hr:r ≤ L)
    (c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<L-r → |PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |truncationValue f (L-r) (1/(h-c))/h^r-
      truncationValue (PowerSeries.X^r*complexityShift c f) L (1/h)| ≤
      (Real.exp (2*δ)*S^(2*(L-r))/h^L)*
        (∑i∈Finset.range (L-r),e i/((L-r-i).factorial:ℝ)) := by
  have hb:=shift_truncation_remainder_bound_budget f e (L-r) L hL (by omega) c S h δ hc hS hh hsmall hδ he hf
  rw [truncationValue_X_pow_mul _ _ _ hr]
  have hv:truncationValue f (L-r) (1/(h-c))/h^r-
      (1/h)^r*truncationValue (complexityShift c f) (L-r) (1/h)=
      (1/h^r)*(truncationValue f (L-r) (1/(h-c))-
        truncationValue (complexityShift c f) (L-r) (1/h)) := by rw [div_pow,one_pow];ring
  rw [hv,abs_mul,abs_of_pos (one_div_pos.mpr (pow_pos hh r))]
  apply (mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr (pow_nonneg hh.le r))).trans_eq
  have hp:h^r*h^(L-r)=h^L := by rw [←pow_add,Nat.add_sub_of_le hr]
  field_simp [hh.ne']
  rw [←hp]
  ring

lemma shifted_remainder_with_budget (x E:ℝ)(f:Series)(e:ℕ→ℝ)(q L:ℕ)
    (hq1:1 ≤ q)(hq:q ≤ L)(c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(hE:0 ≤ E)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ e i*S^(2*i))
    (hx:|x-truncationValue f q (1/(h-c))| ≤ E*S^(2*q)/(h-c)^q) :
    |x-truncationValue (complexityShift c f) q (1/h)| ≤
      (Real.exp (2*δ)*S^(2*q)/h^q)*(E+∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := by
  have hL:1 ≤ L := by omega
  have hs0:0 ≤ S := by have hn:=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hd:=shifted_denominator_power_bound q L hq1 hq c S h δ hc hS hh hsmall hδ
  have hactual:|x-truncationValue f q (1/(h-c))| ≤ (Real.exp (2*δ)*S^(2*q)/h^q)*E := by
    apply hx.trans
    calc
      _=E*S^(2*q)*(1/(h-c)^q) := by ring
      _ ≤ E*S^(2*q)*(Real.exp (2*δ)/h^q) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hE (pow_nonneg hs0 _))
      _=_ := by ring
  have ht:=shift_truncation_remainder_bound_budget f e q L hL hq c S h δ hc hS hh hsmall hδ he hf
  calc
    _ ≤ |x-truncationValue f q (1/(h-c))|+
        |truncationValue f q (1/(h-c))-truncationValue (complexityShift c f) q (1/h)| := abs_sub_le _ _ _
    _ ≤ (Real.exp (2*δ)*S^(2*q)/h^q)*E+
        (Real.exp (2*δ)*S^(2*q)/h^q)*(∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := add_le_add hactual ht
    _=_ := by ring

end WP.HigherOrder
