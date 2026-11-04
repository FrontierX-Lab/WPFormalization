import WPFormalization.HigherOrder.ShiftRemainder
/-! A known order-r prefactor preserves the exact S^(2(L-r)) gain in the
uniform finite shift remainder. The proof handles r=0 and r=L explicitly;
it uses no unknown higher-order remainder or convergence assumption. -/
noncomputable section
namespace WP.HigherOrder
lemma loss_r_shift_truncation_bound (f:Series)(e:ℕ→ℝ)(L r:ℕ)(hL:1 ≤ L)(hr:r ≤ L)
    (c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<L-r→|PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |truncationValue (PowerSeries.X^r*f) L (1/(h-c))-
      truncationValue (complexityShift c (PowerSeries.X^r*f)) L (1/h)| ≤
      (Real.exp (2*δ)*S^(2*(L-r))/h^L)*
        (∑i∈Finset.range (L-r),e i/((L-r-i).factorial:ℝ)) := by
  have hLR:(1:ℝ) ≤ L := by exact_mod_cast hL
  have hSp:0<S := by linarith
  let e':ℕ→ℝ:=fun i=>if i<r then 0 else e (i-r)/S^(2*r)
  have he':∀i:ℕ,0 ≤ e' i := by
    intro i
    dsimp [e']
    split_ifs
    · exact le_rfl
    · exact div_nonneg (he _) (pow_nonneg hSp.le _)
  have hf':∀i:ℕ,i<L→|PowerSeries.coeff i (PowerSeries.X^r*f)| ≤ e' i*S^(2*i) := by
    intro i hi
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hir:i<r
    · simp only [if_neg (by omega : ¬ (r  ≤  i)),abs_zero,e',if_pos hir,zero_mul]
      exact le_rfl
    · have hri:r ≤ i := by omega
      rw [if_pos hri]
      apply (hf (i-r) (by omega)).trans_eq
      simp only [e',if_neg hir]
      have hp:S^(2*i)=S^(2*(i-r))*S^(2*r) := by rw [←pow_add];congr 1;omega
      rw [hp]
      field_simp [hSp.ne']
  have hb:=shift_truncation_remainder_bound (PowerSeries.X^r*f) e' L hL c S h δ hc hS hh hsmall hδ he' hf'
  have hsum:(∑i∈Finset.range L,e' i/((L-i).factorial:ℝ))=
      (1/S^(2*r))*(∑i∈Finset.range (L-r),e i/((L-r-i).factorial:ℝ)) := by
    have hlen:r+(L-r)=L := by omega
    have hprefix:(∑i∈Finset.range r,e' i/((L-i).factorial:ℝ))=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [e',if_pos (Finset.mem_range.mp hi),zero_div]
    calc
      _=(∑i∈Finset.range r,e' i/((L-i).factorial:ℝ))+
          ∑i∈Finset.range (L-r),e' (r+i)/((L-(r+i)).factorial:ℝ) := by
        simpa only [hlen] using Finset.sum_range_add (fun i=>e' i/((L-i).factorial:ℝ)) r (L-r)
      _=∑i∈Finset.range (L-r),e' (r+i)/((L-(r+i)).factorial:ℝ) := by rw [hprefix,zero_add]
      _=_ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [e',if_neg (by omega : ¬ (r+i<r)),Nat.add_sub_cancel_left]
        have hsub:L-(r+i)=L-r-i := by omega
        rw [hsub]
        ring
  rw [hsum] at hb
  apply hb.trans_eq
  have hp:S^(2*L)=S^(2*r)*S^(2*(L-r)) := by rw [←pow_add];congr 1;omega
  rw [hp]
  field_simp [hSp.ne',pow_ne_zero _ hh.ne']
end WP.HigherOrder
