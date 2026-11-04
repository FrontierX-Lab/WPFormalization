import WPFormalization.HigherOrder.NormalizedShiftTail
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.ShiftExtraction
/-! Genuine finite truncations of the actual complexity substitution.
The complete shift Taylor error is proved from the true binomial series,
with a uniform exp(2δ) factorial tail. No hierarchy convergence or
actual volume remainder estimate is assumed. -/
noncomputable section
namespace WP.HigherOrder
lemma inverse_one_sub_truncation_error_le_tail (a q:ℕ) (ha:1 ≤ a) (x:ℝ) (hx:|x|<1) :
    |1/(1-x)^a-∑k∈Finset.range q,(Nat.choose (a+k-1) k:ℝ)*x^k| ≤
      (∑'k:ℕ,(Nat.choose (a+(q+k)-1) (q+k):ℝ)*|x|^(q+k)) :=by
  let f:ℕ→ℝ:=fun k=>(Nat.choose (a+k-1) k:ℝ)*x^k
  have hf:HasSum f (1/(1-x)^a):=binomial_series_hasSum a ha x hx
  have ht:HasSum (fun k:ℕ=>f (k+q)) (1/(1-x)^a-∑k∈Finset.range q,f k):=by
    apply (hasSum_nat_add_iff (f:=f) q).mpr
    convert hf using 1
    ring
  have hnorm:Summable (fun k:ℕ=>‖f (k+q)‖):=ht.summable.norm
  have he:=norm_tsum_le_tsum_norm hnorm
  rw[ht.tsum_eq] at he
  have hright:(∑'k:ℕ,‖f (k+q)‖)=
      ∑'k:ℕ,(Nat.choose (a+(q+k)-1) (q+k):ℝ)*|x|^(q+k):=by
    apply tsum_congr
    intro k
    rw[show k+q=q+k by omega]
    dsimp[f]
    rw[abs_mul,abs_pow,abs_of_nonneg
      (Nat.cast_nonneg _ : (0:ℝ) ≤ (Nat.choose (a+(q+k)-1) (q+k):ℝ))]
  rw[hright] at he
  exact he

lemma inverse_one_sub_truncation_error (a q:ℕ) (ha:1 ≤ a) (x:ℝ) (hx:|x|<1) :
    |1/(1-x)^a-∑k∈Finset.range q,(Nat.choose (a+k-1) k:ℝ)*x^k| ≤
      (Nat.choose (a+q-1) q:ℝ)*|x|^q/(1-|x|)^(a+q) :=by
  exact (inverse_one_sub_truncation_error_le_tail a q ha x hx).trans
    (inverse_shift_tail_le a q ha |x| (abs_nonneg x) hx)

lemma truncationValue_complexityShift (f:Series) (c t:ℝ) (L:ℕ) :
    truncationValue (complexityShift c f) L t=
      ∑i∈Finset.range L,PowerSeries.coeff i f*t^i*
        truncationValue (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^i) (L-i) t :=by
  calc
    _=∑k∈Finset.range L,∑i∈Finset.range (k+1),PowerSeries.coeff i f*
        PowerSeries.coeff (k-i) (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^i)*t^(i+(k-i)):=by
      simp only[truncationValue,complexityShift_coeff_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw[show i+(k-i)=k by have hh:=Finset.mem_range.mp hi;omega]
    _=∑i∈Finset.range L,∑j∈Finset.range (L-i),PowerSeries.coeff i f*
        PowerSeries.coeff j (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^i)*t^(i+j):=
      Finset.sum_range_diag_flip L (fun i j=>PowerSeries.coeff i f*
        PowerSeries.coeff j (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^i)*t^(i+j))
    _=_:=by
      simp only[truncationValue,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw[pow_add]
      ring

lemma exact_shift_truncation_defect (f:Series) (c t:ℝ) (L:ℕ) :
    truncationValue f L (t/(1-c*t))-truncationValue (complexityShift c f) L t=
      ∑i∈Finset.range L,PowerSeries.coeff i f*t^i*
        (1/(1-c*t)^i-truncationValue (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^i) (L-i) t) :=by
  rw[truncationValue_complexityShift]
  simp only[truncationValue,mul_sub,Finset.sum_sub_distrib,div_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inverse_linear_power_truncation_error_normalized (a q L:ℕ)
    (hq:1 ≤ q) (haq:a+q ≤ L) (c S h δ:ℝ) (hc:|c| ≤ L) (hS:2*(L:ℝ) ≤ S)
    (hh:0<h) (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) :
    |1/(1-c/h)^a-truncationValue (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^a) q (1/h)| ≤
      Real.exp (2*δ)*S^(2*q)/((q.factorial:ℝ)*h^q) :=by
  have hS0:0 ≤ S:=by linarith[Nat.cast_nonneg (α:=ℝ) L]
  by_cases ha:a=0
  · subst a
    rw[pow_zero,pow_zero,truncationValue_one q hq]
    simp only[div_one,sub_self,abs_zero]
    positivity
  have ha1:1 ≤ a:=by omega
  have hL:1 ≤ L:=by omega
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hS1:1 ≤ S:=by linarith
  have hhSq:S^2 ≤ h:=(div_le_one hh).mp (hsmall.trans hδ)
  have hx:|c/h|<1:=by
    rw[abs_div,abs_of_pos hh]
    apply (div_lt_one hh).2
    have hc0:0 ≤ |c|:=abs_nonneg c
    nlinarith
  have he:=inverse_one_sub_truncation_error_le_tail a q ha1 (c/h) hx
  have htrunc:truncationValue (((1-PowerSeries.C c*PowerSeries.X:Series)⁻¹)^a) q (1/h)=
      ∑k∈Finset.range q,(Nat.choose (a+k-1) k:ℝ)*(c/h)^k:=by
    unfold truncationValue
    apply Finset.sum_congr rfl
    intro k hk
    rw[inverse_linear_pow_coeff c a k ha1,div_pow,one_pow,div_pow]
    ring
  rw[←htrunc] at he
  have ht:=inverse_shift_tail_normalized a q L ha1 haq |c| S h δ (abs_nonneg c) hc hS hh hsmall hδ
  exact he.trans (by simpa only[abs_div,abs_of_pos hh] using ht)
lemma shift_truncation_remainder_bound (f:Series) (e:ℕ→ℝ) (L:ℕ) (hL:1 ≤ L)
    (c S h δ:ℝ) (hc:|c| ≤ L) (hS:2*(L:ℝ) ≤ S) (hh:0<h)
    (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) (he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<L→|PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |truncationValue f L (1/(h-c))-truncationValue (complexityShift c f) L (1/h)| ≤
      (Real.exp (2*δ)*S^(2*L)/h^L)*(∑i∈Finset.range L,e i/((L-i).factorial:ℝ)) :=by
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hS0:0 ≤ S:=by linarith
  have hhSq:S^2 ≤ h:=(div_le_one hh).mp (hsmall.trans hδ)
  have hch:|c|<h:=by nlinarith[abs_nonneg c]
  have hhc:0<h-c:=by linarith[le_abs_self c]
  have hden:1-c*(1/h)≠0:=by
    intro hz
    have heq:c=h:=by field_simp[hh.ne'] at hz;linarith
    linarith
  have ht:(1/h)/(1-c*(1/h))=1/(h-c):=by field_simp[hh.ne',hhc.ne']
  have hdef:=exact_shift_truncation_defect f c (1/h) L
  rw[ht] at hdef
  rw[hdef]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑i∈Finset.range L,(Real.exp (2*δ)*S^(2*L)/h^L)*(e i/((L-i).factorial:ℝ)):=by
      apply Finset.sum_le_sum
      intro i hi
      have hei:0 ≤ e i:=he i
      have hiL:i<L:=Finset.mem_range.mp hi
      have hiLe:i ≤ L:=hiL.le
      have hqi:1 ≤ L-i:=by omega
      have hpow:=inverse_linear_power_truncation_error_normalized i (L-i) L hqi
        (by omega) c S h δ hc hS hh hsmall hδ
      have hiBound:|PowerSeries.coeff i f| *|1/h|^i ≤ e i*S^(2*i)/h^i:=by
        rw[abs_of_pos (one_div_pos.mpr hh)]
        convert mul_le_mul_of_nonneg_right (hf i hiL) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
          rw[div_pow,one_pow]<;>ring
      have hp1:S^(2*i)*S^(2*(L-i))=S^(2*L):=by rw[←pow_add];congr 1;omega
      have hp2:h^i*h^(L-i)=h^L:=by rw[←pow_add,Nat.add_sub_of_le hiLe]
      rw[abs_mul,abs_mul,abs_pow]
      simp only[mul_one_div]
      have hhBound:=mul_le_mul hiBound hpow (abs_nonneg _)
        (by positivity:0 ≤ e i*S^(2*i)/h^i)
      apply hhBound.trans_eq
      calc
        _=Real.exp (2*δ)*e i*(S^(2*i)*S^(2*(L-i)))/(((L-i).factorial:ℝ)*(h^i*h^(L-i))):=by ring
        _=_:=by rw[hp1,hp2];ring
    _=_:=by rw[Finset.mul_sum]
end WP.HigherOrder
