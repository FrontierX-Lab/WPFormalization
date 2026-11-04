import Mathlib
/-! The genuine inverse-linear shift tail in Appendix C.3.
A finite binomial identity bounds each omitted coefficient, and the
classical binomial series (already proved in Mathlib) sums the bound.
No formal-series convergence is assumed for a hierarchy coefficient. -/
noncomputable section
namespace WP.HigherOrder
lemma binomial_shift_tail_coefficient (a q k:ℕ) (ha:1 ≤ a) :
    (a+q+k-1).choose (q+k) ≤ (a+q-1).choose q*(a+q+k-1).choose k :=by
  have he:=Nat.choose_mul (n:=a+q+k-1) (k:=q+k) (s:=k) (by omega)
  have hsub:a+q+k-1-k=a+q-1:=by omega
  rw[hsub,show q+k-k=q by omega] at he
  have hp:1 ≤ (q+k).choose k:=Nat.choose_pos (by omega)
  calc
    _ ≤ (a+q+k-1).choose (q+k)*(q+k).choose k:=by nlinarith
    _=(a+q+k-1).choose k*(a+q-1).choose q:=he
    _=_:=by ring

lemma binomial_series_hasSum (a:ℕ) (ha:1 ≤ a) (x:ℝ) (hx:|x|<1) :
    HasSum (fun n:ℕ=>(Nat.choose (a+n-1) n:ℝ)*x^n) (1/(1-x)^a) :=by
  have hh:=hasSum_choose_mul_geometric_of_norm_lt_one (a-1)
    (show ‖x‖<1 by simpa only[Real.norm_eq_abs] using hx)
  convert hh using 1
  · funext n
    congr 1
    rw[show n+(a-1)=a+n-1 by omega]
    have he:Nat.choose (a+n-1) n=Nat.choose (a+n-1) (a-1):=Nat.choose_symm_of_eq_add (by omega)
    exact_mod_cast he
  · rw[Nat.sub_add_cancel ha]

lemma inverse_shift_tail_le (a q:ℕ) (ha:1 ≤ a) (x:ℝ) (hx:0 ≤ x) (hx1:x<1) :
    (∑'k:ℕ,(Nat.choose (a+(q+k)-1) (q+k):ℝ)*x^(q+k)) ≤
      (Nat.choose (a+q-1) q:ℝ)*x^q/(1-x)^(a+q) :=by
  have hnorm:|x|<1:=by rwa[abs_of_nonneg hx]
  have hsum:Summable (fun k:ℕ=>(Nat.choose (a+(q+k)-1) (q+k):ℝ)*x^(q+k)):=
    (binomial_series_hasSum a ha x hnorm).summable.comp_injective
      (fun i j h=>Nat.add_left_cancel h)
  have hr:= (binomial_series_hasSum (a+q) (by omega) x hnorm).mul_left
    ((Nat.choose (a+q-1) q:ℝ)*x^q)
  have hpt (k:ℕ):
      (Nat.choose (a+(q+k)-1) (q+k):ℝ)*x^(q+k) ≤
        ((Nat.choose (a+q-1) q:ℝ)*x^q)*((Nat.choose (a+q+k-1) k:ℝ)*x^k):=by
    have hc:(Nat.choose (a+q+k-1) (q+k):ℝ) ≤
      (Nat.choose (a+q-1) q:ℝ)*(Nat.choose (a+q+k-1) k:ℝ):=by
      exact_mod_cast binomial_shift_tail_coefficient a q k ha
    rw[show a+(q+k)-1=a+q+k-1 by omega,pow_add]
    convert mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg hx _) (pow_nonneg hx _)) using 1 <;>ring
  exact (hsum.tsum_le_tsum hpt hr.summable).trans_eq (by rw[hr.tsum_eq];ring)
end WP.HigherOrder
