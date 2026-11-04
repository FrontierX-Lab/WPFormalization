import WPFormalization.HigherOrder.RatioFactorBounds
/-! A finite product of O(r) actual scalar factors costs only a fixed
exponential in r. The retained order q keeps S^(2q), and the sole unknown
errors appear in one positive convolution of the strictly previous scalar
orders. No product of scalar remainder constants is introduced. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma finite_product_uniform_scalar_remainder (x:ℕ→ℝ)(f:ℕ→Series)(n q r:ℕ)
    (hq:1 ≤ q)(hr:1 ≤ r)(hn:n ≤ 2*r)(C B V D S h:ℝ)
    (hC:0 ≤ C)(hB:1 ≤ B)(hV:1 ≤ V)(hD:1 ≤ D)(hS:0 ≤ S)(hh:0<h)
    (EC EG:ℕ→ℝ)(hEC:∀m,0 ≤ EC m)(hEG:∀m,0 ≤ EG m)
    (hX:∀a<n,|x a| ≤ V)
    (hcoeff:∀a<n,∀i<q,|PowerSeries.coeff i (f a)| ≤ C*B^i*S^(2*i))
    (herr:∀a<n,∀m:ℕ,1 ≤ m→m ≤ q→
      |x a-truncationValue (f a) m (1/h)| ≤ D*(EC m+EG m+B^m)*S^(2*m)/h^m) :
    |(∏a∈Finset.range n,x a)-truncationValue (∏a∈Finset.range n,f a) q (1/h)| ≤
      (D*(2*max (2*C) V)^2)^r*(S^(2*q)/h^q)*
        ((∑i∈Finset.range q,(2*B)^i*(EC (q-i)+EG (q-i)))+(2*B)^q) := by
  let Z:=max (2*C) V
  have hZ:1 ≤ Z:=hV.trans (le_max_right _ _)
  have hZ0:0 ≤ Z:=by linarith
  have hB0:0 ≤ B:=by linarith
  have hV0:0 ≤ V:=by linarith
  have hD0:0 ≤ D:=by linarith
  let e:ℕ→ℕ→ℝ:=fun a i=>(2*C)^a*(2*B)^i
  let E:ℕ→ℕ→ℝ:=fun _ m=>D*(EC m+EG m+B^m)
  have he:∀a i,0 ≤ e a i:=by intro a i;dsimp[e];positivity
  have hE:∀a m,0 ≤ E a m:=by intro a m;have hc:=hEC m;have hg:=hEG m;dsimp[E];positivity
  have hprefix:∀a<n,∀i<q,|PowerSeries.coeff i (∏k∈Finset.range a,f k)| ≤ e a i*S^(2*i):=by
    intro a ha i hi
    exact finite_product_coeff_geometric f a i C B S hC hB0 hS
      (fun k hk t ht=>hcoeff k (by omega) t (by omega)) i le_rfl
  have hb:=finite_product_remainder_scaled_bound x f e E n q hq S h V hS hh hV0 he hE hX hprefix herr
  let F:ℕ→ℝ:=fun i=>(2*B)^i*(EC (q-i)+EG (q-i)+B^(q-i))
  have hF:∀i,0 ≤ F i:=by intro i;have hc:=hEC (q-i);have hg:=hEG (q-i);dsimp[F];positivity
  have hsuffix(a:ℕ)(ha:a<n):(2*C)^a*V^(n-(a+1)) ≤ Z^n:=by
    calc
      _ ≤ Z^a*Z^(n-(a+1)):=mul_le_mul
        (pow_le_pow_left₀ (by positivity) (le_max_left _ _) a)
        (pow_le_pow_left₀ hV0 (le_max_right _ _) _)
        (pow_nonneg hV0 _) (pow_nonneg hZ0 _)
      _=Z^(n-1):=by rw[←pow_add];congr 1;omega
      _ ≤ Z^n:=pow_le_pow_right₀ hZ (by omega)
  have hsum:(∑a∈Finset.range n,∑i∈Finset.range q,e a i*E a (q-i)*V^(n-(a+1))) ≤
      (n:ℝ)*Z^n*D*(∑i∈Finset.range q,F i):=by
    calc
      _ ≤ ∑a∈Finset.range n,∑i∈Finset.range q,Z^n*D*F i:=by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro i hi
        have ht:=mul_le_mul_of_nonneg_right (hsuffix a (Finset.mem_range.mp ha))
          (mul_nonneg hD0 (hF i))
        convert ht using 1 <;>dsimp[e,E,F]<;>ring
      _=_:=by simp only[←Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring
  have hnPow:(n:ℝ)*Z^n ≤ (2*Z)^(2*r):=by
    have hn2:(n:ℝ) ≤ (2:ℝ)^n:=by exact_mod_cast Nat.le_of_lt n.lt_two_pow_self
    calc
      _ ≤ (2:ℝ)^n*Z^n:=mul_le_mul_of_nonneg_right hn2 (pow_nonneg hZ0 _)
      _=(2*Z)^n:=by rw[mul_pow]
      _ ≤ (2*Z)^(2*r):=pow_le_pow_right₀ (by linarith) hn
  have hDpow:D ≤ D^r:=by simpa only[pow_one] using (pow_le_pow_right₀ hD hr : D^1 ≤ D^r)
  have hnD:(n:ℝ)*Z^n*D ≤ (D*(2*Z)^2)^r:=by
    have ht:=mul_le_mul hnPow hDpow hD0 (pow_nonneg (by linarith:0 ≤ 2*Z) _)
    apply ht.trans_eq
    calc
      _=((2*Z)^2)^r*D^r:=by rw[pow_mul]
      _=_:=by rw[mul_pow];ring
  have hforcing:(∑i∈Finset.range q,(2*B)^i*B^(q-i)) ≤ (2*B)^q:=by
    have heq:(∑i∈Finset.range q,(2*B)^i*B^(q-i))=B^q*(∑i∈Finset.range q,(2:ℝ)^i):=by
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiq:i ≤ q:=(Finset.mem_range.mp hi).le
      rw[mul_pow]
      have hp:B^i*B^(q-i)=B^q:=by rw[←pow_add,Nat.add_sub_of_le hiq]
      calc
        _=2^i*(B^i*B^(q-i)):=by ring
        _=_:=by rw[hp];ring
    rw[heq]
    have hnq:q-1+1=q:=by omega
    have hgeo:=finite_geometric_two_le (q-1)
    rw[hnq] at hgeo
    exact (mul_le_mul_of_nonneg_left hgeo (pow_nonneg hB0 q)).trans_eq (by rw[mul_pow];ring)
  have hknown:(∑i∈Finset.range q,F i) ≤
      (∑i∈Finset.range q,(2*B)^i*(EC (q-i)+EG (q-i)))+(2*B)^q:=by
    dsimp[F]
    simp_rw[mul_add,Finset.sum_add_distrib]
    linarith
  have hnonneg:0 ≤ (∑i∈Finset.range q,F i):=Finset.sum_nonneg (fun i hi=>hF i)
  have hbound: (∑a∈Finset.range n,∑i∈Finset.range q,e a i*E a (q-i)*V^(n-(a+1))) ≤
      (D*(2*Z)^2)^r*((∑i∈Finset.range q,(2*B)^i*(EC (q-i)+EG (q-i)))+(2*B)^q):=by
    exact hsum.trans (mul_le_mul hnD hknown hnonneg (pow_nonneg (by positivity) _))
  apply hb.trans
  have ht:=mul_le_mul_of_nonneg_left hbound (by positivity:0 ≤ S^(2*q)/h^q)
  convert ht using 1 <;>dsimp[Z]<;>ring

end WP.HigherOrder
