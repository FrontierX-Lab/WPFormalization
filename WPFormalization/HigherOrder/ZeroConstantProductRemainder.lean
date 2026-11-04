import WPFormalization.HigherOrder.LinearRemainderAlgebra
/-! Finite binomial coefficients for the loss-one shift and its product
remainder. The zero constant keeps every scalar error below the parent
order. These generic finite algebra estimates use no paper input. -/
noncomputable section
namespace WP.HigherOrder
lemma complexityShift_one_X_coeff (f:Series) (n:ℕ) :
    PowerSeries.coeff (n+1) (complexityShift 1 (PowerSeries.X*f))=
      ∑j∈Finset.range (n+1),(Nat.choose n j:ℝ)*PowerSeries.coeff j f:=by
  rw[complexityShift_coeff_sum,Finset.sum_range_succ']
  have hzero:PowerSeries.coeff 0 (PowerSeries.X*f)=0:=by
    simp only[PowerSeries.coeff_zero_eq_constantCoeff,map_mul,PowerSeries.constantCoeff_X,zero_mul]
  rw[hzero,zero_mul,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn:j ≤ n:=by have hh:=Finset.mem_range.mp hj;omega
  have hcoef:=PowerSeries.coeff_X_pow_mul f 1 j
  simp only[pow_one] at hcoef
  rw[hcoef,inverse_linear_pow_coeff 1 (j+1) (n+1-(j+1)) (by omega)]
  have hsub:n+1-(j+1)=n-j:=by omega
  have htop:j+1+(n-j)-1=n:=by omega
  rw[hsub,htop,Nat.choose_symm hjn]
  simp only[one_pow,mul_one]
  ring

lemma complexityShift_one_X_coeff_scaled (f:Series) (n:ℕ) (C B T:ℝ)
    (hC:0 ≤ C) (hB:0 ≤ B) (hT:1 ≤ T)
    (hf:∀j:ℕ,j ≤ n→|PowerSeries.coeff j f| ≤ C*B^j*T^(2*j)) :
    |PowerSeries.coeff (n+1) (complexityShift 1 (PowerSeries.X*f))| ≤
      C*(2*max B 1)^n*T^(2*n):=by
  let R:=max B 1
  have hR:1 ≤ R:=le_max_right _ _
  have hR0:0 ≤ R:=by linarith
  have hT0:0 ≤ T:=by linarith
  have hcoeff (j:ℕ) (hj:j∈Finset.range (n+1)):
      |PowerSeries.coeff j f| ≤ C*R^n*T^(2*n):=by
    have hjn:j ≤ n:=by have hh:=Finset.mem_range.mp hj;omega
    have hBj:B^j ≤ R^n:=(pow_le_pow_left₀ hB (le_max_left _ _) _).trans (pow_le_pow_right₀ hR hjn)
    have hTj:T^(2*j) ≤ T^(2*n):=pow_le_pow_right₀ hT (by omega)
    exact (hf j hjn).trans (mul_le_mul (mul_le_mul_of_nonneg_left hBj hC) hTj
      (pow_nonneg hT0 _) (by positivity))
  rw[complexityShift_one_X_coeff]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑j∈Finset.range (n+1),(Nat.choose n j:ℝ)*(C*R^n*T^(2*n)):=by
      apply Finset.sum_le_sum
      intro j hj
      rw[abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hcoeff j hj) (Nat.cast_nonneg _)
    _=(2:ℝ)^n*(C*R^n*T^(2*n)):=by
      rw[←Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n
    _=_:=by rw[mul_pow]; dsimp[R]; ring


lemma zero_constant_product_scaled_step (x y:ℝ) (f g:Series) (L:ℕ) (hL:2 ≤ L)
    (T h R C B Y₀:ℝ) (H:ℕ→ℝ) (hT:0 ≤ T) (hh:0<h)
    (hR:0 ≤ R) (hC:0 ≤ C) (hB:0 ≤ B) (hY₀:0 ≤ Y₀) (hH:∀j,0 ≤ H j)
    (hf₀:PowerSeries.coeff 0 f=0) (hy:|y| ≤ Y₀)
    (hx:|x-truncationValue f L (1/h)| ≤ R*T^(2*(L-1))/h^L)
    (hf:∀i:ℕ,i<L-1→|PowerSeries.coeff (i+1) f| ≤ C*B^i*T^(2*i))
    (hg:∀j:ℕ,1 ≤ j→j ≤ L-1→|y-truncationValue g j (1/h)| ≤ H j*T^(2*j)/h^j) :
    |x*y-truncationValue (f*g) L (1/h)| ≤
      T^(2*(L-1))/h^L*(Y₀*R+C*∑i∈Finset.range (L-1),B^i*H (L-1-i)):=by
  have hn:=zero_constant_left_product_remainder_norm_le x y (1/h) f g L (by omega) hf₀
  have hfirst:|x-truncationValue f L (1/h)| *|y| ≤ (T^(2*(L-1))/h^L)*(Y₀*R):=by
    convert mul_le_mul hx hy (abs_nonneg y) (by positivity:0 ≤ R*T^(2*(L-1))/h^L) using 1 <;>ring
  have hterm (i:ℕ) (hi:i∈Finset.range (L-1)):
      |PowerSeries.coeff (i+1) f| *|1/h|^(i+1)*|y-truncationValue g (L-(i+1)) (1/h)| ≤
        (T^(2*(L-1))/h^L)*(C*B^i*H (L-1-i)):=by
    have hiL:i<L-1:=Finset.mem_range.mp hi
    have hj:L-(i+1)=L-1-i:=by omega
    have hcoef:|PowerSeries.coeff (i+1) f| *|1/h|^(i+1) ≤ C*B^i*T^(2*i)/h^(i+1):=by
      rw[abs_of_pos (one_div_pos.mpr hh)]
      convert mul_le_mul_of_nonneg_right (hf i hiL) (pow_nonneg (one_div_pos.mpr hh).le (i+1)) using 1 <;>
        rw[div_pow,one_pow]<;>ring
    rw[hj]
    have hp:=hg (L-1-i) (by omega) (by omega)
    apply (mul_le_mul hcoef hp (abs_nonneg _) (by positivity:0 ≤ C*B^i*T^(2*i)/h^(i+1))).trans_eq
    have hTp:T^(2*i)*T^(2*(L-1-i))=T^(2*(L-1)):=by rw[←pow_add];congr 1;omega
    have hhp:h^(i+1)*h^(L-1-i)=h^L:=by rw[←pow_add];congr 1;omega
    calc
      _=C*B^i*H (L-1-i)*(T^(2*i)*T^(2*(L-1-i)))/(h^(i+1)*h^(L-1-i)):=by ring
      _=_:=by rw[hTp,hhp];ring
  apply hn.trans
  apply (add_le_add hfirst (Finset.sum_le_sum hterm)).trans_eq
  have hs:(∑i∈Finset.range (L-1),C*B^i*H (L-1-i))=C*(∑i∈Finset.range (L-1),B^i*H (L-1-i)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw[←Finset.mul_sum,hs]
  ring
end WP.HigherOrder
