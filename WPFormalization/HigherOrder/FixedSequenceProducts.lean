import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.FiniteAsymptoticUniqueness
noncomputable section
namespace WP.HigherOrder
lemma finite_product_inverse_power_error_fixed (x y:ℂ)(f g:PowerSeries ℂ)
    (q:ℕ)(t A Y:ℝ)(B:ℕ→ℝ)(ht:0<t)(hA:0≤A)(hY:0≤Y)
    (hyn:‖y‖≤Y)
    (hx:‖x-truncationValue f q ((t:ℂ)⁻¹)‖≤A/t^q)
    (hy:∀j∈Finset.range q,0≤B j ∧
      ‖y-truncationValue g (q-j) ((t:ℂ)⁻¹)‖≤B j/t^(q-j)):
    ‖x*y-truncationValue (f*g) q ((t:ℂ)⁻¹)‖≤
      (A*Y+∑j∈Finset.range q,‖PowerSeries.coeff j f‖*B j)/t^q:=by
  have hn:‖(t:ℂ)⁻¹‖=t⁻¹:=by
    rw[norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  apply (exact_product_remainder_norm_le x y f g q ((t:ℂ)⁻¹)).trans
  rw[hn]
  have hmain:‖x-truncationValue f q ((t:ℂ)⁻¹)‖*‖y‖≤(A*Y)/t^q:=by
    exact (mul_le_mul hx hyn (norm_nonneg _) (by positivity:0≤A/t^q)).trans_eq (by ring)
  have hsum:(∑j∈Finset.range q,‖PowerSeries.coeff j f‖*(t⁻¹)^j*
      ‖y-truncationValue g (q-j) ((t:ℂ)⁻¹)‖)≤
      (∑j∈Finset.range q,‖PowerSeries.coeff j f‖*B j)/t^q:=by
    rw[Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    have hjq:j≤q:=(Finset.mem_range.mp hj).le
    have hid:‖PowerSeries.coeff j f‖*(t⁻¹)^j*(B j/t^(q-j))=
        (‖PowerSeries.coeff j f‖*B j)/t^q:=by
      rw[show q=j+(q-j) from (Nat.add_sub_of_le hjq).symm,pow_add,inv_pow]
      field_simp
      simp only[Nat.add_sub_cancel_left]
    exact (mul_le_mul_of_nonneg_left (hy j hj).2 (by positivity)).trans_eq hid
  exact (add_le_add hmain hsum).trans_eq (by ring)
end WP.HigherOrder

namespace WP.HigherOrder
open Filter
open scoped Topology
lemma finite_sequence_inverse_power_product (F G:ℕ→ℂ)(t:ℕ→ℝ)
    (f g:PowerSeries ℂ)(N:ℕ)(ht:Tendsto t atTop atTop)
    (ha:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n-truncationValue f (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1))
    (hb:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖G n-truncationValue g (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1)):
    ∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n*G n-truncationValue (f*g) (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1):=by
  have hbt(i:Fin (N+1)):∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖G n-truncationValue g (i.val+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(i.val+1):=hb i.val (by omega)
  choose b hbp hbe using hbt
  have hball:∀ᶠn:ℕ in atTop,∀i:Fin (N+1),0<t n ∧
      ‖G n-truncationValue g (i.val+1) ((t n:ℂ)⁻¹)‖≤b i/(t n)^(i.val+1):=
    Filter.eventually_all.mpr hbe
  let i0:Fin (N+1):=⟨0,by omega⟩
  let Y:ℝ:=b i0+‖PowerSeries.coeff 0 g‖
  have hY:0<Y:=add_pos_of_pos_of_nonneg (hbp i0) (norm_nonneg _)
  intro K hKN
  obtain ⟨Ca,hCa,hAe⟩:=ha K hKN
  let B:ℕ→ℝ:=fun j=>b ⟨K-j,by omega⟩
  let C:ℝ:=Ca*Y+∑j∈Finset.range (K+1),‖PowerSeries.coeff j f‖*B j
  have hC:0<C:=by
    apply add_pos_of_pos_of_nonneg (mul_pos hCa hY)
    exact Finset.sum_nonneg (fun j hj=>mul_nonneg (norm_nonneg _) (hbp _).le)
  refine ⟨C,hC,?_⟩
  filter_upwards[hAe,hball,ht.eventually (eventually_ge_atTop 1)] with n han hbn htn
  refine ⟨han.1,?_⟩
  have hg0:‖G n-PowerSeries.coeff 0 g‖≤b i0/t n:=by
    simpa only[i0,Fin.val_mk,zero_add,truncationValue,Finset.sum_range_succ,Finset.sum_range_zero,
      zero_add,pow_zero,mul_one,pow_one] using (hbn i0).2
  have hyn:‖G n‖≤Y:=by
    calc _≤‖G n-PowerSeries.coeff 0 g‖+‖PowerSeries.coeff 0 g‖:=norm_le_norm_sub_add _ _
         _≤b i0/t n+‖PowerSeries.coeff 0 g‖:=add_le_add hg0 (le_refl _)
         _≤Y:=by
           dsimp[Y]
           exact add_le_add (div_le_self (hbp i0).le htn) (le_refl _)
  apply finite_product_inverse_power_error_fixed (F n) (G n) f g (K+1) (t n) Ca Y B han.1 hCa.le hY.le hyn han.2
  intro j hj
  refine ⟨(hbp _).le,?_⟩
  have htj:= (hbn ⟨K-j,by omega⟩).2
  have hjK:j≤K:=Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he:K+1-j=K-j+1:=by omega
  simpa only[he,B,Fin.val_mk] using htj
end WP.HigherOrder

namespace WP.HigherOrder
open Filter
open scoped Topology
lemma finite_sequence_truncation_unique (F:ℕ→ℂ)(t:ℕ→ℝ)(f g:PowerSeries ℂ)(N:ℕ)
    (ht:Tendsto t atTop atTop)
    (hf:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n-truncationValue f (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1))
    (hg:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n-truncationValue g (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1)):
    ∀j≤N,PowerSeries.coeff j f=PowerSeries.coeff j g:=by
  have hconvert (a:PowerSeries ℂ)
      (ha:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
        ‖F n-truncationValue a (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1)):
      ∀K≤N,∃C:ℝ,0<C ∧ ∃G:ℕ,∀n≥G,0<t n ∧
        ‖F n-∑j∈Finset.range (K+1),((t n)^j)⁻¹ • PowerSeries.coeff j a‖≤C/(t n)^(K+1):=by
    intro K hKN
    obtain ⟨C,hC,he⟩:=ha K hKN
    obtain ⟨G,hG⟩:=eventually_atTop.mp he
    refine ⟨C,hC,G,?_⟩
    intro n hn
    have hsum:(∑j∈Finset.range (K+1),((t n)^j)⁻¹ • PowerSeries.coeff j a)=
        truncationValue a (K+1) ((t n:ℂ)⁻¹):=by
      unfold truncationValue
      apply Finset.sum_congr rfl
      intro j hj
      simp only[Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,inv_pow]
      ring
    rw[hsum]
    exact hG n hn
  exact finite_vector_inverse_power_expansion_unique F t (fun j=>PowerSeries.coeff j f)
    (fun j=>PowerSeries.coeff j g) ht N (hconvert f hf) (hconvert g hg)
lemma coeff_quotient_of_product_prefix {R:Type*}[Field R]
    (f g a:PowerSeries R)(hg:PowerSeries.constantCoeff g≠0)(N:ℕ)
    (he:∀j≤N,PowerSeries.coeff j (f*g)=PowerSeries.coeff j a):
    ∀j≤N,PowerSeries.coeff j f=PowerSeries.coeff j (a*g⁻¹):=by
  intro j hj
  have hmul:f=(f*g)*g⁻¹:=by rw[mul_assoc,PowerSeries.mul_inv_cancel g hg,mul_one]
  rw[hmul,PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hvi:v.1≤N:=by
    have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
    omega
  rw[he v.1 hvi]
end WP.HigherOrder

namespace WP.HigherOrder
lemma coeff_from_product_prefix_right_inverse {R:Type*}[CommRing R]
    (f g d a:PowerSeries R)(hgd:g*d=1)(N:ℕ)
    (he:∀j≤N,PowerSeries.coeff j (f*g)=PowerSeries.coeff j a):
    ∀j≤N,PowerSeries.coeff j f=PowerSeries.coeff j (a*d):=by
  intro j hj
  have hmul:f=(f*g)*d:=by rw[mul_assoc,hgd,mul_one]
  rw[hmul,PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hvi:v.1≤N:=by
    have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
    omega
  rw[he v.1 hvi]
end WP.HigherOrder
