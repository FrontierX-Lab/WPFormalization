import WPFormalization.Statements.Basic

/-! Positive convergent products control the sum of their increments.
Applying the finite product inequality to the norm of a genus-zero product
at minus one proves reciprocal-root summability with no new external input. -/
noncomputable section
namespace WP.Analysis
open Set
lemma one_add_sum_le_prod_one_add {ι:Type*} (f:ι→ℝ) (hf:∀i,0≤f i) (s:Finset ι) :
    1+∑i∈s,f i ≤ ∏i∈s,(1+f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,Finset.prod_insert ha]
    calc
      _ ≤ (1+f a)*(1+∑i∈s,f i) := by
        have hs0 : 0 ≤ ∑i∈s,f i := Finset.sum_nonneg (fun i _=>hf i)
        nlinarith [mul_nonneg (hf a) hs0]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (by linarith [hf a])
lemma summable_of_hasProd_one_add_nonneg {ι:Type*} (f:ι→ℝ) (hf:∀i,0≤f i)
    (P:ℝ) (hp:HasProd (fun i=>1+f i) P) : Summable f := by
  apply summable_of_sum_le hf (c:=P)
  intro s
  have hprod: (∏i∈s,(1+f i)) ≤ P := prod_le_hasProd_of_nonneg
    (fun i _=>by linarith [hf i]) (fun i _=>by linarith [hf i]) hp
  have hs:=one_add_sum_le_prod_one_add f hf s
  linarith
lemma reciprocal_summable_of_positive_product (a:ℕ→ℝ) (ha:∀i,0<a i)
    (F:ℂ→ℂ) (hprod:∀z:ℂ,HasProd (fun i=>1-z/(a i:ℂ)) (F z)) :
    Summable (fun i=>(a i)⁻¹) := by
  have hn:HasProd (fun i=>1+(a i)⁻¹) ‖F (-1)‖ := by
    have hp:=(hprod (-1)).norm
    convert hp using 1
    funext i
    have he:1-(-1:ℂ)/(a i:ℂ)=((1+(a i)⁻¹:ℝ):ℂ):=by push_cast;ring
    have hposi:0<1+(a i)⁻¹:=by linarith [inv_pos.mpr (ha i)]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hposi]
  exact summable_of_hasProd_one_add_nonneg _ (fun i=>(inv_pos.mpr (ha i)).le) _ hn
end WP.Analysis
