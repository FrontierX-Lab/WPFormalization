import WPFormalization.Tight.ShiftedPolynomial
/-! Exact normalization of the classical universal moment polynomial.
Only algebraic specialization is proved; no geometric moment input is asserted. -/
noncomputable section
namespace WP
open Set Filter
open scoped Topology
namespace TightMoments
/-- The universal finite descendant polynomial in the moment variables of
Budd--Zonneveld. No realization as a geometric tight volume is assumed here. -/
def momentAmplitude (P:PsiTheory) (g:ℕ) (d:List ℕ) (M:ℕ→ℝ):ℝ:=
  if Stable g d.length ∧ d.sum≤dimension g d.length then
    ∑l∈backgrounds (deficit g d),pure P g (d++backgroundDegrees l)*
      (∏i:Fin (deficit g d),(-M (i.val+1))^(l i)/(l i).factorial)/
        M 0^(complexity g d.length+∑i,l i)
  else 0

def momentPolynomial (P:PsiTheory) (g p:ℕ) (M:ℕ→ℝ) (L:Fin p→ℝ):ℝ:=
  ∑d∈degreeTuples g p,momentAmplitude P g (List.ofFn d) M*
    ∏i,L i^(2*d i)/((2:ℝ)^(d i)*(d i).factorial)

def planeMoments (Y:ℝ) (j:ℕ):ℝ:=(iteratedDeriv (j+1) X Y).re
lemma planeMoments_zero (Y:ℝ):planeMoments Y 0=a Y:=by
  simp only [planeMoments,zero_add,iteratedDeriv_one,a]
lemma shifted_eq_momentAmplitude (P:PsiTheory) (g:ℕ) (d:List ℕ) (Y:ℝ):
    shifted P g d Y=(d.map (fun k=>(oddFactorial k:ℝ))).prod*
      momentAmplitude P g d (planeMoments Y):=by
  unfold shifted momentAmplitude
  split_ifs with h
  · simp only [planeMoments,Nat.add_assoc,Nat.reduceAdd,iteratedDeriv_one,a]
  · simp
lemma momentAmplitude_scale (P:PsiTheory) (g:ℕ) (d:List ℕ) (M:ℕ→ℝ) (c:ℝ):
    momentAmplitude P g d (fun j=>c^j*M j)=
      c^(deficit g d)*momentAmplitude P g d M:=by
  unfold momentAmplitude
  split_ifs with h
  · simp only [pow_zero,one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hdeg:∑i:Fin (deficit g d),(i.val+1)*l i=deficit g d:=
      (mem_backgrounds_iff _ _).mp hl
    have hp:(∏i:Fin (deficit g d),(-(c^(i.val+1)*M (i.val+1)))^(l i)/(l i).factorial)=
        c^(deficit g d)*(∏i:Fin (deficit g d),(-M (i.val+1))^(l i)/(l i).factorial):=by
      simp_rw [show ∀ i:Fin (deficit g d),-(c^(i.val+1)*M (i.val+1))=
        c^(i.val+1)*(-M (i.val+1)) by intro i;ring,mul_pow,←pow_mul]
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hdeg]
    rw [hp]
    ring
  · simp
lemma oddFactorial_length_coefficient (L c:ℝ) (hc:c≠0) (d:ℕ):
    (oddFactorial d:ℝ)*(L^(2*d)/(c^d*(2*d+1).factorial))=
      (L^(2*d)/((2:ℝ)^d*d.factorial))/c^d:=by
  have ho:(d.factorial:ℝ)*(oddFactorial d:ℝ)*(2:ℝ)^d=((2*d+1).factorial:ℝ):=by
    exact_mod_cast Analysis.oddFactorial_factorial d
  rw [←ho]
  have hodd:(oddFactorial d:ℝ)≠0:=by exact_mod_cast (oddFactorial_pos d).ne'
  have hfac:(d.factorial:ℝ)≠0:=by positivity
  field_simp
  <;>ring
lemma oddFactorial_length_product (p:ℕ) (L:Fin p→ℝ) (c:ℝ) (hc:c≠0) (d:Fin p→ℕ):
    (∏i,(oddFactorial (d i):ℝ))*
      (∏i,L i^(2*d i)/(c^(d i)*(2*d i+1).factorial))=
    (∏i,L i^(2*d i)/((2:ℝ)^(d i)*(d i).factorial))/c^(∑i,d i):=by
  rw [←Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact oddFactorial_length_coefficient (L i) c hc (d i)

lemma momentPolynomial_scale_to_shifted (P:PsiTheory) (g p:ℕ) (Y:ℝ) (L:Fin p→ℝ):
    momentPolynomial P g p (fun j=>(2*Real.pi^2)^j*planeMoments Y j) L /
      (2*Real.pi^2)^(dimension g p)=tightShiftedPolynomial P g p Y L := by
  have hc:(2*Real.pi^2:ℝ)≠0:=by positivity
  unfold momentPolynomial tightShiftedPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg:(List.ofFn d).sum≤dimension g (List.ofFn d).length:=by
    simpa only [List.sum_ofFn,List.length_ofFn] using (mem_degreeTuples_iff g p d).mp hd
  have hD:dimension g p=deficit g (List.ofFn d)+∑i,d i:=by
    unfold deficit
    simp only [List.length_ofFn,List.sum_ofFn] at *
    omega
  rw [momentAmplitude_scale,shifted_eq_momentAmplitude]
  have ho:((List.ofFn d).map (fun k=>(oddFactorial k:ℝ))).prod=∏i,(oddFactorial (d i):ℝ):=by
    simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def]
  rw [ho]
  rw [show (∏i,(oddFactorial (d i):ℝ))*momentAmplitude P g (List.ofFn d) (planeMoments Y)*
      (∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial))=
    momentAmplitude P g (List.ofFn d) (planeMoments Y)*
      ((∏i,(oddFactorial (d i):ℝ))*
        ∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial)) by ring,
    oddFactorial_length_product p L (2*Real.pi^2) hc d,hD,pow_add]
  field_simp [hc]
end TightMoments

end WP
