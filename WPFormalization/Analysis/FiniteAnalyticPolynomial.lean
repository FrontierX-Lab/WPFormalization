import Mathlib
/-! Finite scalar-analytic polynomial operations, polynomial moments, and formal unit inverses. -/
noncomputable section
namespace WP.Analysis
open Set Filter Polynomial
open scoped Topology

structure FiniteAnalyticPolynomialAt (F:ℝ→Polynomial ℝ)(x:ℝ):Prop where
  bound : ∃N:ℕ,∀y,(F y).natDegree≤N
  analytic : ∀n:ℕ,AnalyticAt ℝ (fun y=>(F y).coeff n) x
namespace FiniteAnalyticPolynomialAt
variable {F G:ℝ→Polynomial ℝ} {x:ℝ}
lemma const (q:Polynomial ℝ):FiniteAnalyticPolynomialAt (fun _=>q) x:=
  ⟨⟨q.natDegree,fun _=>le_rfl⟩,fun _=>analyticAt_const⟩
lemma C (a:ℝ→ℝ)(ha:AnalyticAt ℝ a x):FiniteAnalyticPolynomialAt (fun y=>Polynomial.C (a y)) x:=by
  refine ⟨⟨0,fun y=>by simp⟩,?_⟩
  intro n
  by_cases hn:n=0
  · subst n;simpa only[Polynomial.coeff_C,ite_true] using ha
  · simpa only[Polynomial.coeff_C,ite_eq_right hn] using (analyticAt_const:AnalyticAt ℝ (fun _:ℝ=>(0:ℝ)) x)
lemma monomial (n:ℕ)(a:ℝ→ℝ)(ha:AnalyticAt ℝ a x):
    FiniteAnalyticPolynomialAt (fun y=>Polynomial.monomial n (a y)) x:=by
  refine ⟨⟨n,fun y=>Polynomial.natDegree_monomial_le (a y)⟩,?_⟩
  intro m
  by_cases hm:n=m
  · subst m;simpa only[Polynomial.coeff_monomial,ite_true] using ha
  · simpa only[Polynomial.coeff_monomial,ite_eq_right hm] using (analyticAt_const:AnalyticAt ℝ (fun _:ℝ=>(0:ℝ)) x)
lemma add (hF:FiniteAnalyticPolynomialAt F x)(hG:FiniteAnalyticPolynomialAt G x):
    FiniteAnalyticPolynomialAt (fun y=>F y+G y) x:=by
  obtain ⟨N,hN⟩:=hF.bound
  obtain ⟨M,hM⟩:=hG.bound
  refine ⟨⟨max N M,fun y=>(Polynomial.natDegree_add_le (F y) (G y)).trans (max_le_max (hN y) (hM y))⟩,?_⟩
  intro n
  simpa only[Polynomial.coeff_add,Pi.add_def] using (hF.analytic n).add (hG.analytic n)
lemma mul (hF:FiniteAnalyticPolynomialAt F x)(hG:FiniteAnalyticPolynomialAt G x):
    FiniteAnalyticPolynomialAt (fun y=>F y*G y) x:=by
  obtain ⟨N,hN⟩:=hF.bound
  obtain ⟨M,hM⟩:=hG.bound
  refine ⟨⟨N+M,fun y=>(Polynomial.natDegree_mul_le).trans (add_le_add (hN y) (hM y))⟩,?_⟩
  intro n
  simp_rw[Polynomial.coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun i hi=>(hF.analytic i.1).mul (hG.analytic i.2))
lemma sum {ι:Type*}(s:Finset ι)(f:ι→ℝ→Polynomial ℝ)(hf:∀i∈s,FiniteAnalyticPolynomialAt (f i) x):
    FiniteAnalyticPolynomialAt (fun y=>∑i∈s,f i y) x:=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa only[Finset.sum_empty] using const (x:=x) 0
  | @insert i s hi ih=>
    simpa only[Finset.sum_insert hi] using (hf i (by simp)).add (ih (fun j hj=>hf j (by simp[hj])))
lemma finiteMoment (hF:FiniteAnalyticPolynomialAt F x)(ω:ℕ→ℝ):
    AnalyticAt ℝ (fun y=>(F y).sum (fun n a=>a*ω n)) x:=by
  obtain ⟨N,hN⟩:=hF.bound
  have he:∀y,(F y).sum (fun n a=>a*ω n)=
      ∑n∈Finset.range (N+1),(F y).coeff n*ω n:=by
    intro y
    apply Polynomial.sum_eq_of_subset _ (by intro i;simp)
    intro n hn
    have hcoeff:(F y).coeff n≠0:=Polynomial.mem_support_iff.mp hn
    have hnd:n≤(F y).natDegree:=Polynomial.le_natDegree_of_ne_zero hcoeff
    exact Finset.mem_range.mpr (by have ht:=hN y;omega)
  simp_rw[he]
  exact Finset.analyticAt_fun_sum _ (fun n hn=>(hF.analytic n).mul analyticAt_const)
end FiniteAnalyticPolynomialAt
lemma finiteAnalyticPolynomialAt_series_coeff_pow (F:ℝ→PowerSeries (Polynomial ℝ))(x:ℝ)
    (hF:∀n,FiniteAnalyticPolynomialAt (fun y=>PowerSeries.coeff n (F y)) x)(k n:ℕ):
    FiniteAnalyticPolynomialAt (fun y=>PowerSeries.coeff n ((F y)^k)) x:=by
  induction k generalizing n with
  | zero=>simpa only[pow_zero] using FiniteAnalyticPolynomialAt.const (x:=x) (PowerSeries.coeff n (1:PowerSeries (Polynomial ℝ)))
  | succ k ih=>
    simp_rw[pow_succ,PowerSeries.coeff_mul]
    exact FiniteAnalyticPolynomialAt.sum _ _ (fun i hi=>(ih i.1).mul (hF i.2))

lemma real_sqrt_analyticAt_of_pos (f:ℝ→ℝ)(x:ℝ)(hf:AnalyticAt ℝ f x)(hpos:0<f x):
    AnalyticAt ℝ (fun y=>Real.sqrt (f y)) x:=by
  have hfc:AnalyticAt ℝ (fun y=>(f y:ℂ)) x:=(Complex.ofRealCLM.analyticAt _).comp hf
  have hs:AnalyticAt ℝ (fun y=>Complex.sqrt ((f y:ℝ):ℂ)) x:=
    (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane _ (Or.inl hpos)).restrictScalars.comp hfc
  have hre:AnalyticAt ℝ (fun y=>(Complex.sqrt ((f y:ℝ):ℂ)).re) x:=
    (Complex.reCLM.analyticAt _).comp hs
  apply hre.congr
  filter_upwards[hf.continuousAt.tendsto.eventually (eventually_gt_nhds hpos)] with y hy
  simpa only[Complex.ofReal_re] using (congrArg Complex.re (Complex.sqrt_of_nonneg (a:=((f y:ℝ):ℂ)) (by exact_mod_cast hy.le)))
end WP.Analysis
namespace WP.Analysis
open PowerSeries

def AnalyticSeriesCoefficientsAt (F:ℝ→PowerSeries ℝ)(x:ℝ):Prop:=
  ∀n:ℕ,AnalyticAt ℝ (fun y=>PowerSeries.coeff n (F y)) x
namespace AnalyticSeriesCoefficientsAt
variable {F G:ℝ→PowerSeries ℝ} {x:ℝ}
lemma mul (hF:AnalyticSeriesCoefficientsAt F x)(hG:AnalyticSeriesCoefficientsAt G x):
    AnalyticSeriesCoefficientsAt (fun y=>F y*G y) x:=by
  intro n
  simp_rw[PowerSeries.coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun i hi=>(hF i.1).mul (hG i.2))
lemma inv (hF:AnalyticSeriesCoefficientsAt F x)(h0:PowerSeries.constantCoeff (F x)≠0):
    AnalyticSeriesCoefficientsAt (fun y=>(F y)⁻¹) x:=by
  have hc:AnalyticAt ℝ (fun y=>PowerSeries.constantCoeff (F y)) x:=by
    simpa only[PowerSeries.coeff_zero_eq_constantCoeff] using hF 0
  have hci:=hc.inv h0
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n=0
    · subst n
      simpa only[PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,Pi.inv_def] using hci
    · have he:(fun y=>PowerSeries.coeff n ((F y)⁻¹))=(fun y=>
          -(PowerSeries.constantCoeff (F y))⁻¹*
            ∑i∈Finset.HasAntidiagonal.antidiagonal n,if i.2<n then
              PowerSeries.coeff i.1 (F y)*PowerSeries.coeff i.2 ((F y)⁻¹) else 0):=by
        funext y
        rw[PowerSeries.coeff_inv,ite_eq_right hn]
      rw[he]
      apply hci.neg.mul
      apply Finset.analyticAt_fun_sum
      intro i hi
      by_cases hlt:i.2<n
      · simp only[ite_eq_left hlt]
        exact (hF i.1).mul (ih i.2 hlt)
      · simp only[ite_eq_right hlt]
        exact analyticAt_const
end AnalyticSeriesCoefficientsAt
end WP.Analysis
