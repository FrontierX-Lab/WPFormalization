import WPFormalization.HigherOrder.ShiftExtraction

/-! Finite normalized coefficient majorants for actual formal products. The norm estimates work over both real and complex coefficient rings and use only coefficients up to the requested order. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma coeff_mul_nonneg {F G:Series} (hF:∀n,0≤PowerSeries.coeff n F) (hG:∀n,0≤PowerSeries.coeff n G) :
    ∀n,0≤PowerSeries.coeff n (F*G) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg (fun ij hij=>mul_nonneg (hF ij.1) (hG ij.2))

lemma coeff_prod_nonneg {ι:Type*} (s:Finset ι) (F:ι→Series)
    (hF:∀i∈s,∀n,0≤PowerSeries.coeff n (F i)) : ∀n,0≤PowerSeries.coeff n (∏i∈s,F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n;simp only [Finset.prod_empty,PowerSeries.coeff_one];split_ifs <;>norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact coeff_mul_nonneg (hF i (Finset.mem_insert_self _ _))
      (ih (fun k hk=>hF k (Finset.mem_insert_of_mem hk)))

lemma scaled_coeff_mul_bound {𝕜:Type*} [NormedCommRing 𝕜] (f g:PowerSeries 𝕜) (F G:Series)
    (S:ℝ) (hS:0≤S) (n:ℕ)
    (hF:∀k,0≤PowerSeries.coeff k F) (hG:∀k,0≤PowerSeries.coeff k G)
    (hf:∀k:ℕ,k≤n→‖PowerSeries.coeff k f‖≤S^(2*k)*PowerSeries.coeff k F)
    (hg:∀k:ℕ,k≤n→‖PowerSeries.coeff k g‖≤S^(2*k)*PowerSeries.coeff k G) :
    ‖PowerSeries.coeff n (f*g)‖≤S^(2*n)*PowerSeries.coeff n (F*G) := by
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have hs:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hi:ij.1≤n:=by omega
  have hj:ij.2≤n:=by omega
  calc _≤‖PowerSeries.coeff ij.1 f‖*‖PowerSeries.coeff ij.2 g‖:=norm_mul_le _ _
       _≤(S^(2*ij.1)*PowerSeries.coeff ij.1 F)*(S^(2*ij.2)*PowerSeries.coeff ij.2 G):=
         mul_le_mul (hf _ hi) (hg _ hj) (norm_nonneg _) (mul_nonneg (pow_nonneg hS _) (hF _))
       _=S^(2*n)*(PowerSeries.coeff ij.1 F*PowerSeries.coeff ij.2 G):=by
         have hp:S^(2*ij.1)*S^(2*ij.2)=S^(2*n):=by rw [←pow_add];congr 1;omega
         calc _=(S^(2*ij.1)*S^(2*ij.2))*(PowerSeries.coeff ij.1 F*PowerSeries.coeff ij.2 G):=by ring
              _=_:=by rw [hp]

lemma scaled_coeff_prod_bound {𝕜 ι:Type*} [NormedCommRing 𝕜] [NormOneClass 𝕜] (s:Finset ι)
    (f:ι→PowerSeries 𝕜) (F:ι→Series) (S:ℝ) (hS:0≤S)
    (hF:∀i∈s,∀k,0≤PowerSeries.coeff k (F i)) (n:ℕ)
    (hf:∀i∈s,∀k:ℕ,k≤n→‖PowerSeries.coeff k (f i)‖≤S^(2*k)*PowerSeries.coeff k (F i)) :
    ‖PowerSeries.coeff n (∏i∈s,f i)‖≤S^(2*n)*PowerSeries.coeff n (∏i∈s,F i) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty,PowerSeries.coeff_one]
    split_ifs with hn
    · subst n;simp
    · simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    apply scaled_coeff_mul_bound _ _ _ _ S hS n
    · exact hF i (Finset.mem_insert_self _ _)
    · exact coeff_prod_nonneg s F (fun k hk=>hF k (Finset.mem_insert_of_mem hk))
    · exact hf i (Finset.mem_insert_self _ _)
    · intro k hk
      exact ih (fun i hi=>hF i (Finset.mem_insert_of_mem hi)) k
        (fun i hi l hl=>hf i (Finset.mem_insert_of_mem hi) l (hl.trans hk))
end WP.HigherOrder
