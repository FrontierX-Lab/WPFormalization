import WPFormalization.Intersection.CriticalCoefficient
import WPFormalization.Intersection.PureZeroBounds
noncomputable section
namespace WP
lemma endpoint_normalization_general (P:PsiTheory)(g:ℕ)(d:List ℕ)
    (hs:Stable g d.length)(hd:d.sum≤dimension g d.length):
    ratio P g d y₀=pureC P g (d++List.replicate (deficit g d) 2) := by
  let h:=complexity g d.length
  let m:=deficit g d
  have hh:1≤h:=by dsimp[h];unfold complexity;unfold Stable at hs;omega
  have hc:complexity g (d++List.replicate m 2).length=h+m:=by
    dsimp[h]
    simp only [List.length_append,List.length_replicate]
    unfold complexity
    unfold Stable at hs
    omega
  have hn:normalized P g d y₀=(3:ℝ)^m*
      (d.map (fun k=>(oddFactorial k:ℝ))).prod*pure P g (d++List.replicate m 2)/(m.factorial:ℝ):=by
    simp only [normalized,ite_true,hs,hd,and_self,if_true]
    rfl
  have hp:0<Real.Gamma (h+m:ℕ):=Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h+m by omega))
  have hf:(m.factorial:ℝ)≠0:=by positivity
  unfold ratio
  rw [hn,model_critical g d hh]
  change (3^m*(d.map (fun k=>(oddFactorial k:ℝ))).prod*pure P g (d++List.replicate m 2)/(m.factorial:ℝ)) /
    ((3:ℝ)^(h+m)*Real.Gamma (h+m:ℕ)/(4^g*5^m*m.factorial)) = _
  unfold pureC
  simp only [List.length_append,List.length_replicate] at hc
  simp only [List.map_append,List.map_replicate,List.prod_append,List.prod_replicate]
  rw [show (oddFactorial 2:ℝ)=15 by norm_num [oddFactorial,Finset.prod_range_succ]]
  simp only [List.length_append,List.length_replicate]
  change _ = (4:ℝ)^g*((d.map (fun k=>(oddFactorial k:ℝ))).prod*15^m) /
    (3^complexity g (d.length+m)*Real.Gamma (complexity g (d.length+m)))*pure P g (d++List.replicate m 2)
  rw [hc]
  rw [show (15:ℝ)=3*5 by norm_num,mul_pow]
  field_simp
  <;> ring
end WP
namespace WP
lemma critical_ratio_zero_bounds (P:PsiTheory)(g:ℕ)(d:List ℕ)
    (hs:Stable g d.length)(hd:d.sum ≤ dimension g d.length):
    (1/6:ℝ)*(2/3:ℝ)^(d.count 0) ≤ ratio P g d y₀ ∧
      ratio P g d y₀ ≤ (2:ℝ)^(d.count 0):=by
  let m:=deficit g d
  have hst:Stable g (d++List.replicate m 2).length:=by
    simp only [List.length_append,List.length_replicate]
    unfold Stable at *
    omega
  have hdim:(d++List.replicate m 2).sum=dimension g (d++List.replicate m 2).length:=by
    simp only [List.sum_append,List.sum_replicate,List.length_append,List.length_replicate,nsmul_eq_mul]
    dsimp[m]
    unfold deficit dimension
    unfold dimension at hd
    unfold Stable at hs
    omega
  have hb:=pureC_zero_bounds P g (d++List.replicate m 2) hst hdim
  rw [endpoint_normalization_general P g d hs hd]
  simpa [List.count_replicate,m] using hb
end WP
