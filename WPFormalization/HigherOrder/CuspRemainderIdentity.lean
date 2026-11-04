import WPFormalization.HigherOrder.LargeWeightRemainder
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.HierarchyIdentities
import WPFormalization.Analysis.FactorialKernelMoments
import WPFormalization.Marked.CuspFromProfile
/-! The actual dilaton operator paired with the canonical formal cusp
rule at every finite order. The weighted shifted-head coefficient sums
are genuinely absolutely summable, from the proved C.4 bounds and true
signed-b moments. The exact finite-background dilaton identity and the
formal rule then give a true HasSum of actual child remainders, without
assuming a completed hierarchy error recurrence or remainder bounds. -/
noncomputable section
open Set
namespace WP.HigherOrder
open PowerSeries
lemma shifted_head_coeff_summable (P:PsiTheory) (p n:ℕ) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>bCoeff Y (l+1)*PowerSeries.coeff n
      (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0)))) :=by
  obtain ⟨C,B,M,hC,hB,hM,hprof,hscal⟩:=canonical_real_coefficient_bounds P
  let e:ℕ→ℝ:=fun i=>C*B^i
  have he:∀i:ℕ,0 ≤ e i:=fun i=>by dsimp[e];positivity
  let J:=PowerSeries.coeff n ((PowerSeries.exp ℝ)*PowerSeries.mk e)
  have hJ:0 ≤ J:=coeff_mul_nonneg exp_coeff_nonneg (fun i=>by simpa only[PowerSeries.coeff_mk] using he i) n
  let T:ℝ:=(p:ℝ)+(M:ℝ)*(n+1)+3
  have hT:0 ≤ T:=by dsimp[T];positivity
  have hM1:(1:ℝ) ≤ M:=by exact_mod_cast (show 1 ≤ M by omega)
  have hpoint (l:ℕ) :
      |PowerSeries.coeff n (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0)))| ≤
        (J*(T+1)^(2*n))*((l:ℝ)+2)^(2*n):=by
    have hSl:((n+1:ℕ):ℝ) ≤ T+l+1:=by
      have hm:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
      dsimp[T]
      simp only[Nat.cast_add,Nat.cast_one] at hm ⊢
      nlinarith[Nat.cast_nonneg (α:=ℝ) p,Nat.cast_nonneg (α:=ℝ) l]
    have hbound:=complexityShift_coeff_exponential_majorant (-1) (T+l+1)
      (formalProfile P Y ((l+1)::List.replicate p 0)) e n (n+1) (by omega) (by norm_num) hSl he (by
        intro i hi
        have hb:=hprof i ((l+1)::List.replicate p 0) (by simp) Y hY
        have hiM:=mul_le_mul_of_nonneg_left
          (show (i:ℝ) ≤ n+1 by exact_mod_cast (show i ≤ n+1 by omega)) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
        have hweight:profileOrderWeight (M:ℝ) i ((l+1)::List.replicate p 0) ≤ T+l+1:=by
          simp only[profileOrderWeight,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,
            List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one]
          dsimp[T]
          linarith
        simpa only[formalProfile,PowerSeries.coeff_mk,e] using hb.trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) hweight (2*i))
            (show 0 ≤ C*B^i by positivity)))
    have hbase:T+l+1 ≤ (T+1)*((l:ℝ)+2):=by nlinarith[Nat.cast_nonneg (α:=ℝ) l,mul_nonneg hT (Nat.cast_nonneg (α:=ℝ) l)]
    have hpow: (T+l+1)^(2*n) ≤ ((T+1)*((l:ℝ)+2))^(2*n):=
      pow_le_pow_left₀ (by positivity) hbase _
    exact hbound.trans (by dsimp[J];convert mul_le_mul_of_nonneg_right hpow hJ using 1 <;>rw[mul_pow]<;>ring)
  obtain ⟨Cb,Bb,hCb,hBb,hbm⟩:=Analysis.dilaton_factorial_moments
  have hs0:Summable (fun l:ℕ=>(((l+1:ℕ):ℝ)+1)^(2*n)*|canonicalDilatonCoefficient Y (l+1)|):=
    (hbm (2*n) Y hY).1.comp_injective (fun i j hij=>Nat.add_right_cancel hij)
  have hs:Summable (fun l:ℕ=>((l:ℝ)+2)^(2*n)*|bCoeff Y (l+1)|):=by
    simpa only[bCoeff_eq_canonicalDilatonCoefficient,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hs0
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun l=>norm_nonneg _) _ (hs.mul_left (J*(T+1)^(2*n)))
  intro l
  rw[Real.norm_eq_abs,abs_mul]
  convert mul_le_mul_of_nonneg_left (hpoint l) (abs_nonneg (bCoeff Y (l+1))) using 1 <;>ring

lemma actual_cusp_hasSum (P:PsiTheory) (g p:ℕ) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>(A Y)⁻¹*bCoeff Y (l+1)*profile P g ((l+1)::List.replicate p 0) Y)
      (cuspCorrection P g p Y) :=by
  have hf:HasSum (fun l:ℕ=>bCoeff Y (l+1)*profile P g ((l+1)::List.replicate p 0) Y)
      (∑l∈Finset.range (dimension g (p+1)),bCoeff Y (l+1)*profile P g ((l+1)::List.replicate p 0) Y):=by
    apply hasSum_sum_of_ne_finset_zero
    intro l hl
    have hlD:dimension g (p+1) ≤ l:=by simpa only[Finset.mem_range,not_lt] using hl
    rw[profile_excess_zero P g _ Y (by
      simp only[List.length_cons,List.length_replicate,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero]
      omega),mul_zero]
  have he:=canonical_dilaton_profile_sum_stable P g p hs Y hY
  simp only[←bCoeff_eq_canonicalDilatonCoefficient] at he
  rw[←he] at hf
  convert hf.mul_left (A Y)⁻¹ using 1
  · funext l
    ring
  · unfold cuspCorrection
    ring
lemma formal_cusp_truncation_hasSum (P:PsiTheory) (p L:ℕ) (Y t:ℝ)
    (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>(A Y)⁻¹*bCoeff Y (l+1)*
      truncationValue (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0))) L t)
      (truncationValue (formalCusp P Y p) L t) :=by
  have hcoeff (j:ℕ):PowerSeries.coeff j (formalCusp P Y p)=
      (A Y)⁻¹*(∑'l:ℕ,bCoeff Y (l+1)*PowerSeries.coeff j
        (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0)))):=by
    rw[formalCusp_recursion P Y hY p]
    simp only[cuspSeries,PowerSeries.coeff_C_mul,coefficientSum_coeff]
  have hsumj (j:ℕ) :HasSum (fun l:ℕ=>(A Y)⁻¹*bCoeff Y (l+1)*
      PowerSeries.coeff j (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0)))*t^j)
      (PowerSeries.coeff j (formalCusp P Y p)*t^j):=by
    have hh:=((shifted_head_coeff_summable P p j Y hY).hasSum.mul_left (A Y)⁻¹).mul_right (t^j)
    rw[←hcoeff] at hh
    convert hh using 1
    funext l
    ring
  have hsum:=hasSum_sum (s:=Finset.range L) (fun j hj=>hsumj j)
  convert hsum using 1
  · funext l
    simp only[truncationValue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rfl

lemma actual_cusp_remainder_hasSum (P:PsiTheory) (g p L:ℕ) (hs:Stable g p)
    (Y t:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>(A Y)⁻¹*bCoeff Y (l+1)*
      (profile P g ((l+1)::List.replicate p 0) Y-
        truncationValue (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0))) L t))
      (cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L t) :=by
  have hh:=(actual_cusp_hasSum P g p hs Y hY).sub (formal_cusp_truncation_hasSum P p L Y t hY)
  convert hh using 1
  funext l
  ring

lemma actual_cusp_remainder_bound (P:PsiTheory) (g p L:ℕ) (hs:Stable g p)
    (Y t:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L t| ≤
      |(A Y)⁻¹| *(∑'l:ℕ,|bCoeff Y (l+1)| *
      |profile P g ((l+1)::List.replicate p 0) Y-
        truncationValue (complexityShift (-1) (formalProfile P Y ((l+1)::List.replicate p 0))) L t|) :=by
  have hh:=actual_cusp_remainder_hasSum P g p L hs Y t hY
  have he:=norm_tsum_le_tsum_norm hh.summable.norm
  rw[hh.tsum_eq] at he
  simpa only[Real.norm_eq_abs,abs_mul,mul_assoc,tsum_mul_left] using he
end WP.HigherOrder
