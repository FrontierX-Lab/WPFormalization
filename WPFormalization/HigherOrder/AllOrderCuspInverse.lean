import WPFormalization.HigherOrder.SmallWeightRegion
import WPFormalization.HigherOrder.FixedMarkingGevreyScale
import WPFormalization.HigherOrder.InverseCuspBounds
import WPFormalization.HigherOrder.ScalarScaledRemainders
import WPFormalization.Statements.RecursiveRemainderTarget
/-! The actual inverse cusp inherits the explicitly supplied recursive remainder through the finite inverse identity. All scales, orders, markings and physical parameters are uniform. Fixed markings give a genuine square-root-window Gevrey-two remainder. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma finite_two_geometric_convolution (A B C D:ℝ)(hA:0 ≤ A)(hB:0 ≤ B)(hC:0 ≤ C)(hD:0 ≤ D)(N:ℕ) :
    (∑i∈Finset.range N,(A*B^i)*(C*D^(N-i))) ≤ A*C*(2*max B D)^N := by
  let R:=max B D
  have hR:0 ≤ R:=hB.trans (le_max_left _ _)
  have ht(i:ℕ)(hi:i∈Finset.range N):(A*B^i)*(C*D^(N-i)) ≤ A*C*R^N:=by
    have hiN:i ≤ N:=(Finset.mem_range.mp hi).le
    have hp:=mul_le_mul (pow_le_pow_left₀ hB (le_max_left B D) i)
      (pow_le_pow_left₀ hD (le_max_right B D) (N-i)) (pow_nonneg hD _) (pow_nonneg hR i)
    rw[←pow_add,Nat.add_sub_of_le hiN] at hp
    have hm:=mul_le_mul_of_nonneg_left hp (mul_nonneg hA hC)
    convert hm using 1 <;>ring
  apply (Finset.sum_le_sum ht).trans
  simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn:(N:ℝ) ≤ (2:ℝ)^N:=by exact_mod_cast Nat.le_of_lt N.lt_two_pow_self
  have hm:=mul_le_mul_of_nonneg_right hn (by positivity:0 ≤ A*C*R^N)
  convert hm using 1 <;>dsimp[R]<;>rw[mul_pow]<;>ring

lemma actual_cusp_inverse_scaled_uniform_of_recursiveRemainder (P:PsiTheory)
    (hr:UniformRecursiveRemainderTarget P) :
    ∃C B δ₀:ℝ,∃M₀:ℕ,0<C ∧ 0<B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p N:ℕ,1 ≤ p→Stable g p→1 ≤ complexity g p→1 ≤ N→
    scalarOrderWeight (M:ℝ) N p^2/(complexity g p:ℝ)<δ₀→∀Y∈Icc (0:ℝ) y₀,
      |(cuspCorrection P g p Y)⁻¹-truncationValue ((formalCusp P Y p)⁻¹) N (1/(complexity g p:ℝ))| ≤
        C*B^N*scalarOrderWeight (M:ℝ) N p^(2*N)/(complexity g p:ℝ)^N := by
  obtain ⟨Cr,Br,Mr,hCr,hBr,hMr,hprof,hrem⟩:=hr
  obtain ⟨Ci,Bi,Mi,hCi,hBi,hMi,hcoef⟩:=inverseCusp_coefficient_uniform_bound P
  obtain ⟨δ,hδ,hδ1,hlower⟩:=cusp_inverse_small_weight_uniform P
  let M₀:=max Mr ⌈Mi⌉₊
  have hM₀:2 ≤ M₀:=hMr.trans (le_max_left _ _)
  refine ⟨2*Ci*Cr,2*max Bi Br,δ,M₀,by positivity,by have h:=le_max_left Bi Br;positivity,hδ,hδ1,hM₀,?_⟩
  intro M hM g p N hp hs hcomp hN hsmall Y hY
  let S:=scalarOrderWeight (M:ℝ) N p
  let h:ℝ:=complexity g p
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g p by omega)
  have hMrM:Mr ≤ M:=(le_max_left _ _).trans hM
  have hMiM:Mi ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (le_max_right Mr ⌈Mi⌉₊).trans hM)
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hM0:0 ≤ (M:ℝ):=by linarith
  have hS:0 ≤ S:=by dsimp[S,scalarOrderWeight];positivity
  have hc:1/2 ≤ cuspCorrection P g p Y:=
    (hlower (M:ℝ) h hM2 hh p N hp hN hsmall g p hp (by have :=Nat.cast_nonneg (α:=ℝ) N;linarith) (by omega) Y hY).1
  have hfd:formalCusp P Y p*(formalCusp P Y p)⁻¹=1:=PowerSeries.mul_inv_cancel _ (by simp)
  have he:∀i:ℕ,0 ≤ Ci*Bi^i:=fun i=>by positivity
  have hE:∀i:ℕ,0 ≤ Cr*Br^i:=fun i=>by positivity
  have hInv:∀i<N,|PowerSeries.coeff i ((formalCusp P Y p)⁻¹)| ≤ (Ci*Bi^i)*S^(2*i):=by
    intro i hi
    have hiR:(i:ℝ) ≤ N:=by exact_mod_cast (Finset.mem_range.mp (Finset.mem_range.mpr hi)).le
    have hw:scalarOrderWeight (M:ℝ) i p ≤ S:=by
      unfold scalarOrderWeight
      dsimp[S,scalarOrderWeight]
      nlinarith
    exact (hcoef (M:ℝ) hMiM p i hp Y hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) hw (2*i)) (by positivity))
  have hCusp:∀k:ℕ,1 ≤ k→k ≤ N→
      |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) k (1/h)| ≤ (Cr*Br^k)*S^(2*k)/h^k:=by
    intro k hk hkN
    have hw:scalarOrderWeight (Mr:ℝ) k p ≤ S:=by
      have hMrR:(Mr:ℝ) ≤ M:=by exact_mod_cast hMrM
      have hkR:(k:ℝ) ≤ N:=by exact_mod_cast hkN
      have hmul:=mul_le_mul hMrR hkR (Nat.cast_nonneg k) hM0
      dsimp[S,scalarOrderWeight]
      linarith
    have hb:|cuspCorrection P g p Y-truncationValue (formalCusp P Y p) k (1/h)| ≤
        Cr*Br^k*scalarOrderWeight (Mr:ℝ) k p^(2*k)/h^k:=by
      have he:=(hrem g p hp hs hcomp k hk Y hY)
      have hhC:|cuspCorrection P g p Y-truncationValue (formalCusp P Y p) k (1/h)| ≤
          |cuspCorrection P g p Y-∑j∈Finset.range k,cuspCoefficient P Y p j/h^j|+
          |genusCorrection P g p Y-∑j∈Finset.range k,genusCoefficient P Y p j/h^j|:=by
        have heq:truncationValue (formalCusp P Y p) k (1/h)=∑j∈Finset.range k,cuspCoefficient P Y p j/h^j:=by
          simp only[truncationValue,formalCusp,PowerSeries.coeff_mk,div_pow,one_pow,mul_one_div]
        rw[heq]
        exact le_add_of_nonneg_right (abs_nonneg _)
      exact hhC.trans he
    apply hb.trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) hw (2*k)) (by positivity)) (pow_nonneg hh.le _)
  have hb:=inverse_remainder_scaled_bound (cuspCorrection P g p Y) (formalCusp P Y p) ((formalCusp P Y p)⁻¹)
    hfd hc N hN S h (fun i=>Ci*Bi^i) (fun k=>Cr*Br^k) hS hh he hE hInv hCusp
  have hsum:=finite_two_geometric_convolution Ci Bi Cr Br hCi.le hBi.le hCr.le hBr.le N
  have ht:=mul_le_mul_of_nonneg_left hsum (by positivity:0 ≤ (S^(2*N)/h^N)*2)
  apply hb.trans
  convert ht using 1 <;>dsimp[S,h]<;>ring

lemma actual_cusp_inverse_gevrey_two_of_recursiveRemainder (P:PsiTheory)
    (hr:UniformRecursiveRemainderTarget P)(p:ℕ)(hp:1 ≤ p) :
    ∃C B c:ℝ,0<C ∧ 0<B ∧ 0<c ∧∀g:ℕ,Stable g p→1 ≤ complexity g p→
    ∀N:ℕ,1 ≤ N→(N:ℝ) ≤ c*Real.sqrt (complexity g p:ℝ)→∀Y∈Icc (0:ℝ) y₀,
      |(cuspCorrection P g p Y)⁻¹-truncationValue ((formalCusp P Y p)⁻¹) N (1/(complexity g p:ℝ))| ≤
        C*B^N*(N.factorial:ℝ)^2/(complexity g p:ℝ)^N := by
  obtain ⟨C,B,δ,M,hC,hB,hδ,hδ1,hM,hscaled⟩:=actual_cusp_inverse_scaled_uniform_of_recursiveRemainder P hr
  obtain ⟨c,hc,hwindow⟩:=fixed_marking_small_sqrt_window (M:ℝ) (Nat.cast_nonneg _) p hp δ hδ
  let Q:ℝ:=((p:ℝ)+M)^2*Real.exp 2
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hm2:(2:ℝ) ≤ M:=by exact_mod_cast hM
  have hQ:0<Q:=by dsimp[Q];positivity
  refine ⟨C,B*Q,c,hC,by positivity,hc,?_⟩
  intro g hs hhN N hN horder Y hY
  have hh:0<(complexity g p:ℝ):=by exact_mod_cast (show 0<complexity g p by omega)
  have hsmall:=hwindow (complexity g p:ℝ) hh N hN horder
  have hb:=hscaled M le_rfl g p N hp hs hhN hN hsmall Y hY
  have hsBound:=fixed_marking_order_weight_factorial (M:ℝ) (Nat.cast_nonneg _) p N hN
  apply hb.trans
  have hm:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsBound (by positivity:0 ≤ C*B^N)) (pow_nonneg hh.le N)
  convert hm using 1 <;> (try dsimp[Q]) <;> (try rw[mul_pow]) <;>ring
end WP.HigherOrder
