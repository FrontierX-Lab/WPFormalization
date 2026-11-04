import WPFormalization.HigherOrder.RatioFactorBounds
import WPFormalization.HigherOrder.TwoScaleShiftRemainder
import WPFormalization.HigherOrder.CanonicalCoefficientScales
/-! Genuine shifted actual child profiles have uniform finite remainders
from their strictly earlier truncation orders. Only the parent scale controls
the inverse-complexity geometry; the child scale may grow without bound. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma actual_shifted_profile_previous_step (P:PsiTheory) :
    ∃C B D:ℝ,∃M₀:ℕ,0<C ∧ 1 ≤ B ∧ 0<D ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g':ℕ,∀d:List ℕ,1 ≤ d.length→Stable g' d.length→
    ∀L q:ℕ,1 ≤ q→q<L→∀c S T h:ℝ,|c| ≤ L→2*(L:ℝ) ≤ S→S ≤ T→0<h→S^2/h ≤ 1→
    (complexity g' d.length:ℝ)=h-c→profileOrderWeight (M:ℝ) q d ≤ T→
    ∀Y∈Icc (0:ℝ) y₀,∀EP:ℕ→ℝ,(∀m,0 ≤ EP m)→
    (∀m:ℕ,1 ≤ m→m ≤ q→
      |profile P g' d Y-truncationValue (formalProfile P Y d) m (1/(complexity g' d.length:ℝ))| ≤
        EP m*profileOrderWeight (M:ℝ) m d^(2*m)/(complexity g' d.length:ℝ)^m)→
    (∀i<q,|PowerSeries.coeff i (complexityShift c (formalProfile P Y d))| ≤ C*B^i*T^(2*i)) ∧
    (∀m:ℕ,1 ≤ m→m ≤ q→
      |profile P g' d Y-truncationValue (complexityShift c (formalProfile P Y d)) m (1/h)| ≤
        D*(EP m+B^m)*T^(2*m)/h^m) := by
  obtain ⟨C,B,M₀,hC,hB,hM₀,hprof,hscalar⟩:=canonical_real_coefficient_bounds P
  let B':=2*max B 1
  let D:=Real.exp 2*(1+C)
  have hB':1 ≤ B':=by dsimp[B'];have :=le_max_right B 1;linarith
  have hD:0<D:=by dsimp[D];positivity
  refine ⟨2*C,B',D,M₀,by positivity,hB',hD,hM₀,?_⟩
  intro M hM g' d hd hs L q hq hqL c S T h hc hS hST hh hsmall hcomp hT Y hY EP hEP hprofile
  have hL:1 ≤ L:=by omega
  have hS0:0 ≤ S:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hT0:0 ≤ T:=hS0.trans hST
  have hML:(M₀:ℝ) ≤ M:=by exact_mod_cast hM
  have hweight(i:ℕ)(hi:i ≤ q):profileOrderWeight (M:ℝ) i d ≤ T:=by
    apply LE.le.trans _ hT
    have hm:=mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ q by exact_mod_cast hi) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    unfold profileOrderWeight
    linarith
  have hraw(i:ℕ)(hi:i ≤ q):|PowerSeries.coeff i (formalProfile P Y d)| ≤ C*B^i*T^(2*i):=by
    have hw:profileOrderWeight (M₀:ℝ) i d ≤ T:=by
      apply LE.le.trans _ (hweight i hi)
      have hm:=mul_le_mul_of_nonneg_right hML (Nat.cast_nonneg i : (0:ℝ) ≤ i)
      unfold profileOrderWeight
      linarith
    have hb:=(hprof i d hd Y hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) hw (2*i)) (by positivity))
    simpa only[formalProfile,PowerSeries.coeff_mk] using hb
  constructor
  · intro i hi
    have hb:=complexityShift_coeff_scaled_bound c T (formalProfile P Y d) (fun k=>C*B^k) i L (by omega) hc (by linarith)
      (fun k=>by positivity) (fun k hk=>hraw k (by omega))
    have hcBound:=factorial_convolution_geometric_bound_succ C B hC.le hB.le i
    apply hb.trans
    have ht:=mul_le_mul_of_nonneg_left hcBound (pow_nonneg hT0 (2*i))
    convert ht using 1 <;>dsimp[B']<;>ring
  · intro m hm hmq
    have hactual:|profile P g' d Y-truncationValue (formalProfile P Y d) m (1/(h-c))| ≤
        EP m*T^(2*m)/(h-c)^m:=by
      rw[←hcomp]
      apply (hprofile m hm hmq).trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) (hweight m hmq) (2*m)) (hEP m)
    have hb:=shifted_remainder_with_budget_two_scale (profile P g' d Y) (EP m) (formalProfile P Y d)
      (fun i=>C*B^i) m L hm (by omega) c S T h 1 hc hS hST hh hsmall (by norm_num)
      (hEP m) (fun i=>by positivity) (fun i hi=>hraw i (by omega)) hactual
    have hknown:=factorial_convolution_geometric_bound C B hC.le hB.le m
    have hforce:Real.exp 2*(EP m+∑i∈Finset.range m,C*B^i/((m-i).factorial:ℝ)) ≤ D*(EP m+B'^m):=by
      have hEPm:=hEP m
      have hBp:0 ≤ B'^m:=by positivity
      have h1:EP m+C*B'^m ≤ (1+C)*(EP m+B'^m):=by nlinarith
      have hs:EP m+∑i∈Finset.range m,C*B^i/((m-i).factorial:ℝ) ≤ (1+C)*(EP m+B'^m):=
        by linarith[hknown]
      have ht:=mul_le_mul_of_nonneg_left hs (Real.exp_nonneg 2)
      convert ht using 1 <;>dsimp[D]<;>ring
    norm_num only[mul_one] at hb
    apply hb.trans
    have ht:=mul_le_mul_of_nonneg_left hforce (by positivity:0 ≤ T^(2*m)/h^m)
    convert ht using 1 <;>ring

end WP.HigherOrder
