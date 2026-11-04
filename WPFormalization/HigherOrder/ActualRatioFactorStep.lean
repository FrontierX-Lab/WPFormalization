import WPFormalization.HigherOrder.RatioFactorBounds
import WPFormalization.HigherOrder.CanonicalCoefficientScales
/-! Each actual C.14 scalar factor is controlled by genuine strictly
previous-order cusp/genus remainders at its own stable state. The true child
complexity h-r+a and unchanged genus complexity are proved, the real C.4
bounds supply all known coefficients, and C.5(d) supplies the common scale.
No complete large-ratio remainder is assumed. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma actual_ratio_factor_uniform_step (P:PsiTheory) :
    ∃ C B D:ℝ,∃M₀:ℕ,0<C ∧ 1 ≤ B ∧ 0<D ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p j s L:ℕ,j ≤ g→s<p→Stable (g-j) (p-s)→1 ≤ 2*j+s→2*j+s<L→
    ∀Y∈Icc (0:ℝ) y₀,
    scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ) ≤ 1→
    ∀EC EG:ℕ→ℝ,(∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    ∀a<(2*j+s)+j,
      (∀i<L-(2*j+s),|PowerSeries.coeff i (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a)| ≤
        C*B^i*scalarOrderWeight (M:ℝ) L p^(2*i)) ∧
      (∀m:ℕ,1 ≤ m→m ≤ L-(2*j+s)→
        |actualLargeRatioFactor P g p j s Y a-
          truncationValue (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a) m (1/(complexity g p:ℝ))| ≤
          D*(EC m+EG m+B^m)*scalarOrderWeight (M:ℝ) L p^(2*m)/(complexity g p:ℝ)^m) := by
  obtain ⟨C,B,M₀,hC,hB,hM₀,hprof,hscalar⟩:=canonical_real_coefficient_bounds P
  let K:=max C (2*(max 1 (2*C))^2)
  let B':=4*max B 1
  let D:=2*Real.exp 2+4*C*Real.exp 2+1
  have hK:0<K:=lt_of_lt_of_le hC (le_max_left _ _)
  have hB':1 ≤ B':=by dsimp[B'];have :=le_max_right B 1;linarith
  have hD:0<D:=by dsimp[D];nlinarith[Real.exp_pos 2]
  refine ⟨K,B',D,M₀,hK,hB',hD,hM₀,?_⟩
  intro M hM g p j s L hj hs hstable hr1 hr Y hY hsmall EC EG hEC hEG hcusp hgenus a ha
  let r:=2*j+s
  let S:=scalarOrderWeight (M:ℝ) L p
  let h:ℝ:=complexity g p
  have hp:1 ≤ p:=by omega
  have hL:1 ≤ L:=by omega
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hM1:(1:ℝ) ≤ M:=by linarith
  have hS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,scalarOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) p]
  have hS0:0 ≤ S:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hh:0<h:=by
    have hn:0<complexity g p:=by unfold complexity Stable at *;omega
    dsimp[h]
    exact_mod_cast hn
  have hweight(p':ℕ)(hp':p' ≤ p+r)(i:ℕ)(hi:i+r ≤ L):
      scalarOrderWeight (M:ℝ) i p' ≤ S:=
    scalar_order_weight_shift (M:ℝ) hM1 i L p p' r hp' hi
  have hknown(p':ℕ)(hp':1 ≤ p')(hpr:p' ≤ p+r)(i:ℕ)(hi:i+r ≤ L):
      |PowerSeries.coeff i (formalCusp P Y p')|+|PowerSeries.coeff i (formalGenus P Y p')| ≤
        C*B^i*S^(2*i):=by
    have hwM:scalarOrderWeight (M₀:ℝ) i p' ≤ scalarOrderWeight (M:ℝ) i p':=by
      have hm:(M₀:ℝ) ≤ M:=by exact_mod_cast hM
      have ht:=mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg i : (0:ℝ) ≤ i)
      unfold scalarOrderWeight
      linarith
    have hw:=hwM.trans (hweight p' hpr i hi)
    have hb:=(hscalar i p' hp' Y hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) hw (2*i)) (by positivity))
    simpa only[formalCusp,formalGenus,PowerSeries.coeff_mk] using hb
  by_cases har:a<r
  · have harRaw:a<2*j+s:=har
    have hp':1 ≤ p-s+a:=by omega
    have hs':Stable (g-j) (p-s+a):=by unfold Stable at *;omega
    have hcomplex:(complexity (g-j) (p-s+a):ℝ)=h-((r-a:ℕ):ℝ):=by
      have hn:complexity (g-j) (p-s+a)+(r-a)=complexity g p:=by
        dsimp[r] at *
        unfold Stable complexity at *
        omega
      have hR:(complexity (g-j) (p-s+a):ℝ)+((r-a:ℕ):ℝ)=h:=by dsimp[h];exact_mod_cast hn
      linarith
    have hc:|((r-a:ℕ):ℝ)| ≤ L:=by
      rw[abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (show r-a ≤ L by dsimp[r] at *;omega)
    have hcast:((2*j+s:ℕ):ℝ)-(a:ℝ)=((r-a:ℕ):ℝ):=by dsimp[r];rw[Nat.cast_sub (by omega)]
    constructor
    · intro i hi
      have hraw:∀k ≤ i,|PowerSeries.coeff k (formalCusp P Y (p-s+a))| ≤ C*B^k*S^(2*k):=by
        intro k hk
        have hb:=hknown (p-s+a) hp' (by dsimp[r] at *;omega) k (by dsimp[r] at *;omega)
        linarith[abs_nonneg (PowerSeries.coeff k (formalGenus P Y (p-s+a)))]
      have hb:=shifted_scalar_inverse_linear_coeff_exponential (formalCusp P Y (p-s+a)) C B hC.le hB.le
        i L (by dsimp[r] at *;omega) ((r-a:ℕ):ℝ) S hc (by linarith) hraw
      simp only[formalLargeRatioFactor,ite_eq_left harRaw,formalHierarchyJet]
      rw[hcast]
      apply hb.trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity:B'^i≥0)) (pow_nonneg hS0 _)
    · intro m hm hmq
      have hraw:∀k < m,|PowerSeries.coeff k (formalCusp P Y (p-s+a))| ≤ C*B^k*S^(2*k):=by
        intro k hk
        have hb:=hknown (p-s+a) hp' (by dsimp[r] at *;omega) k (by dsimp[r] at *;omega)
        linarith[abs_nonneg (PowerSeries.coeff k (formalGenus P Y (p-s+a)))]
      have he:|cuspCorrection P (g-j) (p-s+a) Y-
          truncationValue (formalCusp P Y (p-s+a)) m (1/(h-((r-a:ℕ):ℝ)))| ≤
          EC m*S^(2*m)/(h-((r-a:ℕ):ℝ))^m:=by
        rw[←hcomplex]
        apply (hcusp (g-j) (p-s+a) m hp' hs' hm (by dsimp[r] at *;omega)).trans
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity)
            (hweight (p-s+a) (by dsimp[r] at *;omega) m (by dsimp[r] at *;omega)) _) (hEC m))
          (by positivity)
      have hb:=shifted_scalar_inverse_linear_remainder_exponential (cuspCorrection P (g-j) (p-s+a) Y)
        (EC m) (formalCusp P Y (p-s+a)) C B hC.le hB.le m L (by omega) (by dsimp[r] at *;omega)
        ((r-a:ℕ):ℝ) S h 1 hc hS hh hsmall (by norm_num) (hEC m) hraw he
      simp only[actualLargeRatioFactor,formalLargeRatioFactor,ite_eq_left harRaw,formalHierarchyJet]
      rw[hcast]
      apply hb.trans
      have ht:2*Real.exp 2*EC m+(4*C*Real.exp 2)*B'^m ≤ D*(EC m+EG m+B'^m):=by
        have h1:2*Real.exp 2 ≤ D:=by dsimp[D];nlinarith[Real.exp_pos 2]
        have h2:4*C*Real.exp 2 ≤ D:=by dsimp[D];nlinarith[Real.exp_pos 2]
        calc
          _ ≤ D*EC m+D*B'^m:=add_le_add
            (mul_le_mul_of_nonneg_right h1 (hEC m)) (mul_le_mul_of_nonneg_right h2 (by positivity))
          _ ≤ D*(EC m+EG m+B'^m):=by nlinarith[hEG m]
      have hf:=mul_le_mul_of_nonneg_left ht (by positivity:0 ≤ S^(2*m)/h^m)
      convert hf using 1 <;>dsimp[S,h,B']<;>ring
  · have harRaw:¬a<2*j+s:=har
    let b:=a-r
    have hb:b<j:=by dsimp[b,r] at *;omega
    have hp':1 ≤ p+2*b:=by omega
    have hs':Stable (g-b) (p+2*b):=by unfold Stable at *;omega
    have hcomplex:complexity (g-b) (p+2*b)=complexity g p:=by unfold complexity;omega
    constructor
    · intro i hi
      have hh':=hknown (p+2*b) hp' (by dsimp[r];omega) i (by dsimp[r] at *;omega)
      have hraw:|PowerSeries.coeff i (formalGenus P Y (p+2*b))| ≤ C*B^i*S^(2*i):=by
        linarith[abs_nonneg (PowerSeries.coeff i (formalCusp P Y (p+2*b)))]
      simp only[formalLargeRatioFactor,ite_eq_right harRaw,formalHierarchyJet]
      apply hraw.trans
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hS0 (2*i))
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hB.le (by dsimp[B'];have :=le_max_left B 1;linarith) i)
        (pow_nonneg hB.le i) hK.le
    · intro m hm hmq
      have he:=hgenus (g-b) (p+2*b) m hp' hs' hm (by dsimp[r] at *;omega)
      rw[hcomplex] at he
      have hw:=hweight (p+2*b) (by dsimp[r];omega) m (by dsimp[r] at *;omega)
      have ht:EG m ≤ D*(EC m+EG m+B'^m):=by
        have hD1:1 ≤ D:=by dsimp[D];nlinarith[Real.exp_pos 2]
        have hEGm:=hEG m
        have hECm:=hEC m
        have hBp:0 ≤ B'^m:=by positivity
        nlinarith
      simp only[actualLargeRatioFactor,formalLargeRatioFactor,ite_eq_right harRaw,formalHierarchyJet]
      apply he.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hECm:=hEC m
      have hEGm:=hEG m
      exact mul_le_mul ht (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) hw (2*m))
        (pow_nonneg (by unfold scalarOrderWeight;positivity) (2*m)) (mul_nonneg hD.le (by positivity))

end WP.HigherOrder
