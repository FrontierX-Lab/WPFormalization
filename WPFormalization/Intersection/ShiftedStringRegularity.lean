import WPFormalization.Intersection.BackgroundString
import WPFormalization.Intersection.BackgroundStringCalculus
/-! Real analytic regularity and the direct finite parameter derivative of the
original degree-zero shifted amplitude, on the open set where a is nonzero. -/
noncomputable section
namespace WP
lemma hasDerivAt_real_X_jet (k : ℕ) (Y : ℝ) :
    HasDerivAt (fun t : ℝ => (iteratedDeriv k X t).re)
      (iteratedDeriv (k+1) X Y).re Y := by
  have hr := ((iteratedDeriv_X_differentiable k) (Y:ℂ)).hasDerivAt.real_of_complex
  simpa only [iteratedDeriv_succ] using hr
lemma hasDerivAt_a_from_X_jet (Y : ℝ) :
    HasDerivAt a (iteratedDeriv 2 X Y).re Y := by
  exact a_hasDerivAt Y
lemma hasDerivAt_background_time (i : ℕ) (Y : ℝ) :
    HasDerivAt (fun t : ℝ => -(iteratedDeriv (i+2) X t).re)
      (-(iteratedDeriv (i+3) X Y).re) Y := by
  convert! (hasDerivAt_real_X_jet (i+2) Y).neg using 1
set_option backward.isDefEq.respectTransparency false in
lemma shifted_zero_fixed_background (P : PsiTheory) (g p : ℕ) (hs : Stable g p) (Y : ℝ) :
    shifted P g (List.replicate p 0) Y =
      ∑ l ∈ backgroundVectors (dimension g p+1) (dimension g p+1) (dimension g p),
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          (∏ i : Fin (dimension g p+1), (-(iteratedDeriv (i.val+2) X Y).re)^(l i)/(l i).factorial)/
            a Y^(complexity g p+∑ i,l i) := by
  have hdef : deficit g (List.replicate p 0)=dimension g p := by simp [deficit]
  have hvalid : Stable g (List.replicate p 0).length ∧
      (List.replicate p 0).sum ≤ dimension g (List.replicate p 0).length := by simpa using hs
  rw [←hdef]
  unfold shifted
  rw [if_pos hvalid]
  simp only [List.length_replicate,List.map_replicate,List.prod_replicate]
  have ho : oddFactorial 0=1 := by simp [oddFactorial]
  rw [ho]
  simp only [Nat.cast_one,one_pow,one_mul]
  rw [sum_backgroundVectors_zeroExtend (deficit g (List.replicate p 0)) 1
    (deficit g (List.replicate p 0)+1) (by omega)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [backgroundDegrees_zeroExtend,background_weight_zeroExtend]
  have hsize : (∑ i : Fin (deficit g (List.replicate p 0)+1),zeroExtendBackground 1 l i)=
      ∑ i : Fin (deficit g (List.replicate p 0)),l i := by
    rw [←backgroundDegrees_length,backgroundDegrees_zeroExtend,backgroundDegrees_length]
  rw [hsize]
  simp only [pure,List.map_append,List.map_replicate,Int.ofNat_eq_natCast,Nat.cast_zero,Fin.val_castAdd]

lemma shifted_zero_analyticAt (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (ha : a Y≠0) : AnalyticAt ℝ (fun t : ℝ => shifted P g (List.replicate p 0) t) Y := by
  have hfun : (fun t : ℝ => shifted P g (List.replicate p 0) t)=fun t : ℝ =>
      ∑ l ∈ backgroundVectors (dimension g p+1) (dimension g p+1) (dimension g p),
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          (∏ i : Fin (dimension g p+1), (-(iteratedDeriv (i.val+2) X t).re)^(l i)/(l i).factorial)/
            a t^(complexity g p+∑ i,l i) := funext (shifted_zero_fixed_background P g p hs)
  rw [hfun]
  have hjet (k : ℕ) : AnalyticAt ℝ (fun t : ℝ => (iteratedDeriv k X t).re) Y :=
    ((iteratedDeriv_X_differentiable k).analyticAt (Y:ℂ)).re_ofReal
  have haa : AnalyticAt ℝ a Y := by
    change AnalyticAt ℝ (fun t : ℝ => (deriv X t).re) Y
    simpa only [iteratedDeriv_one] using hjet 1
  apply Finset.analyticAt_fun_sum
  intro l hl
  apply AnalyticAt.div
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_prod
    intro i hi
    convert! ((hjet (i.val+2)).neg.pow (l i)).div_const (c:=((l i).factorial:ℝ)) using 1
  · exact haa.pow _
  · exact pow_ne_zero _ ha

def backgroundRationalDerivative {N : ℕ} (t v : Fin N→ℝ) (l : Fin N→ℕ)
    (a w : ℝ) (n : ℕ) : ℝ :=
  (∑ i : Fin N, if 0<l i then v i*(∏ j : Fin N,
    t j^(Function.update l i (l i-1) j)/(Function.update l i (l i-1) j).factorial) else 0)/a^n+
      (∏ i : Fin N,t i^(l i)/(l i).factorial)*((n:ℝ)*w/a^(n+1))
lemma shifted_zero_hasDerivAt_finite (P : PsiTheory) (g p : ℕ) (hs : Stable g p)
    (Y : ℝ) (ha : a Y≠0) :
    HasDerivAt (fun t : ℝ => shifted P g (List.replicate p 0) t)
      (∑ l ∈ backgroundVectors (dimension g p+1) (dimension g p+1) (dimension g p),
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          backgroundRationalDerivative
            (fun i : Fin (dimension g p+1) => -(iteratedDeriv (i.val+2) X Y).re)
            (fun i : Fin (dimension g p+1) => -(iteratedDeriv (i.val+3) X Y).re)
            l (a Y) (-(iteratedDeriv 2 X Y).re) (complexity g p+∑i,l i)) Y := by
  have hfun : (fun t : ℝ => shifted P g (List.replicate p 0) t)=fun t : ℝ =>
      ∑ l ∈ backgroundVectors (dimension g p+1) (dimension g p+1) (dimension g p),
        P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat)*
          (∏ i : Fin (dimension g p+1), (-(iteratedDeriv (i.val+2) X t).re)^(l i)/(l i).factorial)/
            a t^(complexity g p+∑ i,l i) := funext (shifted_zero_fixed_background P g p hs)
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro l hl
  have ht := (hasDerivAt_weighted_background_term
    (fun i : Fin (dimension g p+1) => fun t : ℝ => -(iteratedDeriv (i.val+2) X t).re)
    (fun i : Fin (dimension g p+1) => -(iteratedDeriv (i.val+3) X Y).re)
    l a Y (-(iteratedDeriv 2 X Y).re) (complexity g p+∑i,l i)
    (fun i=>hasDerivAt_background_time i.val Y)
    (by simpa only [neg_neg] using a_hasDerivAt Y) ha).const_mul
      (P.psi g (List.replicate p 0 ++ (backgroundDegrees l).map Int.ofNat))
  convert! ht using 1
  · ext t
    ring
end WP
