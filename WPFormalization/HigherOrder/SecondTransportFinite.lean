import Mathlib.Tactic.ComputeDegree
import WPFormalization.HigherOrder.SecondHeadPolynomial
import WPFormalization.HigherOrder.BMoments
import WPFormalization.HigherOrder.SecondDilatonMoment

/-! Exact finite identification of the actual second dilaton moment and the original transport coefficient, Appendix C.10-C.11. -/
noncomputable section
namespace WP.HigherOrder

def cubicPrimitive (p : ℕ) (Y x : ℝ) : ℝ :=
  (cubicIncrement p Y).coeff 3/4*x^2*(x-1)^2+
  (cubicIncrement p Y).coeff 2/6*x*(x-1)*(2*x-1)+
  (cubicIncrement p Y).coeff 1/2*x*(x-1)+(cubicIncrement p Y).coeff 0*x

set_option maxHeartbeats 1800000 in
lemma cubicIncrement_eval_coeff (p : ℕ) (Y x : ℝ) :
    (cubicIncrement p Y).eval x=(cubicIncrement p Y).coeff 3*x^3+
      (cubicIncrement p Y).coeff 2*x^2+(cubicIncrement p Y).coeff 1*x+
      (cubicIncrement p Y).coeff 0 := by
  have hd : (cubicIncrement p Y).natDegree<4 := by
    unfold cubicIncrement
    dsimp only
    compute_degree <;> norm_num
  rw [Polynomial.eval_eq_sum_range' hd x]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one]
  ring

lemma cubicPrimitive_succ (p : ℕ) (Y x : ℝ) :
    cubicPrimitive p Y (x+1)-cubicPrimitive p Y x=(cubicIncrement p Y).eval x := by
  rw [cubicIncrement_eval_coeff]
  unfold cubicPrimitive
  ring

lemma sum_cubicIncrement (p : ℕ) (Y : ℝ) (d : ℕ) :
    (∑ t∈Finset.range d,(cubicIncrement p Y).eval (t:ℝ))=cubicPrimitive p Y d := by
  induction d with
  | zero => simp [cubicPrimitive]
  | succ d ih =>
    rw [Finset.sum_range_succ,ih]
    have h:=cubicPrimitive_succ p Y (d:ℝ)
    push_cast
    linarith

lemma beforeCoordinate_head_zero_tail (d p t : ℕ) :
    beforeCoordinate (d::List.replicate p 0) 0 t=t::List.replicate p 0 := by
  apply List.ext_getElem (by simp [beforeCoordinate])
  intro j hj hj'
  cases j with
  | zero => simp [beforeCoordinate]
  | succ j => simp [beforeCoordinate]

lemma secondProfile_head_zero_tail (Y : ℝ) (d p : ℕ) :
    secondProfile Y (d::List.replicate p 0)=
      -(∑ t∈Finset.range d,secondIncrement Y 0 (t::List.replicate p 0)) := by
  unfold secondProfile
  rw [show (d::List.replicate p 0).length=p+1 by simp,Finset.sum_range_succ']
  have hzero : (∑ i∈Finset.range p,∑ t∈Finset.range ((d::List.replicate p 0)[i+1]!),
      secondIncrement Y (i+1) (beforeCoordinate (d::List.replicate p 0) (i+1) t))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [List.getElem!_cons_succ]
  rw [hzero]
  simp only [List.getElem!_cons_zero,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [beforeCoordinate_head_zero_tail]
lemma cubicPrimitive_b_hasSum (p : ℕ) (Y : ℝ) :
    HasSum (fun d : ℕ => canonicalDilatonCoefficient Y d*cubicPrimitive p Y (d:ℝ)) (sigmaB p Y) := by
  let a := fun j=>(cubicIncrement p Y).coeff j
  have h₁ := bMoment_hasSum 1 Y
  have h₂ := bMoment_hasSum 2 Y
  have h₃ := bMoment_hasSum 3 Y
  have h₄ := bMoment_hasSum 4 Y
  have hs := ((((h₄.sub (h₃.mul_left 2)).add h₂).mul_left (a 3/4)).add
    ((((h₃.mul_left 2).sub (h₂.mul_left 3)).add h₁).mul_left (a 2/6))).add
    ((h₂.sub h₁).mul_left (a 1/2))
  have ht := hs.add (h₁.mul_left (a 0))
  convert! ht using 1
  ext d
  dsimp [cubicPrimitive,a]
  ring
lemma canonicalDilatonCoefficient_one (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    canonicalDilatonCoefficient Y 1=(1:ℝ)/3 := by
  simp [canonicalDilatonCoefficient,realCoeff,coeff,barH_zero Y hY]

lemma canonicalDilatonCoefficient_two (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    canonicalDilatonCoefficient Y 2= -theta Y 1/5 := by
  have h0:=Analysis.barK_zero_closed Y hY
  have hD := ((barH_differentiable Y 0).hasDerivAt).add
    ((((hasDerivAt_id (0:ℂ)).const_mul (2/3:ℂ)).mul
      (((barH_differentiable Y).deriv 0).hasDerivAt)))
  have he : (fun z : ℂ=>barH Y z+(2/3:ℂ)*z*deriv (barH Y) z)=barK Y :=
    funext (fun z=>(normalized_kernel_identity Y hY z).symm)
  change HasDerivAt (fun z : ℂ=>barH Y z+(2/3:ℂ)*z*deriv (barH Y) z) _ 0 at hD
  rw [he] at hD
  have hK:=hD.deriv
  simp only [id_eq,mul_zero,zero_mul,add_zero] at hK
  have hi:=((barK_differentiable Y 0).hasDerivAt.inv (by rw [h0];exact one_ne_zero)).deriv
  change deriv (fun w:ℂ=>(barK Y w)⁻¹) 0= -deriv (barK Y) 0/(barK Y 0)^2 at hi
  rw [h0] at hi
  simp only [one_pow,div_one] at hi
  have hr:=congrArg Complex.re hK
  norm_num [Complex.add_re,Complex.mul_re] at hr
  simp only [canonicalDilatonCoefficient,show 1≤2 by omega,ite_true,show 2-1=1 by omega,
    realCoeff,coeff,iteratedDeriv_succ,iteratedDeriv_zero,Nat.factorial_one,Nat.cast_one,div_one]
  change (deriv (barH Y) 0).re/3= -theta Y 1/5
  simp only [theta,realCoeff,coeff,iteratedDeriv_succ,iteratedDeriv_zero,
    Nat.factorial_one,Nat.cast_one,div_one,hi,Complex.neg_re]
  linarith

lemma canonicalDilatonCoefficient_tail_hasSum (N : ℕ) (Y : ℝ) :
    HasSum (fun d : ℕ=>if N≤d then canonicalDilatonCoefficient Y d else 0)
      (A Y-∑ d∈Finset.range N,canonicalDilatonCoefficient Y d) := by
  let f : ℕ→ℝ:=fun d=>if N≤d then canonicalDilatonCoefficient Y d else 0
  have hshift : HasSum (fun d=>canonicalDilatonCoefficient Y (d+N))
      (A Y-∑ d∈Finset.range N,canonicalDilatonCoefficient Y d) := by
    apply (hasSum_nat_add_iff N).mpr
    convert! canonicalDilatonCoefficient_hasSum Y using 1
    ring
  have he : HasSum (fun d=>f (d+N)) (A Y-∑ d∈Finset.range N,canonicalDilatonCoefficient Y d) := by
    simpa only [f,show ∀d:ℕ,N≤d+N by omega,ite_true] using hshift
  have hprefix : (∑d∈Finset.range N,f d)=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    dsimp [f]
    rw [if_neg (by have hi:=Finset.mem_range.mp hd;omega)]
  have hh:=he.sum_range_add
  simpa only [hprefix,zero_add] using hh
lemma sum_exceptionalIncrement (p d : ℕ) (Y : ℝ) :
    (∑t∈Finset.range d,exceptionalIncrement p t Y)=
      (if 1≤d then exceptionalIncrement p 0 Y else 0)+
      (if 2≤d then exceptionalIncrement p 1 Y else 0)+
      (if 3≤d then exceptionalIncrement p 2 Y else 0) := by
  by_cases hd : d<3
  · interval_cases d <;> norm_num [Finset.sum_range_succ]
  · have hd3 : 3≤d := by omega
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hd3
    rw [Finset.sum_range_add]
    have hz : (∑t∈Finset.range n,exceptionalIncrement p (3+t) Y)=0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact exceptionalIncrement_eq_zero p (3+t) Y (by omega)
    rw [hz]
    norm_num [Finset.sum_range_succ,show 1≤3+n by omega,show 2≤3+n by omega,show 3≤3+n by omega]

lemma secondProfile_head_formula_of_increment (p : ℕ) (Y : ℝ)
    (hB : ∀t:ℕ,secondIncrement Y 0 (t::List.replicate p 0)=
      (cubicIncrement (p+1) Y).eval (t:ℝ)+exceptionalIncrement (p+1) t Y) (d : ℕ) :
    secondProfile Y (d::List.replicate p 0)= -cubicPrimitive (p+1) Y (d:ℝ)-
      (if 1≤d then exceptionalIncrement (p+1) 0 Y else 0)-
      (if 2≤d then exceptionalIncrement (p+1) 1 Y else 0)-
      (if 3≤d then exceptionalIncrement (p+1) 2 Y else 0) := by
  rw [secondProfile_head_zero_tail]
  simp_rw [hB]
  rw [Finset.sum_add_distrib,sum_cubicIncrement,sum_exceptionalIncrement]
  ring

lemma secondProfile_b_hasSum_of_increment (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (hB : ∀t:ℕ,secondIncrement Y 0 (t::List.replicate p 0)=
      (cubicIncrement (p+1) Y).eval (t:ℝ)+exceptionalIncrement (p+1) t Y) :
    HasSum (fun d : ℕ=>canonicalDilatonCoefficient Y d*secondProfile Y (d::List.replicate p 0))
      (-sigmaB (p+1) Y-exceptionalIncrement (p+1) 0 Y*A Y-
        exceptionalIncrement (p+1) 1 Y*(A Y-1/3)-
        exceptionalIncrement (p+1) 2 Y*(A Y-1/3+theta Y 1/5)) := by
  have h₀ := (canonicalDilatonCoefficient_tail_hasSum 1 Y).mul_left (exceptionalIncrement (p+1) 0 Y)
  have h₁ := (canonicalDilatonCoefficient_tail_hasSum 2 Y).mul_left (exceptionalIncrement (p+1) 1 Y)
  have h₂ := (canonicalDilatonCoefficient_tail_hasSum 3 Y).mul_left (exceptionalIncrement (p+1) 2 Y)
  have hs := ((((cubicPrimitive_b_hasSum (p+1) Y).neg).sub h₀).sub h₁).sub h₂
  convert! hs using 1
  · funext d
    rw [secondProfile_head_formula_of_increment p Y hB d]
    by_cases h1 : 1≤d <;> by_cases h2 : 2≤d <;> by_cases h3 : 3≤d <;>
      simp only [h1,h2,h3,ite_true,ite_false,mul_zero] <;>ring
  · have hz : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,canonicalDilatonCoefficient_one Y hY,
      canonicalDilatonCoefficient_two Y hY,hz,zero_add]
    ring

lemma secondDilatonMoment_eq_finite (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    secondDilatonMoment p Y= -sigmaB (p+1) Y-exceptionalIncrement (p+1) 0 Y*A Y-
      exceptionalIncrement (p+1) 1 Y*(A Y-1/3)-
      exceptionalIncrement (p+1) 2 Y*(A Y-1/3+theta Y 1/5) := by
  exact (secondDilatonMoment_hasSum p Y hY).unique
    (secondProfile_b_hasSum_of_increment p Y hY (fun t=>secondIncrement_head_eq_cubic p t Y hY))

lemma secondProfile_head_finite (p d : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    secondProfile Y (d::List.replicate p 0)= -cubicPrimitive (p+1) Y (d:ℝ)-
      (if 1≤d then exceptionalIncrement (p+1) 0 Y else 0)-
      (if 2≤d then exceptionalIncrement (p+1) 1 Y else 0)-
      (if 3≤d then exceptionalIncrement (p+1) 2 Y else 0) :=
  secondProfile_head_formula_of_increment p Y (fun t=>secondIncrement_head_eq_cubic p t Y hY) d

lemma transportGamma_eq_secondDilatonMoment (p : ℕ) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    transportGamma p Y=transportBeta p Y^2-transportBeta p Y-secondDilatonMoment p Y/A Y := by
  rw [secondDilatonMoment_eq_finite p Y hY,transportGamma]
  ring

end WP.HigherOrder
