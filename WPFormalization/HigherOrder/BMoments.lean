import Mathlib.Combinatorics.Enumerative.Stirling
import WPFormalization.HigherOrder.SecondProfile
import WPFormalization.Marked.SignedDilatonMoments

/-! Every signed dilaton moment is an actual absolutely convergent sum.
A Stirling expansion identifies the Euler-plus-one definition with finitely
many ordinary derivatives of the entire normalized H kernel at one. -/
noncomputable section
namespace WP.HigherOrder
lemma eulerPlusOne_entire (f : ℂ→ℂ) (hf : Differentiable ℂ f) : Differentiable ℂ (eulerPlusOne f) := by
  intro z
  exact ((differentiableAt_id.mul ((hf.analyticAt z).deriv.differentiableAt)).add (hf z))
lemma eulerPlusOne_coeff (f : ℂ→ℂ) (hf : Differentiable ℂ f) (n : ℕ) :
    coeff (eulerPlusOne f) n=((n:ℂ)+1)*coeff f n := by
  have hd : Differentiable ℂ (fun z:ℂ=>z*deriv f z) := by
    intro z
    exact differentiableAt_id.mul ((hf.analyticAt z).deriv.differentiableAt)
  have he := congrArg (fun p:PowerSeries ℂ=>PowerSeries.coeff n p)
    (Analysis.taylor_add (hd.analyticAt 0) (hf.analyticAt 0))
  simp only [Analysis.taylor_coeff,map_add] at he
  rw [Analysis.harmonic_coeff_euler f (hf.analyticAt 0) n] at he
  change coeff (eulerPlusOne f) n=_ at he
  rw [he]
  ring
lemma eulerPlusOne_iterate_entire (f : ℂ→ℂ) (hf : Differentiable ℂ f) (j : ℕ) :
    Differentiable ℂ ((eulerPlusOne^[j]) f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact eulerPlusOne_entire _ ih
lemma eulerPlusOne_iterate_coeff (f : ℂ→ℂ) (hf : Differentiable ℂ f) (j n : ℕ) :
    coeff ((eulerPlusOne^[j]) f) n=((n:ℂ)+1)^j*coeff f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',eulerPlusOne_coeff _ (eulerPlusOne_iterate_entire f hf j) n,ih,pow_succ]
    ring
lemma bMoment_hasSum_succ (j : ℕ) (Y : ℝ) :
    HasSum (fun n : ℕ => ((n:ℝ)+1)^j*canonicalDilatonCoefficient Y (n+1)) (bMoment j Y) := by
  have hs := (entire_realCoeff_hasSum ((eulerPlusOne^[j]) (barH Y))
    (eulerPlusOne_iterate_entire _ (barH_differentiable Y) j)).div_const 3
  convert! hs using 1
  ext n
  simp only [canonicalDilatonCoefficient,show 1≤n+1 by omega,ite_true,Nat.add_sub_cancel,realCoeff]
  rw [eulerPlusOne_iterate_coeff _ (barH_differentiable Y) j n]
  have hc : (((n:ℂ)+1)^j)=((((n:ℝ)+1)^j:ℝ):ℂ) := by push_cast;rfl
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
lemma bMoment_hasSum (j : ℕ) (Y : ℝ) :
    HasSum (fun d : ℕ => (d:ℝ)^j*canonicalDilatonCoefficient Y d) (bMoment j Y) := by
  have hs := (hasSum_nat_add_iff (f:=fun d : ℕ => (d:ℝ)^j*canonicalDilatonCoefficient Y d) 1).mp
    (by simpa only [Nat.cast_add,Nat.cast_one] using bMoment_hasSum_succ j Y)
  have hzero : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
  simpa only [Finset.sum_range_one,hzero,mul_zero,add_zero] using hs
lemma bMoment_abs_uniform (j : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Set.Icc (0:ℝ) y₀, |bMoment j Y|≤C := by
  obtain ⟨C,hC,hbound⟩ := canonicalDilatonCoefficient_moment_tsum_uniform j
  refine ⟨C,hC,?_⟩
  intro Y hY
  have hs := bMoment_hasSum j Y
  calc
    |bMoment j Y| = |∑' d : ℕ, (d:ℝ)^j*canonicalDilatonCoefficient Y d| := by rw [hs.tsum_eq]
    _ ≤ ∑' d : ℕ, |(d:ℝ)^j*canonicalDilatonCoefficient Y d| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' d : ℕ, ((d:ℝ)+1)^j*|canonicalDilatonCoefficient Y d| :=
      hs.summable.abs.tsum_le_tsum (by
        intro d
        rw [abs_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg d) j)]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) j) (abs_nonneg _))
        (canonicalDilatonCoefficient_moment_summable j Y hY)
    _ ≤ C := hbound Y hY

lemma entire_iteratedDeriv (f : ℂ→ℂ) (hf : Differentiable ℂ f) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact fun z => (ih.analyticAt z).deriv.differentiableAt

lemma taylor_iteratedDeriv (f : ℂ→ℂ) (k : ℕ) :
    Analysis.taylor (iteratedDeriv k f)=(PowerSeries.derivative^[k]) (Analysis.taylor f) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ,Analysis.taylor_deriv,ih,Function.iterate_succ_apply']

lemma monomial_iteratedDeriv_coeff (f : ℂ→ℂ) (hf : Differentiable ℂ f) (k n : ℕ) :
    coeff (fun z=>z^k*iteratedDeriv k f z) n=(n.descFactorial k:ℂ)*coeff f n := by
  have ht := congrArg (fun p:PowerSeries ℂ=>PowerSeries.coeff n p)
    (Analysis.taylor_mul (f:=fun z:ℂ=>z^k) (g:=iteratedDeriv k f)
      (analyticAt_id.pow k) ((entire_iteratedDeriv f hf k).analyticAt 0))
  rw [Analysis.taylor_pow (f:=fun z:ℂ=>z) analyticAt_id,Analysis.taylor_id,taylor_iteratedDeriv,PowerSeries.coeff_X_pow_mul'] at ht
  simp only [Analysis.taylor_coeff] at ht
  rw [ht]
  split_ifs with h
  · rw [PowerSeries.coeff_iterate_derivative,Analysis.taylor_coeff,Nat.sub_add_cancel h]
    rw [←Nat.add_descFactorial_eq_ascFactorial,Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega)]
    simp

lemma shifted_power_stirling (n j : ℕ) :
    (n+1)^j=∑ k∈Finset.range (j+1),Nat.stirlingSecond (j+1) (k+1)*n.descFactorial k := by
  have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (n+1) (j+1)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.stirlingSecond_succ_zero,zero_mul,add_zero,Nat.succ_descFactorial_succ] at h
  rw [pow_succ] at h
  have he : (n+1)*((n+1)^j)=(n+1)*(∑ k∈Finset.range (j+1),Nat.stirlingSecond (j+1) (k+1)*n.descFactorial k) := by
    rw [mul_comm (n+1),h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  exact Nat.mul_left_cancel (Nat.succ_pos n) he

lemma entire_coeff_hasSum (f : ℂ→ℂ) (hf : Differentiable ℂ f) :
    HasSum (coeff f) (f 1) := by
  convert! Complex.hasSum_taylorSeries_of_entire hf 0 1 using 1
  ext n
  simp only [coeff,sub_zero,one_pow,smul_eq_mul]
  ring
lemma monomial_iteratedDeriv_coeff_hasSum (f : ℂ→ℂ) (hf : Differentiable ℂ f) (k : ℕ) :
    HasSum (fun n : ℕ => (n.descFactorial k:ℂ)*coeff f n) (iteratedDeriv k f 1) := by
  have hg : Differentiable ℂ (fun z=>z^k*iteratedDeriv k f z) := by
    exact (differentiable_id.pow k).mul (entire_iteratedDeriv f hf k)
  have hs := entire_coeff_hasSum _ hg
  simp only [one_pow,one_mul] at hs
  convert! hs using 1
  ext n
  exact (monomial_iteratedDeriv_coeff f hf k n).symm

lemma eulerPlusOne_iterate_one_stirling (f : ℂ→ℂ) (hf : Differentiable ℂ f) (j : ℕ) :
    ((eulerPlusOne^[j]) f) 1=
      ∑ k∈Finset.range (j+1),(Nat.stirlingSecond (j+1) (k+1):ℂ)*iteratedDeriv k f 1 := by
  have hs : HasSum (fun n : ℕ => ∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond (j+1) (k+1):ℂ)*((n.descFactorial k:ℂ)*coeff f n))
      (∑ k∈Finset.range (j+1),(Nat.stirlingSecond (j+1) (k+1):ℂ)*iteratedDeriv k f 1) := by
    apply hasSum_sum
    intro k hk
    exact (monomial_iteratedDeriv_coeff_hasSum f hf k).mul_left _
  have he := entire_coeff_hasSum _ (eulerPlusOne_iterate_entire f hf j)
  apply he.unique
  convert! hs using 1
  ext n
  rw [eulerPlusOne_iterate_coeff f hf]
  simp_rw [←mul_assoc]
  rw [←Finset.sum_mul]
  have hp : ((n:ℂ)+1)^j=∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond (j+1) (k+1):ℂ)*(n.descFactorial k:ℂ) := by
    exact_mod_cast shifted_power_stirling n j
  rw [hp]

lemma bMoment_eq_stirling_jets (j : ℕ) (Y : ℝ) :
    bMoment j Y=(∑ k∈Finset.range (j+1),
      (Nat.stirlingSecond (j+1) (k+1):ℝ)*(iteratedDeriv k (barH Y) 1).re)/3 := by
  rw [bMoment,eulerPlusOne_iterate_one_stirling _ (barH_differentiable Y) j]
  change Complex.reCLM _/3=_
  rw [map_sum]
  simp only [Complex.reCLM_apply,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
end WP.HigherOrder
