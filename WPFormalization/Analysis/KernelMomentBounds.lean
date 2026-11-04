import WPFormalization.Analysis.WeightCoefficients
import WPFormalization.Analysis.QuadraticRemainder

/-! Uniform absolute moments of the actual canonical kernel weights.
The joint nonvanishing disk gives a common Cauchy bound. The exact weight
germ turns it into geometric coefficient decay, all polynomial absolute
moments, and a uniform theta bound by finite telescoping. Positivity of
individual increments remains a separate actual-product obligation. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma weightGenerating_uniform_analytic : ∃ R M:ℝ,1<R ∧ 0<M ∧ ∀Y∈Icc (0:ℝ) y₀,
    DifferentiableOn ℂ (weightGenerating Y) (Metric.closedBall 0 R) ∧
    ∀z:ℂ,‖z‖≤R → ‖weightGenerating Y z‖≤M := by
  obtain ⟨η,hη,hzero⟩:=deflatedBarK_uniform_zero_free
  let R:ℝ:=1+η/2
  have hR:1<R:=by dsimp [R];linarith
  have hρ:R≤1+η:=by dsimp [R];linarith
  have hc:Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) R=>
      weightGenerating (p.1:ℝ) p.2) := by
    have hmap:Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) R=>
      (p.1,(p.2:ℂ))) := by fun_prop
    have hbase:=deflatedBarK_joint_continuous.comp hmap
    exact hbase.inv₀ (fun p=>hzero p.1 p.1.property p.2
      ((show ‖(p.2:ℂ)‖≤R by simpa only [Metric.mem_closedBall,dist_zero_right] using p.2.property).trans hρ))
  obtain ⟨B,hB⟩:=isCompact_univ.bddAbove_image hc.norm.continuousOn
  refine ⟨R,max B 1,hR,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro Y hY
  constructor
  · intro z hz
    have hzR:‖z‖≤R:=by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact ((deflatedBarK_differentiable Y z).inv (hzero Y hY z (hzR.trans hρ))).differentiableWithinAt
  · intro z hz
    exact (hB (mem_image_of_mem _ (show (⟨Y,hY⟩,⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz⟩)∈(univ:Set (Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) R)) from mem_univ _))).trans (le_max_left _ _)
lemma weight_norm_geometric_bound : ∃R M:ℝ,1<R ∧ 0<M ∧ ∀Y∈Icc (0:ℝ) y₀,∀n:ℕ,
    |weight Y n|≤M/R^n := by
  obtain ⟨R,M,hR,hM,hdata⟩:=weightGenerating_uniform_analytic
  refine ⟨R,M,hR,hM,?_⟩
  intro Y hY n
  rw [←weightGenerating_coeff Y hY]
  exact (Complex.abs_re_le_norm _).trans
    (coeff_norm_le_circle_bound (weightGenerating Y) R M (lt_trans zero_lt_one hR)
      (hdata Y hY).1 (fun z hz=>(hdata Y hY).2 z (le_of_eq (by simpa only [Metric.mem_sphere,dist_zero_right] using hz))) n)
lemma summable_shifted_pow_div_geometric (q:ℕ) (R:ℝ) (hR:1<R) :
    Summable (fun n:ℕ=>(1+(n:ℝ))^q/R^n) := by
  have hRpos:0<R:=lt_trans zero_lt_one hR
  have hr:‖(R⁻¹:ℝ)‖<1:=by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_lt_one₀ hRpos).2 hR
  have hs:=summable_pow_mul_geometric_of_norm_lt_one q hr
  have hs':Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^q*(R⁻¹)^(n+1)):=
    (summable_nat_add_iff 1).mpr hs
  convert hs'.mul_left R using 1
  ext n
  simp only [Nat.cast_add,Nat.cast_one,pow_succ,inv_pow,div_eq_mul_inv]
  have hRn:(R:ℝ)≠0:=hRpos.ne'
  field_simp
  <;> ring
lemma weight_absolute_moments_uniform (q:ℕ) : ∃C:ℝ,∀Y∈Icc (0:ℝ) y₀,
    Summable (fun n:ℕ=>(1+(n:ℝ))^q*|weight Y n|) ∧
    ∑'n:ℕ,(1+(n:ℝ))^q*|weight Y n|≤C := by
  obtain ⟨R,M,hR,hM,hbound⟩:=weight_norm_geometric_bound
  have hs:=summable_shifted_pow_div_geometric q R hR
  refine ⟨M*∑'n:ℕ,(1+(n:ℝ))^q/R^n,?_⟩
  intro Y hY
  have hmajor:Summable (fun n:ℕ=>M*((1+(n:ℝ))^q/R^n)):=hs.mul_left M
  have hpoint (n:ℕ):(1+(n:ℝ))^q*|weight Y n|≤M*((1+(n:ℝ))^q/R^n) := by
    have hh:=mul_le_mul_of_nonneg_left (hbound Y hY n)
      (show 0≤(1+(n:ℝ))^q by positivity)
    convert hh using 1 <;> ring
  have hsmall:Summable (fun n:ℕ=>(1+(n:ℝ))^q*|weight Y n|):=
    Summable.of_nonneg_of_le (fun n=>by positivity) hpoint hmajor
  refine ⟨hsmall,?_⟩
  calc
    _ ≤ ∑'n:ℕ,M*((1+(n:ℝ))^q/R^n):=hsmall.tsum_le_tsum hpoint hmajor
    _ = _ := tsum_mul_left
lemma weight_sum_range (Y:ℝ) (n:ℕ):
    (∑i∈Finset.range (n+1),weight Y i)=theta Y n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [weight,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]
    ring
lemma theta_uniform_bound : ∃C:ℝ,∀Y∈Icc (0:ℝ) y₀,∀n:ℕ,theta Y n≤C := by
  obtain ⟨C,hC⟩:=weight_absolute_moments_uniform 0
  simp only [pow_zero,one_mul] at hC
  refine ⟨C,?_⟩
  intro Y hY n
  rw [←weight_sum_range Y n]
  calc
    _ ≤ ∑i∈Finset.range (n+1),|weight Y i|:=Finset.sum_le_sum (fun i _=>le_abs_self _)
    _ ≤ ∑'i:ℕ,|weight Y i|:=(hC Y hY).1.sum_le_tsum _ (fun i _=>abs_nonneg _)
    _ ≤ C:=(hC Y hY).2
lemma theta_zero_closed (Y:ℝ) (hY:Y∈Icc 0 y₀):theta Y 0=1 := by
  simp only [theta,realCoeff,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,
    div_one,barK_zero_closed Y hY,inv_one,Complex.one_re]
lemma theta_monotone_of_weight_nonneg (Y:ℝ) (hp:∀n:ℕ,0≤weight Y n):Monotone (theta Y) := by
  apply monotone_nat_of_le_succ
  intro n
  have hh:0≤theta Y (n+1)-theta Y n:=by simpa [weight] using hp (n+1)
  linarith
lemma weight_moments_uniform (q:ℕ) : ∃C:ℝ,∀Y∈Icc (0:ℝ) y₀,
    Summable (fun n:ℕ=>(1+(n:ℝ))^q*weight Y n) ∧
    ∑'n:ℕ,(1+(n:ℝ))^q*weight Y n≤C := by
  obtain ⟨C,hC⟩:=weight_absolute_moments_uniform q
  refine ⟨C,?_⟩
  intro Y hY
  have hn (n:ℕ):‖(1+(n:ℝ))^q*weight Y n‖=(1+(n:ℝ))^q*|weight Y n|:=by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤(1+(n:ℝ))^q by positivity)]
  have hs:Summable (fun n:ℕ=>(1+(n:ℝ))^q*weight Y n):=
    ((hC Y hY).1.congr (fun n=>(hn n).symm)).of_norm
  refine ⟨hs,?_⟩
  exact (hs.tsum_le_tsum (fun n=>mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
    (hC Y hY).1).trans (hC Y hY).2
end WP.Analysis
