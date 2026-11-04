import WPFormalization.HigherOrder.PoissonCentralExpansionProof
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poisson_central_expansion_uniform (R:ℝ) (hR:0<R):
  ∃ν₀ C:ℝ,0<ν₀∧ν₀<R∧0<C∧∀f:ℂ × ℂ → ℂ,
    AnalyticOnNhd ℂ f (Metric.ball 0 R)→
    (∀p∈Metric.ball (0:ℂ × ℂ) R,‖f p‖≤1)→
    (∀ (h : ℝ) (k K : ℕ), 0 < h → (k:ℝ)/h ≤ ν₀ → (K:ℝ) ≤ h/2 →
      ‖poissonCoefficientOperator h k (fun u=>f (u,((k:ℝ)/h:ℝ))) -
        ∑j∈Finset.range (K+1),poissonCentralAmplitude f j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j‖ ≤
          C^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) ∧
    (∀ j, AnalyticOnNhd ℂ (poissonCentralAmplitude f j) (Metric.ball 0 ν₀)) ∧
    (∀ j ν, ‖ν‖ < ν₀ → ‖poissonCentralAmplitude f j ν‖ ≤ C^(j+1)*(j.factorial:ℝ)) ∧
    (∀ j, 1 ≤ j → poissonCentralAmplitude f j 0=0) ∧
    (∀ (h : ℝ) (k : ℕ), 0 < h → (k:ℝ)/h ≤ ν₀ →
      ‖poissonCoefficientOperator h k (fun u=>f (u,((k:ℝ)/h:ℝ)))‖ ≤ C) := by
  let R₀ : ℝ := R/2
  have hR₀ : 0 < R₀ := half_pos hR
  obtain ⟨νa,C₀,hνa,hνaR,hC₀,hreal⟩ := poisson_central_real_gevrey R₀ hR₀
  let ν₀ : ℝ := min νa (1/2)
  have hν₀ : 0 < ν₀ := lt_min hνa (by norm_num)
  have hνold : ν₀ ≤ νa := min_le_left _ _
  have hνsmall : ν₀ ≤ 1/2 := min_le_right _ _
  have hνR : ν₀ < R₀/4 := hνold.trans_lt hνaR
  let D : ℝ := 8*(max 1 (4/R₀))^2
  let C : ℝ := max C₀ (max 1 D)
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCD : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC2 : 2 ≤ C := hC₀.trans hC₀C
  have hνR8 : ν₀ < R/8 := by dsimp [R₀] at hνR;linarith
  refine ⟨ν₀,C,hν₀,by linarith,by linarith,?_⟩
  intro f hf hb
  have hslice (ν : ℂ) (hν : ‖ν‖ ≤ ν₀) :
      AnalyticOnNhd ℂ (fun u=>f (u,ν)) (Metric.closedBall 0 R₀) ∧
        (∀u∈Metric.closedBall (0:ℂ) R₀,‖f (u,ν)‖ ≤ 1) := by
    refine ⟨poisson_joint_slice_closed_ball f R hR hf ν (by linarith),?_⟩
    intro u hu
    have hu' : ‖u‖ ≤ R/2 := by simpa only [R₀,Metric.mem_closedBall,dist_zero_right] using hu
    apply hb
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_mk,max_lt_iff]
    exact ⟨by linarith,by linarith⟩
  have hdiag (ν : ℂ) (hν : ‖ν‖ < ν₀) : (ν,ν)∈Metric.ball (0:ℂ × ℂ) R := by
    rw [Metric.mem_ball,dist_zero_right,Prod.norm_mk,max_self]
    linarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro h k K hh hν hK
    let ν : ℂ := (((k:ℝ)/h:ℝ):ℂ)
    have hn : ‖ν‖ ≤ ν₀ := by dsimp [ν];rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)];exact hν
    obtain ⟨hfa,hfb⟩ := hslice ν hn
    have ht := hreal (fun u=>f (u,ν)) hfa hfb h k K hh (hν.trans hνold) hK
    have ht' : ‖poissonCoefficientOperator h k (fun u=>f (u,ν))-
        ∑j∈Finset.range (K+1),poissonCentralAmplitude f j ν/(h:ℂ)^j‖ ≤
          C₀^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
      simpa only [poissonCentralAmplitude_eq_functional,ν,Complex.ofReal_div,Complex.ofReal_natCast] using ht
    exact ht'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hC₀C _) (by positivity)) (by positivity))
  · intro j ν hν
    have hn : ‖ν‖ < ν₀ := by simpa only [Metric.mem_ball,dist_zero_right] using hν
    by_cases hj : j=0
    · subst j
      have he : poissonCentralAmplitude f 0=(fun v : ℂ=>f (v,v)) := by funext v;exact poissonCentralAmplitude_zero f v
      rw [he]
      exact (hf _ (hdiag ν hn)).comp (f:=fun v : ℂ=>(v,v)) (analyticAt_id.prod analyticAt_id)
    · have he : poissonCentralAmplitude f j=(fun v : ℂ=>∑m∈Finset.Icc (j+1) (2*j),
          (poissonCentralInverseCoefficient m j:ℂ)*v^(m-j)*WP.coeff (fun z=>f (v+z,v)) m) := by
        funext v
        rw [poissonCentralAmplitude,ite_eq_right hj]
      rw [he]
      apply Finset.analyticAt_fun_sum
      intro m hm
      exact (analyticAt_const.mul (analyticAt_id.pow _)).mul
        (Analysis.diagonalCoeff_analyticAt f _ Metric.isOpen_ball hf m ν (hdiag ν hn))
  · intro j ν hν
    obtain ⟨hfa,hfb⟩ := hslice ν hν.le
    have hc (m : ℕ) : ‖WP.coeff (fun z=>f (ν+z,ν)) m‖ ≤ 1/(R₀/2)^m :=
      poisson_shifted_coeff_norm R₀ 1 hR₀ (fun u=>f (u,ν)) hfa hfb ν (by linarith) m
    have hn1 : ‖ν‖ ≤ 1 := by linarith
    have ht := poissonCentralFunctional_norm_le (R₀/2) 1 (half_pos hR₀) (by norm_num)
      (fun m=>WP.coeff (fun z=>f (ν+z,ν)) m) hc ν hn1 j
    have ht' : ‖poissonCentralAmplitude f j ν‖ ≤ D^j*(j.factorial:ℝ) := by
      simpa only [poissonCentralAmplitude_eq_functional,one_mul,D,show (2:ℝ)/(R₀/2)=4/R₀ by ring] using ht
    apply ht'.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (pow_le_pow_left₀ (by dsimp [D];positivity) hCD _).trans (pow_le_pow_right₀ hC1 (Nat.le_succ j))
  · exact poissonCentralAmplitude_at_zero f
  · intro h k hh hν
    let ν : ℂ := (((k:ℝ)/h:ℝ):ℂ)
    have hn : ‖ν‖ ≤ ν₀ := by dsimp [ν];rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)];exact hν
    obtain ⟨hfa,hfb⟩ := hslice ν hn
    have ht := poissonCoefficientOperator_norm_le h R₀ 1 hh hR₀ (by norm_num) k
      (by linarith) (fun u=>f (u,ν)) hfa (fun u hu=>hfb u (Metric.sphere_subset_closedBall hu))
    exact (by simpa only [mul_one] using ht : ‖poissonCoefficientOperator h k (fun u=>f (u,ν))‖ ≤ 2).trans hC2
end WP.HigherOrder
