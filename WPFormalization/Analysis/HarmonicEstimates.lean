import WPFormalization.Analysis.HarmonicProbability
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma harmonicMass_exponential_uniform : ∃ t C:ℝ,0<t ∧ 0<C ∧ ∀Y∈Icc (0:ℝ) y₀,
    HasSum (fun m:ℕ=>Real.exp (t*m)*harmonicMass Y m) (harmonicPGF Y (Real.exp t)).re ∧
    (harmonicPGF Y (Real.exp t)).re ≤ C := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  let q : ℝ := 1+η/2
  have hq : 1<q := by dsimp [q]; linarith
  have hq0 : 0<q := lt_trans zero_lt_one hq
  have hqc : (q:ℂ) ∈ Metric.closedBall 0 (1+η) := by
    rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]
    dsimp [q]
    linarith
  have hcont : Continuous (fun Y:Icc (0:ℝ) y₀ => (harmonicPGF (Y:ℝ) (q:ℂ)).re) :=
    Complex.continuous_re.comp ((harmonicPGF_joint_closed hη hzero).comp
      (continuous_id.prodMk (continuous_const (y := (⟨(q:ℂ),hqc⟩:Metric.closedBall (0:ℂ) (1+η))))))
  obtain ⟨B,hB⟩ := isCompact_univ.bddAbove_image hcont.continuousOn
  refine ⟨Real.log q,max B 1,Real.log_pos hq,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro Y hY
  have he : Real.exp (Real.log q)=q := Real.exp_log hq0
  have hs := harmonicMass_hasSum_weighted hη hzero Y hY q (by rw [abs_of_pos hq0]; dsimp [q]; linarith)
  constructor
  · rw [he]
    convert hs using 1
    ext m
    rw [mul_comm (Real.log q) (m:ℝ),Real.exp_nat_mul,he,mul_comm]
  · rw [he]
    exact (hB (mem_image_of_mem _ (show (⟨Y,hY⟩:Icc (0:ℝ) y₀)∈univ from mem_univ _))).trans (le_max_left _ _)
lemma centered_square_le_exp (t:ℝ)(ht:0<t)(m:ℕ) :
    ((m:ℝ)-3/2)^2 ≤ (4/t^2+9/2)*Real.exp (t*m) := by
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hexp := Real.pow_div_factorial_le_exp (t*m) (mul_nonneg ht.le hm) 2
  norm_num at hexp
  have hp : 0<t^2 := sq_pos_of_pos ht
  have hpow : (m:ℝ)^2 ≤ 2/t^2*Real.exp (t*m) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith [hexp]
  have he1 : 1≤Real.exp (t*m) := Real.one_le_exp (mul_nonneg ht.le hm)
  have hD : 0≤4/t^2 := by positivity
  have heq : (4/t^2+9/2)*Real.exp (t*m) = 2*(2/t^2*Real.exp (t*m))+9/2*Real.exp (t*m) := by ring
  rw [heq]
  nlinarith [sq_nonneg ((m:ℝ)+3/2)]
lemma harmonicVariance_summable (Y:ℝ)(hY:Y∈Icc 0 y₀) :
    Summable (fun m:ℕ=>((m:ℝ)-3/2)^2*harmonicMass Y m) := by
  obtain ⟨t,C,ht,hC,hbound⟩ := harmonicMass_exponential_uniform
  have hS := (hbound Y hY).1.summable.mul_left (4/t^2+9/2)
  apply Summable.of_nonneg_of_le (fun m=>mul_nonneg (sq_nonneg _) (harmonicMass_pos Y hY m).le) _ hS
  intro m
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (centered_square_le_exp t ht m) (harmonicMass_pos Y hY m).le
lemma harmonicVariance_lower (Y:ℝ)(hY:Y∈Icc 0 y₀) : (9/4)*harmonicMass Y 0 ≤ harmonicVariance Y := by
  have hh := (harmonicVariance_summable Y hY).le_tsum 0 (fun m _=>mul_nonneg (sq_nonneg _) (harmonicMass_pos Y hY m).le)
  norm_num only [Nat.cast_zero,zero_sub,neg_sq,div_pow] at hh
  exact hh
set_option maxHeartbeats 600000 in
lemma harmonic_uniform_bounds : ∃ c C t:ℝ,0<c ∧ 0<C ∧ 0<t ∧ ∀Y∈Icc (0:ℝ) y₀,
    c≤harmonicMass Y 0 ∧ c≤harmonicMass Y 1 ∧ c≤harmonicVariance Y ∧ harmonicVariance Y≤C ∧
    Summable (fun m:ℕ=>Real.exp (t*m)*harmonicMass Y m) ∧
    ∑'m:ℕ, Real.exp (t*m)*harmonicMass Y m≤C := by
  let S := Icc (0:ℝ) y₀
  have hS : (univ:Set S).Nonempty := ⟨⟨0,le_rfl,y₀_pos.le⟩,mem_univ _⟩
  have hc : Continuous (fun Y:S => min (harmonicMass (Y:ℝ) 0) (harmonicMass (Y:ℝ) 1)) :=
    (harmonicMass_continuous 0).min (harmonicMass_continuous 1)
  obtain ⟨Ymin,_,hmin⟩ := isCompact_univ.exists_isMinOn (f := fun Y:S => min (harmonicMass (Y:ℝ) 0) (harmonicMass (Y:ℝ) 1)) hS hc.continuousOn
  let c := min (harmonicMass (Ymin:ℝ) 0) (harmonicMass (Ymin:ℝ) 1)
  have hcP : 0<c := lt_min (harmonicMass_pos Ymin Ymin.property 0) (harmonicMass_pos Ymin Ymin.property 1)
  obtain ⟨t,B,ht,hB,hbound⟩ := harmonicMass_exponential_uniform
  let D := 4/t^2+9/2
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨c,max B (D*B),t,hcP,lt_of_lt_of_le hB (le_max_left _ _),ht,?_⟩
  intro Y hY
  have hcY : c ≤ min (harmonicMass Y 0) (harmonicMass Y 1) := (isMinOn_iff.mp hmin) (⟨Y,hY⟩:S) (mem_univ _)
  have hc0 := hcY.trans (min_le_left _ _)
  have hc1 := hcY.trans (min_le_right _ _)
  have hExp := (hbound Y hY).1
  have hExpB := (hbound Y hY).2
  have hVar : harmonicVariance Y ≤ D*(harmonicPGF Y (Real.exp t)).re := by
    calc harmonicVariance Y = ∑'m:ℕ,((m:ℝ)-3/2)^2*harmonicMass Y m := rfl
         _ ≤ ∑'m:ℕ,D*(Real.exp (t*m)*harmonicMass Y m) :=
           Summable.tsum_le_tsum
             (fun m=>by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (centered_square_le_exp t ht m) (harmonicMass_pos Y hY m).le)
             (harmonicVariance_summable Y hY) (hExp.summable.mul_left D)
         _ = D*(∑'m:ℕ,Real.exp (t*m)*harmonicMass Y m) := tsum_mul_left
         _ = D*(harmonicPGF Y (Real.exp t)).re := congrArg (fun x=>D*x) hExp.tsum_eq
  refine ⟨hc0,hc1,?_,hVar.trans ((mul_le_mul_of_nonneg_left hExpB hD.le).trans (le_max_right _ _)),hExp.summable,?_⟩
  · have hlow := harmonicVariance_lower Y hY
    nlinarith only [hc0,hlow,harmonicMass_pos Y hY 0]
  · exact hExp.tsum_eq.trans_le (hExpB.trans (le_max_left _ _))
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma critical_harmonic_second_deriv : deriv (deriv (harmonicPGF y₀)) 1 = 9/2 := by
  have he : harmonicPGF y₀ = fun z:ℂ => (2/5:ℂ)*(1-(3/5:ℂ)*z)^(-1:ℤ) := by
    funext z
    simp [harmonicPGF,barH,div_eq_mul_inv]
    ring_nf
    simp
  have hd : deriv (deriv (harmonicPGF y₀)) = iteratedDeriv 2 (harmonicPGF y₀) := by simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hd]
  rw [he,iteratedDeriv_const_mul_field]
  have hh : (fun z:ℂ=>(1-(3/5:ℂ)*z)^(-1:ℤ)) = (fun z:ℂ=>(1-z)^(-1:ℤ)) ∘ (fun z:ℂ=>(3/5:ℂ)*z) := rfl
  rw [hh]
  simp only [Function.comp_def]
  rw [iteratedDeriv_comp_mul_left (fun z:ℂ=>(1-z)^(-1:ℤ)) (3/5) 2 1]
  rw [iteratedDeriv_comp_const_sub (f:=fun z:ℂ=>z^(-1:ℤ)) (s:=(1:ℂ))]
  simp only [iteratedDeriv_eq_iterate,iter_deriv_zpow',smul_eq_mul]
  norm_num [Finset.prod_range_succ]
lemma harmonicMass_second_moment (Y:ℝ)(hY:Y∈Icc 0 y₀) :
    HasSum (fun m:ℕ=>(m:ℝ)^2*harmonicMass Y m)
      (deriv (harmonicPGF Y) 1+deriv (deriv (harmonicPGF Y)) 1).re := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  let f := harmonicPGF Y
  let g : ℂ→ℂ := fun z=>z*deriv f z
  have hf := (harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall
  have hA (z:ℂ)(hz:z∈Metric.ball 0 (1+η)) : AnalyticAt ℂ f z := hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hG (z:ℂ)(hz:z∈Metric.ball 0 (1+η)) : AnalyticAt ℂ g z := analyticAt_id.mul (hA z hz).deriv
  have hz0 : (0:ℂ)∈Metric.ball 0 (1+η) := by simp only [Metric.mem_ball,dist_self]; linarith
  have hz1 : (1:ℂ)∈Metric.ball 0 (1+η) := by norm_num; linarith
  have hD : DifferentiableOn ℂ (fun z=>z*deriv g z) (Metric.ball 0 (1+η)) := by
    intro z hz
    exact (differentiableAt_id.mul (hG z hz).deriv.differentiableAt).differentiableWithinAt
  have hderiv : deriv g 1 = deriv f 1+deriv (deriv f) 1 := by
    exact ((hasDerivAt_id (1:ℂ)).mul (hA 1 hz1).deriv.differentiableAt.hasDerivAt).deriv.trans (by simp only [id_eq,one_mul])
  have hs := hasSum_coeff_on_ball _ (1+η) hD 1 (by norm_num; linarith)
  rw [one_mul,hderiv] at hs
  convert Complex.hasSum_re hs using 1
  ext n
  rw [one_pow,mul_one,harmonic_coeff_euler _ (hG 0 hz0) n,harmonic_coeff_euler _ (hA 0 hz0) n]
  change (n:ℝ)^2*(WP.coeff f n).re = ((n:ℂ)*((n:ℂ)*WP.coeff f n)).re
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  ring
lemma harmonicVariance_critical : harmonicVariance y₀=15/4 := by
  have hY : y₀∈Icc (0:ℝ) y₀ := ⟨y₀_pos.le,le_rfl⟩
  have h0 := harmonicMass_hasSum y₀ hY
  have h1 := harmonicMass_mean y₀ hY
  have h2 := harmonicMass_second_moment y₀ hY
  rw [harmonicPGF_deriv_one y₀ hY,critical_harmonic_second_deriv] at h2
  norm_num at h2
  have hs := (h2.sub (h1.mul_left 3)).add (h0.mul_left (9/4))
  have he : (fun m:ℕ=>((m:ℝ)-3/2)^2*harmonicMass y₀ m) =
      (fun m:ℕ=>(m:ℝ)^2*harmonicMass y₀ m-3*((m:ℝ)*harmonicMass y₀ m)+9/4*harmonicMass y₀ m) := by funext m; ring
  rw [harmonicVariance,he]
  exact hs.tsum_eq.trans (by norm_num)
end WP.Analysis
