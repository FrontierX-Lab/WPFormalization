import WPFormalization.Analysis.CriticalCuspCoordinates
import WPFormalization.Volumes.PlanarInverse
import WPFormalization.Statements.ConvolutionDefinitions
import Mathlib.Analysis.Complex.SqrtDeriv
/-! The actual quadratic critical X coordinate, its holomorphic inverse,
and the Puiseux identity for the genuine planar third derivative. The branch
is selected through the actual real inverse and continued over a convex lens.
Every fold, residue, inverse and complex identity is proved locally; no
Puiseux or Fourier estimate is assumed as an external result. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma complex_analytic_quadratic_factor (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (h0 : f 0=0) (h1 : deriv f 0=0) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0=iteratedDeriv 2 f 0/2 ∧
      ∀ᶠ z in 𝓝 0, f z=z^2*B z := by
  obtain ⟨B,hB,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,iteratedDeriv_zero,iteratedDeriv_one,
    h0,h1,smul_eq_mul,mul_zero,zero_add] at he
  refine ⟨B,hB,?_,he⟩
  have heq : f =ᶠ[𝓝 (0:ℂ)] (fun z => z^2*B z) := he
  have hj := heq.iteratedDeriv_eq 2
  rw [iteratedDeriv_fun_mul (by fun_prop) hB.contDiffAt] at hj
  norm_num [Finset.sum_range_succ,iteratedDeriv_fun_pow_zero,iteratedDeriv_zero] at hj
  linear_combination -hj / 2

def complexCriticalGap (δ : ℂ) : ℂ := 1-X ((y₀:ℂ)-δ)/(xCritical:ℂ)
lemma X_critical_value : X (y₀:ℂ)=(xCritical:ℂ) := by
  apply Complex.ext
  · rfl
  · simp [X_im_ofReal]
lemma X_second_critical_value : iteratedDeriv 2 X (y₀:ℂ)=(-(criticalB:ℝ):ℂ) := by
  apply Complex.ext
  · simp [criticalB]
  · simp [iteratedDeriv_X_im_ofReal]
lemma complexCriticalGap_analytic : AnalyticAt ℂ complexCriticalGap 0 :=
  analyticAt_const.sub (((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)).div_const)
lemma complexCriticalGap_zero : complexCriticalGap 0=0 := by
  simp only [complexCriticalGap,sub_zero,X_critical_value]
  rw [div_self (by exact_mod_cast critical_x_pos.ne'),sub_self]
lemma complexCriticalGap_deriv_zero : deriv complexCriticalGap 0=0 := by
  have hD : HasDerivAt (fun z : ℂ => (y₀:ℂ)-z) (-1) 0 := by
    convert! (hasDerivAt_const (0:ℂ) (y₀:ℂ)).sub (hasDerivAt_id (0:ℂ)) using 1 <;> simp only [zero_sub,id_eq,Pi.sub_apply]
  have h := (hasDerivAt_const (0:ℂ) (1:ℂ)).sub ((((X_differentiable _).hasDerivAt).comp 0 hD).div_const (xCritical:ℂ))
  convert! h.deriv using 1 <;> simp only [complexCriticalGap,Function.comp_def,Pi.sub_apply,sub_zero,derivX_y₀_zero,zero_mul,zero_div]
lemma complexCriticalGap_second_deriv :
    iteratedDeriv 2 complexCriticalGap 0=((criticalB/xCritical:ℝ):ℂ) := by
  have hxa : AnalyticAt ℂ (fun z : ℂ => X ((y₀:ℂ)-z)/(xCritical:ℂ)) 0 :=
    ((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_id)).div_const
  change iteratedDeriv 2 (fun δ : ℂ => 1-X ((y₀:ℂ)-δ)/(xCritical:ℂ)) 0=_
  rw [iteratedDeriv_fun_sub (by fun_prop) hxa.contDiffAt,iteratedDeriv_div_const,
    iteratedDeriv_comp_const_sub]
  simp only [iteratedDeriv_const,Nat.ofNat_pos,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,ite_false,
    sub_zero,neg_one_sq,one_smul,X_second_critical_value]
  push_cast
  ring
lemma complexCriticalGap_factor :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0=((criticalB/(2*xCritical):ℝ):ℂ) ∧
      ∀ᶠ z in 𝓝 0, complexCriticalGap z=z^2*B z := by
  obtain ⟨B,hB,hB0,he⟩ := complex_analytic_quadratic_factor complexCriticalGap complexCriticalGap_analytic
    complexCriticalGap_zero complexCriticalGap_deriv_zero
  refine ⟨B,hB,?_,he⟩
  rw [hB0,complexCriticalGap_second_deriv]
  push_cast
  ring
lemma complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z := by
  rw [Complex.sqrt,←Complex.cpow_mul_nat]
  norm_num

lemma complex_sqrt_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) : AnalyticAt ℂ Complex.sqrt z :=
  Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane z hz

lemma critical_fold_local_coordinate :
    ∃ (D : ℂ → ℂ) (b : ℝ), 0 < b ∧ AnalyticAt ℂ D 0 ∧ D 0=0 ∧
      deriv D 0=((Real.sqrt b)⁻¹:ℝ) ∧ b=criticalB/(2*xCritical) ∧
      (∀ᶠ t in 𝓝 (0:ℂ), X ((y₀:ℂ)-D t)=(xCritical:ℂ)*(1-t^2)) := by
  obtain ⟨B,hB,hB0,hfactor⟩ := complexCriticalGap_factor
  let b : ℝ := criticalB/(2*xCritical)
  have hb : 0 < b := div_pos criticalB_pos (mul_pos (by norm_num) critical_x_pos)
  have hBplane : B 0 ∈ Complex.slitPlane := by rw [hB0];exact Or.inl hb
  have hs : AnalyticAt ℂ (fun δ => Complex.sqrt (B δ)) 0 := (complex_sqrt_analyticAt hBplane).comp hB
  let Q : ℂ → ℂ := fun δ => δ*Complex.sqrt (B δ)
  have hQ : AnalyticAt ℂ Q 0 := analyticAt_id.mul hs
  have hQ0 : Q 0=0 := by simp [Q]
  have hs0 : Complex.sqrt (B 0)=((Real.sqrt b:ℝ):ℂ) := by
    rw [hB0]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hb.le)
  have hdQ : HasDerivAt Q ((Real.sqrt b:ℝ):ℂ) 0 := by
    convert! (hasDerivAt_id (0:ℂ)).mul hs.differentiableAt.hasDerivAt using 1 <;>
      simp only [Q,id_eq,Pi.mul_apply,zero_mul,one_mul,add_zero,hs0]
  have hQne : deriv Q 0 ≠ 0 := by rw [hdQ.deriv];exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  let D := hQ.hasStrictDerivAt.localInverse Q (deriv Q 0) 0 hQne
  have hDa : AnalyticAt ℂ D 0 := by simpa only [hQ0] using hQ.analyticAt_localInverse hQne
  have hD0 : D 0=0 := by simpa only [hQ0] using (hQ.hasStrictDerivAt.eventually_left_inverse hQne).self_of_nhds
  have hDd : deriv D 0=(((Real.sqrt b)⁻¹:ℝ):ℂ) := by
    have hd := (hQ.hasStrictDerivAt.to_localInverse hQne).hasDerivAt
    simpa only [hQ0,hdQ.deriv,Complex.ofReal_inv] using hd.deriv
  have hright : ∀ᶠ t in 𝓝 (0:ℂ), Q (D t)=t := by simpa only [hQ0] using hQ.hasStrictDerivAt.eventually_right_inverse hQne
  have hDt : Tendsto D (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by simpa only [hD0] using hDa.continuousAt.tendsto
  refine ⟨D,b,hb,hDa,hD0,hDd,rfl,?_⟩
  filter_upwards [hright,hDt.eventually hfactor] with t ht hf
  have he : t^2=complexCriticalGap (D t) := by
    calc t^2=(Q (D t))^2 := congrArg (fun w : ℂ => w^2) ht.symm
         _=(D t)^2*B (D t) := by dsimp only [Q];rw [mul_pow,complex_sqrt_sq]
         _=complexCriticalGap (D t) := hf.symm
  dsimp only [complexCriticalGap] at he
  have hxc : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  field_simp [hxc] at he
  linear_combination he
lemma critical_fold_local_coordinate_data :
    ∃ (B D : ℂ → ℂ) (b : ℝ), 0 < b ∧ AnalyticAt ℂ B 0 ∧ B 0=(b:ℂ) ∧
      AnalyticAt ℂ D 0 ∧ D 0=0 ∧ deriv D 0=((Real.sqrt b)⁻¹:ℝ) ∧ b=criticalB/(2*xCritical) ∧
      (∀ᶠ δ in 𝓝 (0:ℂ), complexCriticalGap δ=δ^2*B δ) ∧
      (∀ᶠ δ in 𝓝 (0:ℂ), D (δ*Complex.sqrt (B δ))=δ) ∧
      (∀ᶠ t in 𝓝 (0:ℂ), X ((y₀:ℂ)-D t)=(xCritical:ℂ)*(1-t^2)) := by
  obtain ⟨B,hB,hB0,hfactor⟩ := complexCriticalGap_factor
  let b : ℝ := criticalB/(2*xCritical)
  have hb : 0 < b := div_pos criticalB_pos (mul_pos (by norm_num) critical_x_pos)
  have hBplane : B 0 ∈ Complex.slitPlane := by rw [hB0];exact Or.inl hb
  have hs : AnalyticAt ℂ (fun δ => Complex.sqrt (B δ)) 0 := (complex_sqrt_analyticAt hBplane).comp hB
  let Q : ℂ → ℂ := fun δ => δ*Complex.sqrt (B δ)
  have hQ : AnalyticAt ℂ Q 0 := analyticAt_id.mul hs
  have hQ0 : Q 0=0 := by simp [Q]
  have hs0 : Complex.sqrt (B 0)=((Real.sqrt b:ℝ):ℂ) := by
    rw [hB0]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hb.le)
  have hdQ : HasDerivAt Q ((Real.sqrt b:ℝ):ℂ) 0 := by
    convert! (hasDerivAt_id (0:ℂ)).mul hs.differentiableAt.hasDerivAt using 1 <;>
      simp only [Q,id_eq,Pi.mul_apply,zero_mul,one_mul,add_zero,hs0]
  have hQne : deriv Q 0 ≠ 0 := by rw [hdQ.deriv];exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  let D := hQ.hasStrictDerivAt.localInverse Q (deriv Q 0) 0 hQne
  have hDa : AnalyticAt ℂ D 0 := by simpa only [hQ0] using hQ.analyticAt_localInverse hQne
  have hD0 : D 0=0 := by simpa only [hQ0] using (hQ.hasStrictDerivAt.eventually_left_inverse hQne).self_of_nhds
  have hDd : deriv D 0=(((Real.sqrt b)⁻¹:ℝ):ℂ) := by
    have hd := (hQ.hasStrictDerivAt.to_localInverse hQne).hasDerivAt
    simpa only [hQ0,hdQ.deriv,Complex.ofReal_inv] using hd.deriv
  have hright : ∀ᶠ t in 𝓝 (0:ℂ), Q (D t)=t := by simpa only [hQ0] using hQ.hasStrictDerivAt.eventually_right_inverse hQne
  have hDt : Tendsto D (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by simpa only [hD0] using hDa.continuousAt.tendsto
  have hleft : ∀ᶠ δ in 𝓝 (0:ℂ), D (δ*Complex.sqrt (B δ))=δ :=
    hQ.hasStrictDerivAt.eventually_left_inverse hQne
  refine ⟨B,D,b,hb,hB,hB0,hDa,hD0,hDd,rfl,hfactor,hleft,?_⟩
  filter_upwards [hright,hDt.eventually hfactor] with t ht hf
  have he : t^2=complexCriticalGap (D t) := by
    calc t^2=(Q (D t))^2 := congrArg (fun w : ℂ => w^2) ht.symm
         _=(D t)^2*B (D t) := by dsimp only [Q];rw [mul_pow,complex_sqrt_sq]
         _=complexCriticalGap (D t) := hf.symm
  dsimp only [complexCriticalGap] at he
  have hxc : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  field_simp [hxc] at he
  linear_combination he
end WP.Analysis
namespace WP.Analysis
lemma complex_analytic_linear_factor (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (h0 : f 0=0) :
    ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ C 0=deriv f 0 ∧
      ∀ᶠ t in 𝓝 (0:ℂ), f t=t*C t := by
  obtain ⟨C,hC,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.cast_one,div_one,iteratedDeriv_zero,h0,smul_eq_mul,mul_zero,zero_add] at he
  have heq : f =ᶠ[𝓝 (0:ℂ)] (fun t => t*C t) := he
  have hd : HasDerivAt (fun t : ℂ => t*C t) (C 0) 0 := by
    convert! (hasDerivAt_id (0:ℂ)).mul hC.differentiableAt.hasDerivAt using 1 <;> simp
  exact ⟨C,hC,heq.deriv_eq.trans hd.deriv |>.symm,he⟩

lemma critical_fold_residue_data :
    ∃ (D Ξ : ℂ → ℂ) (b c : ℝ), 0 < b ∧ 0 < c ∧
      AnalyticAt ℂ D 0 ∧ D 0=0 ∧ deriv D 0=(((Real.sqrt b)⁻¹:ℝ):ℂ) ∧
      b=criticalB/(2*xCritical) ∧ c=criticalB*(Real.sqrt b)⁻¹ ∧
      AnalyticAt ℂ Ξ 0 ∧ Ξ 0=1 ∧
      (∀ᶠ t in 𝓝 (0:ℂ), X ((y₀:ℂ)-D t)=(xCritical:ℂ)*(1-t^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℂ), t≠0 → deriv X ((y₀:ℂ)-D t)*((c:ℂ)⁻¹*Ξ t/t)=1) := by
  obtain ⟨D,b,hb,hDa,hD0,hDd,hbdef,hfold⟩ := critical_fold_local_coordinate
  let g : ℂ → ℂ := fun t => deriv X ((y₀:ℂ)-D t)
  have hga : AnalyticAt ℂ g 0 := ((X_differentiable.analyticAt _).deriv).comp (analyticAt_const.sub hDa)
  have hg0 : g 0=0 := by simp only [g,hD0,sub_zero,derivX_y₀_zero]
  let c : ℝ := criticalB*(Real.sqrt b)⁻¹
  have hc : 0 < c := mul_pos criticalB_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb))
  have hgD : HasDerivAt g (c:ℂ) 0 := by
    have hX : HasDerivAt (deriv X) (iteratedDeriv 2 X (y₀:ℂ)) (y₀:ℂ) := by
      convert! ((X_differentiable.analyticAt (y₀:ℂ)).deriv).differentiableAt.hasDerivAt using 1 <;> simp only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    have hshift : HasDerivAt (fun t : ℂ => (y₀:ℂ)-D t) (-(((Real.sqrt b)⁻¹:ℝ):ℂ)) 0 := by
      convert! (hasDerivAt_const (0:ℂ) (y₀:ℂ)).sub hDa.differentiableAt.hasDerivAt using 1 <;> simp only [hDd,zero_sub,Pi.sub_apply]
    have hXi : HasDerivAt (deriv X) (iteratedDeriv 2 X (y₀:ℂ)) ((y₀:ℂ)-D 0) := by simpa only [hD0,sub_zero] using hX
    convert! hXi.comp 0 hshift using 1
    rw [X_second_critical_value]
    dsimp [c]
    push_cast
    ring
  obtain ⟨C,hCa,hC0,hCfactor⟩ := complex_analytic_linear_factor g hga hg0
  have hCzero : C 0=(c:ℂ) := hC0.trans hgD.deriv
  have hCne : C 0 ≠ 0 := by rw [hCzero];exact_mod_cast hc.ne'
  let Ξ : ℂ → ℂ := fun t => (c:ℂ)/C t
  have hΞ : AnalyticAt ℂ Ξ 0 := analyticAt_const.div hCa hCne
  have hΞ0 : Ξ 0=1 := by dsimp [Ξ];rw [hCzero];exact div_self (by exact_mod_cast hc.ne')
  refine ⟨D,Ξ,b,c,hb,hc,hDa,hD0,hDd,hbdef,rfl,hΞ,hΞ0,hfold,?_⟩
  filter_upwards [hCfactor,hCa.continuousAt.eventually_ne hCne] with t ht hn htn
  dsimp only [Ξ]
  change g t*((c:ℂ)⁻¹*((c:ℂ)/C t)/t)=1
  rw [ht]
  field_simp [hn,htn,show (c:ℂ) ≠ 0 by exact_mod_cast hc.ne']
lemma critical_fold_residue_for_coordinate (D : ℂ → ℂ) (b : ℝ) (hb : 0 < b)
    (hDa : AnalyticAt ℂ D 0) (hD0 : D 0=0) (hDd : deriv D 0=(((Real.sqrt b)⁻¹:ℝ):ℂ)) :
    ∃ (Ξ : ℂ → ℂ) (c : ℝ), 0 < c ∧ c=criticalB*(Real.sqrt b)⁻¹ ∧
      AnalyticAt ℂ Ξ 0 ∧ Ξ 0=1 ∧
      (∀ᶠ t in 𝓝 (0:ℂ), t≠0 → deriv X ((y₀:ℂ)-D t)*((c:ℂ)⁻¹*Ξ t/t)=1) := by
  let g : ℂ → ℂ := fun t => deriv X ((y₀:ℂ)-D t)
  have hga : AnalyticAt ℂ g 0 := ((X_differentiable.analyticAt _).deriv).comp (analyticAt_const.sub hDa)
  have hg0 : g 0=0 := by simp only [g,hD0,sub_zero,derivX_y₀_zero]
  let c : ℝ := criticalB*(Real.sqrt b)⁻¹
  have hc : 0 < c := mul_pos criticalB_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb))
  have hgD : HasDerivAt g (c:ℂ) 0 := by
    have hX : HasDerivAt (deriv X) (iteratedDeriv 2 X (y₀:ℂ)) (y₀:ℂ) := by
      convert! ((X_differentiable.analyticAt (y₀:ℂ)).deriv).differentiableAt.hasDerivAt using 1 <;> simp only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    have hshift : HasDerivAt (fun t : ℂ => (y₀:ℂ)-D t) (-(((Real.sqrt b)⁻¹:ℝ):ℂ)) 0 := by
      convert! (hasDerivAt_const (0:ℂ) (y₀:ℂ)).sub hDa.differentiableAt.hasDerivAt using 1 <;> simp only [hDd,zero_sub,Pi.sub_apply]
    have hXi : HasDerivAt (deriv X) (iteratedDeriv 2 X (y₀:ℂ)) ((y₀:ℂ)-D 0) := by simpa only [hD0,sub_zero] using hX
    convert! hXi.comp 0 hshift using 1
    rw [X_second_critical_value]
    dsimp [c]
    push_cast
    ring
  obtain ⟨C,hCa,hC0,hCfactor⟩ := complex_analytic_linear_factor g hga hg0
  have hCzero : C 0=(c:ℂ) := hC0.trans hgD.deriv
  have hCne : C 0 ≠ 0 := by rw [hCzero];exact_mod_cast hc.ne'
  let Ξ : ℂ → ℂ := fun t => (c:ℂ)/C t
  have hΞ : AnalyticAt ℂ Ξ 0 := analyticAt_const.div hCa hCne
  have hΞ0 : Ξ 0=1 := by dsimp [Ξ];rw [hCzero];exact div_self (by exact_mod_cast hc.ne')
  refine ⟨Ξ,c,hc,rfl,hΞ,hΞ0,?_⟩
  filter_upwards [hCfactor,hCa.continuousAt.eventually_ne hCne] with t ht hn htn
  dsimp only [Ξ]
  change g t*((c:ℂ)⁻¹*((c:ℂ)/C t)/t)=1
  rw [ht]
  field_simp [hn,htn,show (c:ℂ) ≠ 0 by exact_mod_cast hc.ne']
end WP.Analysis
namespace WP.Analysis
structure CriticalFoldData where
  B : ℂ → ℂ
  D : ℂ → ℂ
  Ξ : ℂ → ℂ
  b : ℝ
  c : ℝ
  b_pos : 0 < b
  c_pos : 0 < c
  B_analytic : AnalyticAt ℂ B 0
  B_zero : B 0=(b:ℂ)
  D_analytic : AnalyticAt ℂ D 0
  D_zero : D 0=0
  D_deriv : deriv D 0=(((Real.sqrt b)⁻¹:ℝ):ℂ)
  b_eq : b=criticalB/(2*xCritical)
  c_eq : c=criticalB*(Real.sqrt b)⁻¹
  Xi_analytic : AnalyticAt ℂ Ξ 0
  Xi_zero : Ξ 0=1
  gap_factor : ∀ᶠ δ in 𝓝 (0:ℂ), complexCriticalGap δ=δ^2*B δ
  left_inverse : ∀ᶠ δ in 𝓝 (0:ℂ), D (δ*Complex.sqrt (B δ))=δ
  fold_identity : ∀ᶠ t in 𝓝 (0:ℂ), X ((y₀:ℂ)-D t)=(xCritical:ℂ)*(1-t^2)
  residue_identity : ∀ᶠ t in 𝓝 (0:ℂ), t≠0 → deriv X ((y₀:ℂ)-D t)*((c:ℂ)⁻¹*Ξ t/t)=1

lemma exists_criticalFoldData : Nonempty CriticalFoldData := by
  obtain ⟨B,D,b,hb,hBa,hB0,hDa,hD0,hDd,hbdef,hfactor,hleft,hfold⟩ := critical_fold_local_coordinate_data
  obtain ⟨Ξ,c,hc,hcdef,hΞ,hΞ0,hres⟩ := critical_fold_residue_for_coordinate D b hb hDa hD0 hDd
  exact ⟨⟨B,D,Ξ,b,c,hb,hc,hBa,hB0,hDa,hD0,hDd,hbdef,hcdef,hΞ,hΞ0,hfactor,hleft,hfold,hres⟩⟩
end WP.Analysis
namespace WP.Analysis
lemma X_eq_ofReal_XR (Y : ℝ) : X (Y:ℂ)=(XR Y:ℂ) := by
  apply Complex.ext
  · rfl
  · simp [X_im_ofReal]
lemma complexCriticalGap_ofReal (δ : ℝ) :
    complexCriticalGap (δ:ℂ)=((1-XR (y₀-δ)/xCritical:ℝ):ℂ) := by
  simp only [complexCriticalGap,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one]
  rw [←Complex.ofReal_sub,X_eq_ofReal_XR]

lemma CriticalFoldData.real_delta_coordinate (d : CriticalFoldData) :
    ∀ᶠ δ : ℝ in 𝓝 0, 0 < δ →
      d.D (((Real.sqrt (1-XR (y₀-δ)/xCritical)):ℝ):ℂ)=(δ:ℂ) := by
  have hrt : Tendsto (fun δ : ℝ => (δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto
  filter_upwards [hrt.eventually d.gap_factor,hrt.eventually d.left_inverse,
    eventually_lt_nhds y₀_pos] with δ hfac hleft hsmall hδ
  let e : ℝ := 1-XR (y₀-δ)/xCritical
  have hylt : y₀-δ < y₀ := by linarith
  have hXlt : XR (y₀-δ) < xCritical := XR_strictMonoOn (by exact hylt.le) (by simp) hylt
  have he : 0 < e := by
    dsimp [e]
    have hi := (div_lt_one critical_x_pos).mpr hXlt
    linarith
  have hδc : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hB : d.B (δ:ℂ)=((e/δ^2:ℝ):ℂ) := by
    rw [complexCriticalGap_ofReal] at hfac
    change (e:ℂ)=(δ:ℂ)^2*d.B (δ:ℂ) at hfac
    rw [Complex.ofReal_div,Complex.ofReal_pow]
    apply (eq_div_iff (pow_ne_zero 2 hδc)).2
    simpa only [mul_comm] using hfac.symm
  have hQ : (δ:ℂ)*Complex.sqrt (d.B (δ:ℂ))=((Real.sqrt e:ℝ):ℂ) := by
    rw [hB,Complex.sqrt_of_nonneg (by exact_mod_cast (div_nonneg he.le (sq_nonneg δ)))]
    simp only [Complex.ofReal_re]
    rw [←Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_div he.le,Real.sqrt_sq hδ.le]
    field_simp [hδ.ne']
  rw [←hQ]
  exact hleft
end WP.Analysis
namespace WP.Analysis
lemma inverseY_tendsto_critical_left : Tendsto inverseY (𝓝[<] xCritical) (𝓝 y₀) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let u : ℝ := y₀-ε/2
  have hu : u < y₀ := by dsimp [u];linarith
  have hXu : XR u < xCritical := XR_strictMonoOn (by exact hu.le) (by simp) hu
  let δ : ℝ := min ((xCritical-XR u)/2) (xCritical/2)
  have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hXu)) (half_pos critical_x_pos)
  have hnear0 : ∀ᶠ x : ℝ in 𝓝 xCritical, dist x xCritical < δ := Metric.ball_mem_nhds xCritical hδ
  have hnear : ∀ᶠ x : ℝ in 𝓝[<] xCritical, dist x xCritical < δ := hnear0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hnear] with x hx hdist
  have hxlt : x < xCritical := hx
  have hclose := abs_lt.mp (show |x-xCritical| < δ by simpa only [Real.dist_eq] using hdist)
  have hxpos : 0 < x := by have ht := min_le_right ((xCritical-XR u)/2) (xCritical/2);change δ ≤ xCritical/2 at ht;linarith
  have hxroot : XR u < x := by have ht := min_le_left ((xCritical-XR u)/2) (xCritical/2);change δ ≤ (xCritical-XR u)/2 at ht;linarith
  have hbranch := inverseY_branch x ⟨hxpos.le,hxlt⟩
  have hUY : u < inverseY x := by
    by_contra hn
    have ht := XR_strictMonoOn.monotoneOn hbranch.1.2.le hu.le (le_of_not_gt hn)
    rw [hbranch.2] at ht
    linarith
  rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hbranch.1.2)]
  dsimp [u] at hUY
  linarith
end WP.Analysis
namespace WP.Analysis
lemma critical_ray_tendsto :
    Tendsto (fun ε : ℝ => xCritical*(1-ε)) (𝓝[>] 0) (𝓝[<] xCritical) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun ε : ℝ => xCritical*(1-ε)) 0 := by fun_prop
    simpa only [sub_zero,mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change xCritical*(1-ε) < xCritical
    have he : 0 < ε := hε
    nlinarith [critical_x_pos]
lemma CriticalFoldData.inverseY_coordinate (d : CriticalFoldData) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      d.D (((Real.sqrt ε):ℝ):ℂ)=((y₀-inverseY (xCritical*(1-ε)):ℝ):ℂ) := by
  have hdt : Tendsto (fun ε : ℝ => y₀-inverseY (xCritical*(1-ε))) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa only [sub_self,Function.comp_def] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => y₀) (𝓝[>] 0) (𝓝 y₀)).sub
      (inverseY_tendsto_critical_left.comp critical_ray_tendsto)
  have hεlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hεlt,hdt.eventually d.real_delta_coordinate] with ε hε hεlt hd
  have hεp : 0 < ε := hε
  let x : ℝ := xCritical*(1-ε)
  have hx : x ∈ Ico (0:ℝ) xCritical := by
    dsimp [x]
    constructor
    · exact (mul_pos critical_x_pos (sub_pos.mpr hεlt)).le
    · nlinarith [critical_x_pos]
  have hb := inverseY_branch x hx
  let δ : ℝ := y₀-inverseY x
  have hδ : 0 < δ := sub_pos.mpr hb.1.2
  have he := hd hδ
  have harg : 1-XR (y₀-δ)/xCritical=ε := by
    rw [show y₀-δ=inverseY x by dsimp [δ];ring,hb.2]
    dsimp [x]
    field_simp [critical_x_pos.ne']
    <;> ring
  rw [harg] at he
  exact he

lemma CriticalFoldData.universalV_real_puiseux (d : CriticalFoldData) (P : PsiTheory) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      universalV P ((xCritical*(1-ε):ℝ):ℂ)=
        (d.c:ℂ)⁻¹*d.Ξ (((Real.sqrt ε):ℝ):ℂ)/(((Real.sqrt ε):ℝ):ℂ) := by
  have ht : Tendsto (fun ε : ℝ => ((Real.sqrt ε:ℝ):ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    have hc : ContinuousAt (fun ε : ℝ => ((Real.sqrt ε:ℝ):ℂ)) 0 := by fun_prop
    simpa only [Real.sqrt_zero,Complex.ofReal_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hεlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hεlt,d.inverseY_coordinate,ht.eventually d.residue_identity]
    with ε hε hεlt hd hres
  have hεp : 0 < ε := hε
  let x : ℝ := xCritical*(1-ε)
  have hx : x ∈ Ico (0:ℝ) xCritical := by
    dsimp [x]
    constructor
    · exact (mul_pos critical_x_pos (sub_pos.mpr hεlt)).le
    · nlinarith [critical_x_pos]
  have hs : (((Real.sqrt ε):ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hεp).ne'
  have hr := hres hs
  have hDY : (y₀:ℂ)-d.D (((Real.sqrt ε):ℝ):ℂ)=(inverseY x:ℂ) := by
    rw [hd]
    push_cast
    ring
  rw [hDY] at hr
  have hnorm : ‖(x:ℂ)‖ < xCritical := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2
  have hid := PositiveConvolution.planar_inverse_derivative_identity P (x:ℂ) hnorm
  rw [PositiveConvolution.planarInverse_ofReal P x hx] at hid
  have hne : deriv X (inverseY x:ℂ) ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hr
    exact zero_ne_one hr
  apply mul_left_cancel₀ hne
  exact hid.trans hr.symm
end WP.Analysis
namespace WP.Analysis
def criticalRootParameter (z : ℂ) : ℂ := Complex.sqrt (1-z/(xCritical:ℂ))
lemma critical_gap_re_pos (z : ℂ) (hz : ‖z‖ < xCritical) : 0 < (1-z/(xCritical:ℂ)).re := by
  have hr : z.re < xCritical := (Complex.re_le_norm z).trans_lt hz
  have hd : (z/(xCritical:ℂ)).re=z.re/xCritical := by
    simp only [div_eq_mul_inv,←Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [Complex.sub_re,Complex.one_re,hd]
  have ht := (div_lt_one critical_x_pos).mpr hr
  linarith
lemma criticalRootParameter_analytic (z : ℂ) (hz : ‖z‖ < xCritical) : AnalyticAt ℂ criticalRootParameter z := by
  have hw : AnalyticAt ℂ (fun w : ℂ => 1-w/(xCritical:ℂ)) z := by fun_prop
  have hs : AnalyticAt ℂ Complex.sqrt (1-z/(xCritical:ℂ)) :=
    complex_sqrt_analyticAt (z := (1-z/(xCritical:ℂ))) (Or.inl (critical_gap_re_pos z hz))
  exact AnalyticAt.comp (f := fun w : ℂ => 1-w/(xCritical:ℂ)) (x := z) hs hw
lemma criticalRootParameter_sq (z : ℂ) : (criticalRootParameter z)^2=1-z/(xCritical:ℂ) := complex_sqrt_sq _
lemma criticalRootParameter_ne_zero (z : ℂ) (hz : ‖z‖ < xCritical) : criticalRootParameter z ≠ 0 := by
  intro hn
  have hs := criticalRootParameter_sq z
  rw [hn,zero_pow (by norm_num : 2 ≠ 0)] at hs
  have hr := critical_gap_re_pos z hz
  rw [←hs] at hr
  norm_num at hr
lemma criticalRootParameter_norm_sq (z : ℂ) :
    ‖criticalRootParameter z‖^2=‖z-(xCritical:ℂ)‖/xCritical := by
  rw [←norm_pow,criticalRootParameter_sq]
  have hx : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  have he : 1-z/(xCritical:ℂ)=-(z-(xCritical:ℂ))/(xCritical:ℂ) := by field_simp [hx];ring
  rw [he,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos critical_x_pos]
lemma criticalRootParameter_small (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hz : ‖z-(xCritical:ℂ)‖ < xCritical*r^2) : ‖criticalRootParameter z‖ < r := by
  have hs := criticalRootParameter_norm_sq z
  have ht : ‖z-(xCritical:ℂ)‖/xCritical < r^2 := (div_lt_iff₀ critical_x_pos).mpr (by simpa only [mul_comm] using hz)
  nlinarith [norm_nonneg (criticalRootParameter z)]
lemma criticalRootParameter_real (x : ℝ) (hx : x < xCritical) :
    criticalRootParameter (x:ℂ)=((Real.sqrt (1-x/xCritical):ℝ):ℂ) := by
  have hp : 0 ≤ (1-x/xCritical:ℝ) := by have ht := (div_lt_one critical_x_pos).mpr hx;linarith
  unfold criticalRootParameter
  rw [show (1:ℂ)-(x:ℂ)/(xCritical:ℂ)=((1-x/xCritical:ℝ):ℂ) by push_cast;rfl]
  simpa only [Complex.ofReal_re] using (Complex.sqrt_of_nonneg (a := ((1-x/xCritical:ℝ):ℂ)) (by exact_mod_cast hp))
end WP.Analysis
namespace WP.Analysis
lemma CriticalFoldData.universalV_complex_puiseux (d : CriticalFoldData) (P : PsiTheory) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, ‖z‖ < xCritical → ‖z-(xCritical:ℂ)‖ < η →
      universalV P z=(d.c:ℂ)⁻¹*d.Ξ (criticalRootParameter z)/criticalRootParameter z := by
  have hxc := critical_x_pos
  have hrealEv : ∀ᶠ ε : ℝ in 𝓝 0, 0 < ε →
      universalV P ((xCritical*(1-ε):ℝ):ℂ)=
        (d.c:ℂ)⁻¹*d.Ξ (((Real.sqrt ε):ℝ):ℂ)/(((Real.sqrt ε):ℝ):ℂ) :=
    eventually_nhdsWithin_iff.mp (d.universalV_real_puiseux P)
  obtain ⟨ε₁,hε₁,hreal⟩ := Metric.eventually_nhds_iff.mp hrealEv
  obtain ⟨r,hr,hXi⟩ := Metric.eventually_nhds_iff.mp d.Xi_analytic.eventually_analyticAt
  let η : ℝ := min (xCritical/2) (min (xCritical*ε₁/2) (xCritical*r^2/4))
  have hη : 0 < η := lt_min (half_pos critical_x_pos)
    (lt_min (by positivity) (by positivity))
  have hηx : η ≤ xCritical/2 := min_le_left _ _
  have hηε : η ≤ xCritical*ε₁/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηr : η ≤ xCritical*r^2 := by
    have ht := (min_le_right (xCritical/2) (min (xCritical*ε₁/2) (xCritical*r^2/4))).trans (min_le_right _ _)
    change η ≤ xCritical*r^2/4 at ht
    have hp : 0 < xCritical*r^2 := by positivity
    linarith
  let Ω : Set ℂ := Metric.ball (xCritical:ℂ) η ∩ Metric.ball (0:ℂ) xCritical
  let F : ℂ → ℂ := fun z => (d.c:ℂ)⁻¹*d.Ξ (criticalRootParameter z)/criticalRootParameter z
  have hnorm (z : ℂ) (hz : z ∈ Ω) : ‖z‖ < xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right] using hz.2
  have hnear (z : ℂ) (hz : z ∈ Ω) : ‖z-(xCritical:ℂ)‖ < η := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hz.1
  have hF : AnalyticOnNhd ℂ F Ω := by
    intro z hz
    have hroot := criticalRootParameter_analytic z (hnorm z hz)
    have hsmall := criticalRootParameter_small z r hr ((hnear z hz).trans_le hηr)
    have hX := hXi (by simpa only [dist_zero_right] using hsmall)
    exact (analyticAt_const.mul (hX.comp hroot)).div hroot (criticalRootParameter_ne_zero z (hnorm z hz))
  have hV : AnalyticOnNhd ℂ (universalV P) Ω := by
    intro z hz
    change AnalyticAt ℂ (iteratedDeriv 3 (Phi P 0)) z
    simpa only [iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P 0 z (hnorm z hz)).iterated_deriv 3
  have hrealF (x : ℝ) (hx : x ∈ Ioo (xCritical-η) xCritical) : universalV P (x:ℂ)=F (x:ℂ) := by
    have hxpos : 0 < x := by linarith [hx.1]
    let ε : ℝ := 1-x/xCritical
    have hε : 0 < ε := by have ht := (div_lt_one critical_x_pos).mpr hx.2;dsimp [ε];linarith
    have hsmall : ε < ε₁ := by
      have ht : xCritical-x < η := by linarith [hx.1]
      have heq : ε=(xCritical-x)/xCritical := by dsimp [ε];field_simp [hxc.ne']
      rw [heq]
      apply (div_lt_iff₀ hxc).2
      nlinarith
    have he := hreal (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using hsmall) hε
    have hxε : xCritical*(1-ε)=x := by dsimp [ε];field_simp [critical_x_pos.ne'] <;> ring
    rw [hxε] at he
    dsimp [F]
    rw [criticalRootParameter_real x hx.2]
    exact he
  let x₀ : ℝ := xCritical-η/2
  have hx₀ : x₀ ∈ Ioo (xCritical-η) xCritical := by dsimp [x₀];constructor <;> linarith
  have hx₀p : 0 < x₀ := by dsimp [x₀];linarith
  have hmem : (x₀:ℂ) ∈ Ω := by
    constructor
    · rw [Metric.mem_ball,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_neg (by dsimp [x₀];linarith : x₀-xCritical < 0)]
      dsimp [x₀]
      linarith
    · rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx₀p]
      exact hx₀.2
  have hid : EqOn (universalV P) F Ω := by
    apply complex_identity_of_real_germ _ _ Ω x₀ hV hF
      (((convex_ball (xCritical:ℂ) η).inter (convex_ball (0:ℂ) xCritical)).isPreconnected) hmem
    filter_upwards [isOpen_Ioo.mem_nhds hx₀] with x hx
    exact hrealF x hx
  refine ⟨η,hη,?_⟩
  intro z hz hnearz
  exact hid ⟨by simpa only [Metric.mem_ball,dist_eq_norm] using hnearz,
    by simpa only [Metric.mem_ball,dist_zero_right] using hz⟩
end WP.Analysis
