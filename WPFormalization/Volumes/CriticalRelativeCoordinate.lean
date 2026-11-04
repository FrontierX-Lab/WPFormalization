import WPFormalization.Volumes.CriticalPuiseux
import WPFormalization.Analysis.GammaRatioBernoulli
/-! A constructive joint relative inverse of the genuine critical X fold.
For any analytic angle unit L, the inverse delta-coordinate is delta times
a function jointly analytic in delta and standardized angle, including delta=0. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalFoldData.joint_relative_inverse (d : CriticalFoldData)
    (L : ℂ → ℂ) (hL : AnalyticAt ℂ L 0) :
    ∃ q : ℂ × ℂ → ℂ, AnalyticAt ℂ q (0,0) ∧ q (0,0)=1 ∧
      (∀ᶠ δ : ℂ in 𝓝 0, q (δ,0)=1) ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0),
        X ((y₀:ℂ)-p.1*q p)=X ((y₀:ℂ)-p.1)*Complex.exp (Complex.I*p.2*p.1^2*L p.1) := by
  obtain ⟨G,hG,hG0,hDf⟩ := complex_analytic_linear_factor d.D d.D_analytic d.D_zero
  have hGzero : G 0=(((Real.sqrt d.b)⁻¹:ℝ):ℂ) := hG0.trans d.D_deriv
  have hLp : AnalyticAt ℂ (fun p : ℂ × ℂ => L p.1) (0,0) :=
    AnalyticAt.comp (f := Prod.fst) (x := ((0,0):ℂ × ℂ)) hL analyticAt_fst
  have hBp : AnalyticAt ℂ (fun p : ℂ × ℂ => d.B p.1) (0,0) :=
    AnalyticAt.comp (f := Prod.fst) (x := ((0,0):ℂ × ℂ)) d.B_analytic analyticAt_fst
  let Z : ℂ × ℂ → ℂ := fun p => Complex.I*p.2*p.1^2*L p.1
  let H : ℂ × ℂ → ℂ := fun p => d.B p.1-
    (X ((y₀:ℂ)-p.1)/(xCritical:ℂ))*(Complex.I*p.2*L p.1)*complexExpUnit (Z p)
  have hZ : AnalyticAt ℂ Z (0,0) := by
    dsimp only [Z]
    exact ((analyticAt_const.mul analyticAt_snd).mul (analyticAt_fst.pow 2)).mul hLp
  have hZ0 : Z (0,0)=0 := by simp [Z]
  have hH : AnalyticAt ℂ H (0,0) := by
    have hX : AnalyticAt ℂ (fun p : ℂ × ℂ => X ((y₀:ℂ)-p.1)/(xCritical:ℂ)) (0,0) :=
      ((X_differentiable.analyticAt _).comp (analyticAt_const.sub analyticAt_fst)).div_const
    have hE : AnalyticAt ℂ (fun p => complexExpUnit (Z p)) (0,0) :=
      (complexExpUnit_analytic (Z (0,0))).comp hZ
    exact hBp.sub
      ((hX.mul ((analyticAt_const.mul analyticAt_snd).mul hLp)).mul hE)
  have hH0 : H (0,0)=(d.b:ℂ) := by simp [H,d.B_zero]
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ => Complex.sqrt (H p)) (0,0) := by
    have hs : AnalyticAt ℂ Complex.sqrt (H (0,0)) :=
      complex_sqrt_analyticAt (by rw [hH0];exact Or.inl d.b_pos)
    exact hs.comp hH
  let T : ℂ × ℂ → ℂ := fun p => p.1*Complex.sqrt (H p)
  have hT : AnalyticAt ℂ T (0,0) := analyticAt_fst.mul hS
  have hT0 : T (0,0)=0 := by simp [T]
  let q : ℂ × ℂ → ℂ := fun p => Complex.sqrt (H p)*G (T p)
  have hq : AnalyticAt ℂ q (0,0) :=
    hS.mul ((by simpa only [hT0] using hG : AnalyticAt ℂ G (T (0,0))).comp hT)
  have hq0 : q (0,0)=1 := by
    dsimp only [q]
    rw [hT0,hH0,hGzero]
    have hs : Complex.sqrt (d.b:ℂ)=((Real.sqrt d.b:ℝ):ℂ) := by
      simpa only [Complex.ofReal_re] using (Complex.sqrt_of_nonneg (a := (d.b:ℂ)) (by exact_mod_cast d.b_pos.le))
    rw [hs,Complex.ofReal_inv]
    exact mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr d.b_pos).ne')
  have hTt : Tendsto T (𝓝 ((0,0):ℂ × ℂ)) (𝓝 (0:ℂ)) := by simpa only [hT0] using hT.continuousAt.tendsto
  have hfst : Tendsto (Prod.fst : ℂ × ℂ → ℂ) (𝓝 (0,0)) (𝓝 (0:ℂ)) := continuous_fst.continuousAt.tendsto
  have hqD : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), d.D (T p)=p.1*q p := by
    filter_upwards [hTt.eventually hDf] with p hp
    rw [hp]
    dsimp only [T,q]
    ring
  have haxis : ∀ᶠ δ : ℂ in 𝓝 0, q (δ,0)=1 := by
    have htc : ContinuousAt (fun δ : ℂ => (δ,(0:ℂ))) 0 := by fun_prop
    have ht : Tendsto (fun δ : ℂ => (δ,(0:ℂ))) (𝓝 0) (𝓝 (0,0)) := htc.tendsto
    filter_upwards [d.left_inverse,ht.eventually hqD] with δ hleft he
    by_cases hδ : δ=0
    · subst δ
      exact hq0
    have hTa : T (δ,0)=δ*Complex.sqrt (d.B δ) := by simp [T,H]
    rw [hTa,hleft] at he
    apply mul_left_cancel₀ hδ
    simpa only [mul_one] using he.symm
  refine ⟨q,hq,hq0,haxis,?_⟩
  filter_upwards [hfst.eventually d.gap_factor,hTt.eventually d.fold_identity,hqD] with p hgap hfold hqp
  rw [hqp] at hfold
  apply hfold.trans
  have hTsq : (T p)^2=p.1^2*H p := by dsimp only [T];rw [mul_pow,complex_sqrt_sq]
  rw [hTsq]
  have hxcn : (xCritical:ℂ) ≠ 0 := by exact_mod_cast critical_x_pos.ne'
  dsimp only [complexCriticalGap] at hgap
  field_simp [hxcn] at hgap
  have he := complexExpUnit_mul_arg (Z p)
  dsimp only [H]
  field_simp [hxcn]
  dsimp only [Z] at he ⊢
  have harg : Complex.I*p.2*p.1^2*L p.1=p.1^2*Complex.I*p.2*L p.1 := by ring
  rw [harg] at he ⊢
  linear_combination hgap + X ((y₀:ℂ)-p.1)*he
end WP.Analysis
