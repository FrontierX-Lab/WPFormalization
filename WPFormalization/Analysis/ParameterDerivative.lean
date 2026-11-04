import WPFormalization.Analysis.ParameterTaylor

/-! Joint continuity of derivatives in a continuous family of entire functions.
The Cauchy coefficient formula for translated functions supplies the proof. -/
noncomputable section
namespace WP.Analysis
open Set
lemma parameter_derivative_joint_continuous {P :  Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (F : P → ℂ → ℂ) (hDiff:∀ p,Differentiable ℂ (F p))
    (hF : Continuous (fun p : P × ℂ => F p.1 p.2)) :
    Continuous (fun p : P × ℂ => deriv (F p.1) p.2) := by
  let G : (P × ℂ) → ℂ → ℂ:=fun p z => F p.1 (p.2+z)
  have hGDiff (p : P × ℂ):DifferentiableOn ℂ (G p) (Metric.closedBall 0 1) :=
    ((hDiff _).comp (by fun_prop)).differentiableOn
  have hG : Continuous (fun p : (P × ℂ) × Metric.closedBall (0:ℂ) 1 => G p.1 p.2) := by
    have hmap : Continuous (fun p : (P × ℂ) × Metric.closedBall (0:ℂ) 1 =>
      (p.1.1,p.1.2+(p.2:ℂ))) := by fun_prop
    exact hF.comp hmap
  have hc:=parameter_coeff_continuous G 1 (by norm_num) hGDiff hG 1
  have he:(fun p : P × ℂ => WP.coeff (G p) 1)=fun p : P × ℂ => deriv (F p.1) p.2 := by
    funext p
    have hd:=(hDiff p.1 (p.2+0)).hasDerivAt.comp 0 ((hasDerivAt_id (0:ℂ)).const_add p.2)
    simp only [add_zero,mul_one] at hd
    change HasDerivAt (G p) (deriv (F p.1) p.2) 0 at hd
    simp only [WP.coeff,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,div_one]
    exact hd.deriv
  rwa [he] at hc
end WP.Analysis
