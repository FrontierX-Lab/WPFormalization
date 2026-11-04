import WPFormalization.Analysis.KernelRoucheZeros
import WPFormalization.Analysis.KernelGrowth
import WPFormalization.External.Hadamard
noncomputable section
namespace WP
/- The full original Lemma2.1. The deformation zero classification is proved
from the actual characteristic integrals and real signs, with the generic
classical Rouche count. Actual square-root growth verifies the hypothesis of
the classical Hadamard genus-zero factorization. The fifth component alone
uses classical J0 complex-zero reality. No deformed-kernel result is assumed.
Blueprint label(s): lem:kernel-zeros
Paper v3: 2.1 [PDF16]
Status: CONDITIONALLY_PROVED (three precisely registered classical inputs)
-/
@[blueprint "lem:kernel-zeros"]
theorem kernel_zeros :
    (∀ y : ℝ, y ∈ Set.Ioc 0 (Real.pi^2/4) → 0 < XR y) ∧
    (∀ y : ℝ, y ∈ Set.Icc 0 (Real.pi^2/4) →
      (iteratedDeriv 2 X y).re < 0 ∧ 0 < (iteratedDeriv 3 X y).re) ∧
    y₀ < 3/2 ∧
    (∀ Y ∈ Set.Icc 0 y₀, XR Y ≤ Y) ∧
    (∀ z : ℂ, deriv X z = 0 → z.im = 0 ∧ 0 < z.re) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∃ roots : ℕ → ℝ,
      StrictMono roots ∧ (∀ j, 0 < roots j) ∧ roots 0 = r Y ∧
      (∀ z : ℂ, K Y z = 0 ↔ ∃ j, z = (roots j : ℂ)) ∧
      (∀ j, deriv (K Y) (roots j) ≠ 0) ∧
      (∀ z : ℂ, HasProd (fun j => 1 - z / (roots j : ℂ)) (K Y z / a Y)))  := by
  have hs := bessel_signs_pi_interval
  refine ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,derivX_zero_real_pos,?_⟩
  intro Y hY
  obtain ⟨q,hmono,hpos,hfirst,hall,hsimple⟩ := Analysis.K_ordered_simple_zeros Y hY
  refine ⟨q,hmono,hpos,hfirst,hall,hsimple,?_⟩
  have hzero:K Y 0≠0:=by
    rw [K_zero,derivX_ofReal]
    exact_mod_cast a_ne_zero Y hY
  have hinj:Function.Injective (fun j:ℕ=>(q j:ℂ)):=by
    intro i j he
    exact hmono.injective (Complex.ofReal_inj.mp he)
  have hprod:=External.hadamard_genus_zero_of_sqrt_growth (K Y) (K_differentiable Y) hzero
    (Real.exp (2*Real.sqrt Y)) 2 (Real.exp_pos _) (by norm_num)
    (Analysis.K_norm_growth Y hY.1) (fun j:ℕ=>(q j:ℂ)) hinj hall hsimple
  intro z
  simpa only [K_zero,derivX_ofReal] using hprod z

end WP
