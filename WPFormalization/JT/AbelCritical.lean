import WPFormalization.Analysis.CriticalParameterCoordinates

/-! The cubic critical edge of the actual K kernel.  The Abel-to-kernel
identity is supplied separately; every estimate here is a theorem of the
existing entire kernel, without an additional asymptotic input. -/
noncomputable section
namespace WP.JT
open WP.Analysis Filter Set Asymptotics
open scoped Topology

/-- The real trace of the actual critical kernel in the energy coordinate. -/
def criticalKernelTrace (q : ℝ) : ℝ :=
  (K (y₀ : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re

lemma criticalKernelTrace_analyticAt : AnalyticAt ℝ criticalKernelTrace 0 := by
  have ha : AnalyticAt ℝ (fun t : ℝ => (K (y₀ : ℂ) (t : ℂ)).re) 0 :=
    ((K_differentiable (y₀ : ℂ)).analyticAt 0).re_ofReal
  have ha' : AnalyticAt ℝ (fun t : ℝ => (K (y₀ : ℂ) (t : ℂ)).re) (-2 * Real.pi^2 * (0:ℝ)) := by
    simpa using ha
  exact ha'.comp (f := fun q : ℝ => -2 * Real.pi^2 * q)
    (analyticAt_const.mul analyticAt_id)

lemma criticalKernelTrace_zero : criticalKernelTrace 0 = 0 := by
  simp only [criticalKernelTrace, mul_zero, Complex.ofReal_zero, K_zero,
    derivX_y₀_zero, Complex.zero_re]

lemma criticalKernelTrace_hasDerivAt :
    HasDerivAt criticalKernelTrace (2 * Real.pi^2 * criticalB / 3) 0 := by
  have hk : deriv (K (y₀ : ℂ)) 0 = iteratedDeriv 2 X (y₀ : ℂ) / 3 := by
    have h := iteratedDeriv_K_zero (y₀ : ℂ) 1
    norm_num [oddFactorial, Finset.prod_range_succ] at h
    convert h using 1
    ring
  have hd₀ : HasDerivAt (fun t : ℝ => (K (y₀ : ℂ) (t : ℂ)).re)
      (deriv (K (y₀ : ℂ)) 0).re (-2 * Real.pi^2 * (0 : ℝ)) := by
    simpa using (K_differentiable (y₀ : ℂ) 0).hasDerivAt.real_of_complex
  have hd := hd₀.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul (-2 * Real.pi^2))
  rw [hk] at hd
  convert hd using 1
  · rfl
  · simp [criticalB]
    ring

lemma criticalKernelTrace_linear_error :
    (fun q => criticalKernelTrace q - (2 * Real.pi^2 * criticalB / 3) * q)
      =O[𝓝 (0 : ℝ)] (fun q => q^2) := by
  simpa only [criticalKernelTrace_zero, criticalKernelTrace_hasDerivAt.deriv, sub_zero]
    using analytic_first_order_error_at_zero criticalKernelTrace criticalKernelTrace_analyticAt

lemma rpow_three_halves (q : ℝ) (hq : 0 ≤ q) :
    Real.rpow q (3/2 : ℝ) = Real.sqrt q * q := by
  rw [Real.rpow_eq_pow, show (3/2 : ℝ) = 1/2 + 1 by norm_num,
    Real.rpow_add_of_nonneg hq (by norm_num) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.rpow_one]

lemma rpow_five_halves (q : ℝ) (hq : 0 ≤ q) :
    Real.rpow q (5/2 : ℝ) = Real.sqrt q * q^2 := by
  rw [Real.rpow_eq_pow, show (5/2 : ℝ) = 1/2 + 2 by norm_num,
    Real.rpow_add_of_nonneg hq (by norm_num) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.rpow_two]

/-- The exact critical coefficient and the full O(q^(5/2)) remainder,
with q approaching zero from positive energies. -/
lemma critical_kernel_density_isBigO :
    (fun q : ℝ =>
      Real.sqrt q / (2 * Real.pi) * (K (y₀ : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re -
        (Real.pi * criticalB / 3) * Real.rpow q (3/2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun q : ℝ => Real.rpow q (5/2 : ℝ)) := by
  have herr := criticalKernelTrace_linear_error.mono
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hm := ((isBigO_refl (fun q : ℝ => Real.sqrt q) (𝓝[>] (0 : ℝ))).mul herr).const_mul_left
    (1 / (2 * Real.pi))
  apply hm.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    rw [rpow_three_halves q (le_of_lt hq)]
    dsimp only [criticalKernelTrace]
    field_simp [Real.pi_ne_zero]
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (rpow_five_halves q (le_of_lt hq)).symm

/-- An explicit positive constant and radius for the critical edge error.
The zero-energy endpoint is included. -/
lemma critical_kernel_density_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ q ∈ Icc (0 : ℝ) δ,
      |Real.sqrt q / (2 * Real.pi) * (K (y₀ : ℂ) ((-2 * Real.pi^2 * q : ℝ) : ℂ)).re -
        (Real.pi * criticalB / 3) * Real.rpow q (3/2 : ℝ)| ≤
          C * Real.rpow q (5/2 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := critical_kernel_density_isBigO.exists_pos
  have he := hbound.bound
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C, ε/2, hC, by positivity, ?_⟩
  intro q hq
  by_cases hzero : q = 0
  · simp [hzero]
  · have hp : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hzero)
    have hd : dist q 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hp]
      linarith [hq.2]
    have hb := he hd hp
    simpa only [Real.norm_eq_abs, Real.rpow_eq_pow,
      abs_of_nonneg (Real.rpow_nonneg hq.1 (5/2:ℝ))] using hb

end WP.JT
