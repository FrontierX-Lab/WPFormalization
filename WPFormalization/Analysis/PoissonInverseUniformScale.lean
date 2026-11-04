import WPFormalization.Analysis.PoissonNormalizer
/-! The actual inverse Poisson normalizer has common scaled coefficient and remainder bounds for every real density bounded below by a fixed positive number. The coefficient series is the original inverse Stirling series, rescaled by the reciprocal density. Constants precede the density, h and truncation order; no extraction statement or paper-specific approximation is assumed. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma poissonInverse_uniform_scaled_data (m : ℝ) (hm : 0 < m) :
    ∃ C B c H M : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < H ∧ 0 < M ∧
      ∀ ψ : ℝ, m ≤ ψ →
        (∀ j : ℕ, |PowerSeries.coeff j (PowerSeries.rescale ψ⁻¹ (HigherOrder.poissonStirlingSeries⁻¹))| ≤
          C * B^j * (j.factorial : ℝ)^2) ∧
        ∀ h : ℝ, H ≤ h → |(poissonNormalizer (h*ψ))⁻¹| ≤ M ∧
          ∀ K : ℕ, (K : ℝ) ≤ c*h →
          |(poissonNormalizer (h*ψ))⁻¹ - inversePowerTruncation
            (PowerSeries.rescale ψ⁻¹ (HigherOrder.poissonStirlingSeries⁻¹)) K h| ≤
            C * B^(K+1) * ((K+1).factorial : ℝ)^2 / h^(K+1) := by
  obtain ⟨Cc,Bc,hCc,hBc,hcoeff⟩ := GevreyOneAsymptotic.coeff_bound
    (fun x => (poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one
  obtain ⟨Ce,Be,c,He,hCe,hBe,hc,hHe,herror⟩ := GevreyOneAsymptotic.uniform_above_linear_scale
    (fun x => (poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one m hm
  let C : ℝ := max Cc Ce
  let B : ℝ := max (Bc*m⁻¹) Be
  let H : ℝ := max He 1
  let M : ℝ := Ce*Be+1
  have hC : 0 < C := hCc.trans_le (le_max_left _ _)
  have hB : 0 < B := (mul_pos hBc (inv_pos.mpr hm)).trans_le (le_max_left _ _)
  have hH : 0 < H := hHe.trans_le (le_max_left _ _)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C,B,c,H,M,hC,hB,hc,hH,hM,?_⟩
  intro ψ hψ
  have hψpos : 0 < ψ := hm.trans_le hψ
  have ht : 0 ≤ ψ⁻¹ := inv_nonneg.mpr hψpos.le
  have htm : ψ⁻¹ ≤ m⁻¹ := inv_anti₀ hm hψ
  constructor
  · intro j
    rw [PowerSeries.coeff_rescale, abs_mul, abs_pow, abs_of_nonneg ht]
    have hfact1 : 1 ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
    have hfact : (j.factorial : ℝ) ≤ (j.factorial : ℝ)^2 := by nlinarith
    calc
      _ ≤ (m⁻¹)^j * (Cc * Bc^j * (j.factorial : ℝ)) :=
        mul_le_mul (pow_le_pow_left₀ ht htm _) (hcoeff j) (abs_nonneg _) (by positivity)
      _ = Cc * (Bc*m⁻¹)^j * (j.factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ C * B^j * (j.factorial : ℝ)^2 := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_left _ _
  · intro h hhH
    have hhE : He ≤ h := (le_max_left _ _).trans hhH
    have hh1 : 1 ≤ h := (le_max_right _ _).trans hhH
    have hh : 0 < h := zero_lt_one.trans_le hh1
    have hx : m*h ≤ h*ψ := by nlinarith [mul_le_mul_of_nonneg_left hψ hh.le]
    have hzero := herror 0 h (h*ψ) hhE hx (by simpa only [Nat.cast_zero] using (mul_pos hc hh).le)
    have hzero' : |(poissonNormalizer (h*ψ))⁻¹-1| ≤ Ce*Be/h := by
      simpa [inversePowerTruncation, PowerSeries.coeff_zero_eq_constantCoeff] using hzero
    refine ⟨?_,?_⟩
    · have hb : Ce*Be/h ≤ Ce*Be := div_le_self (by positivity) hh1
      have ht0 : |(poissonNormalizer (h*ψ))⁻¹| ≤ |(poissonNormalizer (h*ψ))⁻¹-1|+1 := by
        simpa only [sub_add_cancel,abs_one] using abs_add_le ((poissonNormalizer (h*ψ))⁻¹-1) 1
      dsimp [M]
      linarith only [hb,ht0,hzero']
    · intro K hK
      have hrescale : inversePowerTruncation
          (PowerSeries.rescale ψ⁻¹ (HigherOrder.poissonStirlingSeries⁻¹)) K h =
          inversePowerTruncation (HigherOrder.poissonStirlingSeries⁻¹) K (h*ψ) := by
        dsimp only [inversePowerTruncation]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [PowerSeries.coeff_rescale,mul_pow,div_eq_mul_inv,inv_pow,mul_inv_rev]
        ring
      rw [hrescale]
      apply (herror K h (h*ψ) hhE hx hK).trans
      have hfact1 : 1 ≤ ((K+1).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (K+1))
      have hfact : ((K+1).factorial : ℝ) ≤ ((K+1).factorial : ℝ)^2 := by nlinarith
      dsimp only [C,B]
      gcongr
      · exact le_max_right _ _
      · exact le_max_right _ _
end WP.Analysis
