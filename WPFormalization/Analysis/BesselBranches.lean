import WPFormalization.Analysis.BesselBounds
import WPFormalization.Analysis.CriticalBesselData
import WPFormalization.Analysis.BesselDictionary
/-! The actual inverse branch on the full interval below the first Bessel zero.
The negative axis is handled by nonnegative series coefficients, the positive
axis by the zero-free interval. Strict monotonicity identifies the infimum
inverse with the intermediate-value branch. -/
noncomputable section
namespace WP
open Filter Set
open scoped Topology
lemma a_one_le_of_nonpos (y : ℝ) (hy : y ≤ 0) : 1 ≤ a y := by
  have hn (n : ℕ) : 0 ≤ (-1:ℝ)^n*y^n/(n.factorial:ℝ)^2 := by
    have he : (-1:ℝ)^n*y^n = (-y)^n := by rw [← mul_pow]; congr 1; ring
    rw [he]
    exact div_nonneg (pow_nonneg (neg_nonneg.mpr hy) n) (sq_nonneg _)
  have hs := derivX_hasSum_real y
  have hb := hs.summable.le_tsum 0 (fun n _ => hn n)
  rw [hs.tsum_eq] at hb
  simpa using hb
lemma a_pos_before_y₀ (y : ℝ) (hy : y < y₀) : 0 < a y := by
  by_cases h : 0 ≤ y
  · exact a_pos y ⟨h,hy⟩
  · exact lt_of_lt_of_le zero_lt_one (a_one_le_of_nonpos y (le_of_not_ge h))
lemma XR_hasDerivAt (y : ℝ) : HasDerivAt XR (a y) y :=
  (X_differentiable (y:ℂ)).hasDerivAt.real_of_complex
lemma XR_continuous : Continuous XR :=
  Complex.continuous_re.comp (X_differentiable.continuous.comp Complex.continuous_ofReal)
lemma XR_zero : XR 0 = 0 := by simp [XR,X]
lemma XR_strictMonoOn : StrictMonoOn XR (Iic y₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic y₀) XR_continuous.continuousOn
  intro y hy
  rw [(XR_hasDerivAt y).deriv]
  exact a_pos_before_y₀ y (by simpa only [interior_Iic,mem_Iio] using hy)
lemma inverseY_branch (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    inverseY x ∈ Ico 0 y₀ ∧ XR (inverseY x) = x := by
  obtain ⟨u,hu,hux⟩ := intermediate_value_Icc y₀_pos.le XR_continuous.continuousOn
    (show x ∈ Icc (XR 0) (XR y₀) from ⟨by rw [XR_zero];exact hx.1,hx.2.le⟩)
  have hult : u < y₀ := lt_of_le_of_ne hu.2 (by
    intro he
    rw [he] at hux
    exact (ne_of_lt hx.2) hux.symm)
  have hset : {y : ℝ | y ≤ y₀ ∧ XR y = x} = {u} := by
    ext y
    constructor
    · intro hy
      have he : y = u := XR_strictMonoOn.injOn hy.1 hu.2 (hy.2.trans hux.symm)
      simpa only [mem_singleton_iff] using he
    · intro hy
      have he : y = u := mem_singleton_iff.mp hy
      subst y
      exact ⟨hu.2,hux⟩
  have hi : inverseY x = u := by unfold inverseY;rw [hset,csInf_singleton]
  rw [hi]
  exact ⟨⟨hu.1,hult⟩,hux⟩
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: VERIFIED (actual series, alternating bounds and inverse branch)
-/
@[blueprint "def:bessel"]
theorem bessel_branches :
    Differentiable ℂ X ∧ 0 < y₀ ∧ y₀ < 3/2 ∧ deriv X y₀ = 0 ∧
    (∀ y ∈ Ico 0 y₀, 0 < a y) ∧
    (∀ x ∈ Ico 0 xCritical, inverseY x ∈ Ico 0 y₀ ∧ XR (inverseY x) = x) := by
  exact ⟨X_differentiable,y₀_pos,y₀_lt_three_halves,derivX_y₀_zero,a_pos,inverseY_branch⟩
end WP
