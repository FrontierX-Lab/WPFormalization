import WPFormalization.Analysis.WPInstantonResidue
import WPFormalization.Coefficients.InstantonNormalization

/-! Exact ordinary-WP instanton dictionary, §13.7. The actual action is entire,
its circular residue has the original coefficient normalization, and the
stationary points of the `dw/w` exponent are exactly the trigonometric saddle.
This does not assert the physics contour prediction for actual WP volumes. -/
noncomputable section
namespace WP.Coefficients
open WP.Analysis Set Filter
open scoped Topology

lemma instanton_degree_identity (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    3 * complexity g 1 = 2*k + 2*(3*g-2-k) + 1 := by
  unfold complexity
  omega

theorem instanton_residue_coefficient (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    (Real.Gamma (complexity g 1) : ℂ) *
        residueAtZero (instantonIntegrand (complexity g 1) k) =
      (Real.Gamma (complexity g 1) * (3/2 : ℝ)^(complexity g 1) *
        (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) : ℝ) := by
  rw [instanton_residue _ _ _ (instanton_degree_identity g k hg hk)]
  push_cast
  ring

/-- The literal residue identity, including the factor two and the exact
degree-dependent normalization `4^(-k)`. -/
theorem instanton_residue_normalization (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    (Real.Gamma (complexity g 1) : ℂ) *
        residueAtZero (instantonIntegrand (complexity g 1) k) =
      (2 * (4 : ℝ)^(-(k : ℤ)) * oneBoundaryBracketModel g k : ℝ) := by
  rw [instanton_residue_coefficient g k hg hk,
    instanton_coefficient_normalization g k hg hk]

/-- The same residue value is attained by every sufficiently small positive
circle, so the residue theorem is not merely an identification of a selected
limit or a formal coefficient by definition. -/
theorem instanton_small_circle_normalization (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ),
      (Real.Gamma (complexity g 1) : ℂ) *
        normalizedCircleIntegral (instantonIntegrand (complexity g 1) k) R =
      (2 * (4 : ℝ)^(-(k : ℤ)) * oneBoundaryBracketModel g k : ℝ) := by
  filter_upwards [instanton_normalizedCircleIntegral _ _ _
    (instanton_degree_identity g k hg hk)] with R hR
  rw [hR]
  have hn := instanton_residue_normalization g k hg hk
  rw [instanton_residue _ _ _ (instanton_degree_identity g k hg hk)] at hn
  exact hn

theorem instanton_stationary_unique (g k : ℕ) (hg : 1 ≤ g) (hk : k < 3*g-2)
    (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    deriv (instantonSaddleExponent g k) (t / (2 * Real.pi)) = 0 ↔ t = trigSaddle g k := by
  rw [instanton_stationary_iff_trig g k hg t ht]
  have hs := trig_saddle_spec g k hg hk
  constructor
  · intro he
    exact hs.2.2 t ht he
  · intro he
    subst t
    exact hs.2.1

/- Full original exact dictionary. Analytic identities hold on the whole
complex plane; the stationary equivalence is restricted to the original
positive real saddle interval and admissible integer degrees. -/
@[blueprint "eq:instanton-correspondence"]
theorem instanton_correspondence :
    Differentiable ℂ instantonAction ∧
    (∀ w : ℂ, instantonAction w =
      (2/3 : ℂ) * w^3 * H 0 (2 * (Real.pi : ℂ)^2 * w^2)) ∧
    (∀ g k : ℕ, 1 ≤ g → k ≤ 3*g-2 →
      ((Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k) =
        (Real.Gamma (complexity g 1) * (3/2 : ℝ)^(complexity g 1) *
          (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) : ℝ)) ∧
      ((Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k) =
        (2 * (4 : ℝ)^(-(k : ℤ)) * oneBoundaryBracketModel g k : ℝ))) ∧
    (∀ w : ℂ, instantonAction w ≠ 0 →
      w * deriv instantonAction w / instantonAction w =
        (2 * Real.pi * w)^2 * Complex.sin (2 * Real.pi * w) /
          (Complex.sin (2 * Real.pi * w) -
            2 * Real.pi * w * Complex.cos (2 * Real.pi * w))) ∧
    (∀ g k : ℕ, 1 ≤ g → k < 3*g-2 → ∀ t ∈ Ioo 0 Real.pi,
      deriv (instantonSaddleExponent g k) (t / (2 * Real.pi)) = 0 ↔
        t = trigSaddle g k) :=
  ⟨instantonAction_entire, instantonAction_eq_H,
    fun g k hg hk => ⟨instanton_residue_coefficient g k hg hk,
      instanton_residue_normalization g k hg hk⟩,
    instantonAction_log_derivative, instanton_stationary_unique⟩

end WP.Coefficients
