import WPFormalization.Statements.Basic

/-! Probability transfer for the spectral applications.  The sample spaces may
vary with genus.  These lemmas do not supply any concentration estimate or
geometric spectral assertion; both are explicit hypotheses until instantiated
with the actual Weil--Petersson model. -/
noncomputable section
namespace WP.Spectral
open Filter MeasureTheory
open scoped Topology
universe u

theorem tendsto_one_of_liminf (p : ℕ → ℝ)
    (hlow : ∀ g, 0 ≤ p g) (hupp : ∀ᶠ g in atTop, p g ≤ 1)
    (hinf : 1 ≤ Filter.liminf p atTop) : Tendsto p atTop (𝓝 1) := by
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) p :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hlow)
  have habove : atTop.IsBoundedUnder (· ≤ ·) p :=
    isBoundedUnder_of_eventually_le hupp
  exact tendsto_of_le_liminf_of_limsup_le hinf
    (limsup_le_of_le hbelow.isCoboundedUnder_le hupp) habove hbelow

/-- The physical length chosen for the many-eigenvalue corollary tends to
zero whenever the requested index is little-o of the intensity. -/
theorem many_eigenvalue_length_tendsto_zero (j : ℕ → ℕ) (q : ℕ → ℝ)
    (hsmall : Tendsto (fun g => (j g : ℝ) / q g) atTop (𝓝 0)) :
    Tendsto (fun g => 2 * Real.sqrt ((j g : ℝ) / q g)) atTop (𝓝 0) := by
  simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hsmall).const_mul 2

theorem many_eigenvalue_count_scale (j : ℕ) (q : ℝ) (hq : 0 < q) :
    q * (2 * Real.sqrt ((j : ℝ) / q)) ^ 2 = 4 * j := by
  have hs : Real.sqrt ((j : ℝ) / q) ^ 2 = (j : ℝ) / q :=
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg j) hq.le)
  rw [mul_pow, hs]
  field_simp
  <;> ring

theorem probability_one_of_bad_event
    {Ω : ℕ → Type u} [∀ g, MeasurableSpace (Ω g)]
    (μ : ∀ g, Measure (Ω g))
    (hμ : ∀ᶠ g in atTop, IsProbabilityMeasure (μ g))
    (s t : ∀ g, Set (Ω g)) (hs : ∀ g, MeasurableSet (s g))
    (ht : Tendsto (fun g => (μ g).real (t g)) atTop (𝓝 0))
    (himp : ∀ᶠ g in atTop, ∀ X, X ∉ t g → X ∈ s g) :
    Tendsto (fun g => (μ g).real (s g)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun g => (μ g).real (s g)ᶜ) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun g => measureReal_nonneg)) _ ht
    filter_upwards [himp, hμ] with g hg hμg
    letI : IsProbabilityMeasure (μ g) := hμg
    exact measureReal_mono (fun X hX => by
      by_contra hbad
      exact hX (hg X hbad))
  have htend := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  have htend' : Tendsto (fun g => 1 - (μ g).real (s g)ᶜ) atTop (𝓝 1) := by
    simpa using htend
  apply htend'.congr'
  filter_upwards [hμ] with g hg
  letI : IsProbabilityMeasure (μ g) := hg
  rw [measureReal_compl (hs g), probReal_univ]
  ring

/-- The count level used in Corollary 14.3: concentration within one half at
the deterministic scale `4*j` forces at least `j+1` pants. -/
theorem count_ge_of_relative_error (N j : ℕ) (hj : 1 ≤ j)
    (herr : |(N : ℝ) / (4 * j) - 1| < (1 / 2 : ℝ)) : j + 1 ≤ N := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hlow := (abs_lt.mp herr).1
  have hdiv : (1 / 2 : ℝ) < (N : ℝ) / (4 * j) := by linarith
  have hN : (2 * j : ℕ) < N := by
    have := (lt_div_iff₀ (mul_pos (by norm_num) hjpos)).mp hdiv
    have hreal : 2 * (j : ℝ) < N := by linarith
    exact_mod_cast hreal
  omega

theorem probability_one_of_relative_count
    {Ω : ℕ → Type u} [∀ g, MeasurableSpace (Ω g)]
    (μ : ∀ g, Measure (Ω g))
    (hμ : ∀ᶠ g in atTop, IsProbabilityMeasure (μ g))
    (N : ∀ g, Ω g → ℕ) (j : ℕ → ℕ)
    (s : ∀ g, Set (Ω g)) (hs : ∀ g, MeasurableSet (s g))
    (hj : ∀ᶠ g in atTop, 1 ≤ j g)
    (hcount : Tendsto (fun g => (μ g).real
      {X | (1 / 2 : ℝ) ≤ |(N g X : ℝ) / (4 * j g) - 1|}) atTop (𝓝 0))
    (hgeometry : ∀ᶠ g in atTop, ∀ X, j g + 1 ≤ N g X → X ∈ s g) :
    Tendsto (fun g => (μ g).real (s g)) atTop (𝓝 1) := by
  apply probability_one_of_bad_event μ hμ s _ hs hcount
  filter_upwards [hj, hgeometry] with g hjg hgg
  intro X hX
  exact hgg X (count_ge_of_relative_error (N g X) (j g) hjg (lt_of_not_ge hX))

end WP.Spectral
