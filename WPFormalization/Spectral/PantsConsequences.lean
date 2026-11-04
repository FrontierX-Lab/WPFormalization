import WPFormalization.Spectral.ManyEigenvaluesTransfer
import WPFormalization.RandomGeometry.PantsConcentration

/-! The exact consequent of Proposition 14.2: floor((1-epsilon)qL^2)-1
positive discrete eigenvalues at threshold 6L. This uses the actual
concentration producer, with no concentration or moment hypothesis. -/
noncomputable section
universe u v w z
namespace WP.Spectral
open Filter MeasureTheory WP.External WP.RandomGeometry
open scoped Topology

theorem pants_many_eigenvalues (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (S : SpectralGeometry H)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (L : ℕ → ℝ) (hLp : ∀ᶠ g in atTop, 0 < L g) (hL : Tendsto L atTop (𝓝 0))
    (hscale : Tendsto (fun g => pantsScale g (n g) * L g ^ 2) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X | ∃ ℓ, S.positiveEigenvalue X
          (Nat.floor ((1 - ε) * (pantsScale g (n g) * L g ^ 2)) - 1) = some ℓ ∧
        ℓ ≤ 6 * L g}) atTop (𝓝 1) := by
  let a : ℕ → ℝ := fun g => pantsScale g (n g) * L g ^ 2
  let j : ℕ → ℕ := fun g => Nat.floor ((1 - ε) * a g) - 1
  have hapos : ∀ᶠ g in atTop, 0 < a g := hscale.eventually_gt_atTop 0
  have hfloor2 : ∀ᶠ g in atTop, 2 ≤ Nat.floor ((1 - ε) * a g) := by
    have hh := (hscale.const_mul_atTop (show 0 < 1 - ε by linarith)).eventually_ge_atTop 2
    exact hh.mono fun _ h => Nat.le_floor h
  have htail := pants_concentration P G H T C MI n hn L hLp hL hscale ε hε
  have hprob := wpProbability_eventually_probability P G n
    ((fast_cusps_eventually_two n hn).mono fun _ h => by omega)
  change Tendsto (fun g => (wpProbability G g (n g)).real
    {X | ∃ ℓ, S.positiveEigenvalue X (j g) = some ℓ ∧ ℓ ≤ 6 * L g}) atTop (𝓝 1)
  apply probability_one_of_bad_event (fun g => wpProbability G g (n g)) hprob
    (fun g => {X | ∃ ℓ, S.positiveEigenvalue X (j g) = some ℓ ∧ ℓ ≤ 6 * L g})
    (fun g => {X | ε ≤ |(H.pantsCount X (L g) : ℝ) / a g - 1|})
    (fun g => S.measurable_le g (n g) (j g) (6 * L g)) htail
  have hshort : ∀ᶠ g in atTop, 6 * L g < 1 / 4 := by
    have hh := hL.const_mul 6
    norm_num only [mul_zero] at hh
    exact hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hapos,hfloor2,hLp,hshort,eventually_ge_atTop (2 : ℕ)]
    with g hag hfg hLg hsg hg
  intro X hX
  have hlt : |(H.pantsCount X (L g) : ℝ) / a g - 1| < ε := lt_of_not_ge hX
  have hlow : (1 - ε) * a g < (H.pantsCount X (L g) : ℝ) :=
    (lt_div_iff₀ hag).mp (by linarith [(abs_lt.mp hlt).1])
  have hfloor : Nat.floor ((1 - ε) * a g) < H.pantsCount X (L g) := by
    apply (Nat.floor_lt (mul_nonneg (by linarith) hag.le)).mpr
    exact hlow
  have hj1 : 1 ≤ j g := by dsimp [j]; omega
  have hcount : j g + 1 ≤ H.pantsCount X ((6 * L g) / 6) := by
    rw [show (6 * L g) / 6 = L g by ring]
    dsimp [j]
    omega
  exact S.many_pants g (n g) (by unfold Stable; omega) X (j g) (6 * L g)
    hj1 (mul_pos (by norm_num) hLg) hsg hcount

end WP.Spectral

namespace WP.RandomGeometry
open Filter MeasureTheory WP.External
open scoped Topology

@[blueprint "prop:pants-concentration"]
theorem short_pants_concentration (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (S : SpectralGeometry H)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (L : ℕ → ℝ) (hLp : ∀ᶠ g in atTop, 0 < L g) (hL : Tendsto L atTop (𝓝 0))
    (hscale : Tendsto (fun g => pantsScale g (n g) * L g ^ 2) atTop atTop) :
    (∀ η : ℝ, 0 < η → Tendsto (fun g => (wpProbability G g (n g)).real
      {X | η ≤ |(H.pantsCount X (L g) : ℝ) /
        (pantsScale g (n g) * L g ^ 2) - 1|}) atTop (𝓝 0)) ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ∃ ℓ, S.positiveEigenvalue X
            (Nat.floor ((1 - ε) * (pantsScale g (n g) * L g ^ 2)) - 1) = some ℓ ∧
          ℓ ≤ 6 * L g}) atTop (𝓝 1) := by
  exact ⟨pants_concentration P G H T C MI n hn L hLp hL hscale,
    fun ε hε => WP.Spectral.pants_many_eigenvalues P G H T C MI S n hn L hLp hL hscale ε hε.1 hε.2⟩

end WP.RandomGeometry
