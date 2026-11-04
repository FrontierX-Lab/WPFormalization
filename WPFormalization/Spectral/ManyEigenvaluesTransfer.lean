import WPFormalization.Spectral.VanishingGap
import WPFormalization.Statements.Intensities

/-! The new deterministic/probabilistic transfer in Corollary 14.3.  The
original Proposition 14.2 is an explicit INTERNAL proof input here, not a
classical external interface.  The final paper corollary must instantiate
that input with the actual pants-concentration producer. -/
noncomputable section
universe u v w
namespace WP.Spectral
open Filter MeasureTheory WP.External
open scoped Topology

lemma pantsScale_pos (g n : ℕ) (hg : 1 ≤ g) (hn : 2 ≤ n) :
    0 < pantsScale g n := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlam : 0 < (n : ℝ) / g := div_pos (by linarith) hgR
  have hY := Analysis.densityY_spec ((n : ℝ) / g) hlam.le
  have hYpos : 0 < densityY ((n : ℝ) / g) := by
    by_contra h
    have hz : densityY ((n : ℝ) / g) = 0 := le_antisymm (not_lt.mp h) hY.1.1
    rw [hz, density_zero_value] at hY
    linarith [hY.2]
  have hx : 0 < XR (densityY ((n : ℝ) / g)) := by
    rw [← XR_zero]
    exact XR_strictMonoOn y₀_pos.le hY.1.2.le hYpos
  have hp : 0 < profileC ((n : ℝ) / g) := by
    rw [profileC, if_neg hlam.ne']
    exact div_pos (mul_pos hlam (sq_pos_of_pos Real.pi_pos)) hx
  unfold pantsScale
  exact div_pos (mul_pos (by linarith) (by linarith))
    (mul_pos (mul_pos (by norm_num) hgR) hp)

theorem many_eigenvalues_from_concentration (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (S : SpectralGeometry H) (n j : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (hj : Tendsto j atTop atTop)
    (hsmall : Tendsto (fun g => (j g : ℝ) / pantsScale g (n g)) atTop (𝓝 0))
    (hconcentration : ∀ L : ℕ → ℝ,
      (∀ᶠ g in atTop, 0 < L g) → Tendsto L atTop (𝓝 0) →
      Tendsto (fun g => pantsScale g (n g) * L g ^ 2) atTop atTop →
      ∀ ε : ℝ, 0 < ε → Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ε ≤ |(H.pantsCount X (L g) : ℝ) /
          (pantsScale g (n g) * L g ^ 2) - 1|}) atTop (𝓝 0)) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X | ∃ ℓ, S.positiveEigenvalue X (j g) = some ℓ ∧
        ℓ ≤ 12 * Real.sqrt ((j g : ℝ) / pantsScale g (n g))}) atTop (𝓝 1) := by
  let q := fun g => pantsScale g (n g)
  let L := fun g => 2 * Real.sqrt ((j g : ℝ) / q g)
  have hq : ∀ᶠ g in atTop, 0 < pantsScale g (n g) := by
    filter_upwards [fast_cusps_eventually_two n hn, eventually_ge_atTop 1] with g hng hg
    exact pantsScale_pos g (n g) hg hng
  have hj1 : ∀ᶠ g in atTop, 1 ≤ j g := hj.eventually (eventually_ge_atTop 1)
  have hL : Tendsto L atTop (𝓝 0) := many_eigenvalue_length_tendsto_zero j q hsmall
  have hLp : ∀ᶠ g in atTop, 0 < L g := by
    filter_upwards [hq, hj1] with g hqg hjg
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr
      (div_pos (by exact_mod_cast (show 0 < j g by omega)) hqg))
  have hscale : ∀ᶠ g in atTop, q g * L g ^ 2 = 4 * j g :=
    hq.mono fun g hg => many_eigenvalue_count_scale (j g) (q g) hg
  have hjreal : Tendsto (fun g => (j g : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hj
  have hscale_top : Tendsto (fun g => q g * L g ^ 2) atTop atTop :=
    (hjreal.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).congr' (hscale.mono fun _ h => h.symm)
  have htail := hconcentration L hLp hL hscale_top (1 / 2) (by norm_num)
  have htail' : Tendsto (fun g => (wpProbability G g (n g)).real
      {X | (1 / 2 : ℝ) ≤ |(H.pantsCount X (L g) : ℝ) / (4 * j g) - 1|})
      atTop (𝓝 0) := by
    apply htail.congr'
    filter_upwards [hscale] with g hg
    rw [show pantsScale g (n g) * L g ^ 2 = 4 * j g from hg]
  have hμ := wpProbability_eventually_probability P G n
    ((fast_cusps_eventually_two n hn).mono fun _ h => by omega)
  apply probability_one_of_relative_count (fun g => wpProbability G g (n g)) hμ
    (fun g X => H.pantsCount X (L g)) j _ (fun g => S.measurable_le g (n g) (j g) _)
    hj1 htail'
  have hε := hL.const_mul 6
  norm_num only [mul_zero] at hε
  filter_upwards [hj1, hLp, eventually_ge_atTop 2,
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with g hjg hLg hg hεg
  intro X hX
  have hlength : (6 * L g) / 6 = L g := by ring
  have hXX : j g + 1 ≤ H.pantsCount X ((6 * L g) / 6) := by simpa [hlength] using hX
  obtain ⟨ℓ, he, hb⟩ := S.many_pants g (n g) (by unfold Stable; omega) X (j g)
    (6 * L g) hjg (mul_pos (by norm_num) hLg) hεg hXX
  refine ⟨ℓ, he, hb.trans_eq ?_⟩
  dsimp [L, q]
  ring

end WP.Spectral
