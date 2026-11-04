import WPFormalization.External.ShenWuPants
import WPFormalization.Statements.VolumeRatios
import WPFormalization.Geometry.Bridge
import WPFormalization.Marked.ShiftedTransport
import WPFormalization.Spectral.ProbabilityTransfer

/-! The new step in Corollary 1.6 is the all-density volume-ratio limit.
The lower-probability bound and deterministic spectral theory are the precise
published classical interfaces.  All objects retain the same explicit G,H.
-/
noncomputable section
universe u v w
namespace WP.Spectral
open Filter MeasureTheory WP.External
open scoped Topology

lemma spectral_cusp_volume_pos (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n) : 0 < cuspVolume G g n := by
  have hs : Stable g n := by unfold Stable; omega
  rw [Geometry.cuspVolume_eq_volumeModel P G g n hs]
  unfold volumeModel mixedBracket
  exact mul_pos (by positivity)
    (shifted_zero_pos P g n hn hs 0 ⟨le_rfl, y₀_pos⟩)

lemma fast_cusps_eventually_two (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop) :
    ∀ᶠ g in atTop, 2 ≤ n g := by
  filter_upwards [eventually_ge_atTop 1,
    hn.eventually (eventually_gt_atTop (2 : ℝ))] with g hg hfast
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hr : (1 : ℝ) ≤ Real.sqrt g := by simpa using Real.sqrt_le_sqrt hgR
  have ht := (lt_div_iff₀ (by linarith : (0 : ℝ) < Real.sqrt g)).mp hfast
  have hnr : (2 : ℝ) < n g := by linarith
  exact_mod_cast (show (2 : ℝ) ≤ n g by linarith)

lemma shenWuLength_tendsto_zero (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop) :
    Tendsto (shenWuLength n) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp hn
  have hi' : Tendsto (fun g : ℕ => Real.sqrt g / (n g : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using hi
  change Tendsto (fun g : ℕ => Real.sqrt (Real.sqrt g / (n g : ℝ))) atTop (𝓝 0)
  simpa only [Real.sqrt_zero, Function.comp_def] using
    (Real.continuous_sqrt.tendsto 0).comp hi'

lemma geometric_discrete_ratio_tendsto_one (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 2 ≤ n g) :
    Tendsto (fun g => cuspVolume G g (n g - 1)^2 /
      (cuspVolume G g (n g) * cuspVolume G g (n g - 2))) atTop (𝓝 1) := by
  obtain ⟨C, hC, g₀, hratio⟩ := volume_ratios P
  have hbound : Tendsto (fun g : ℕ => C / (g : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hz : Tendsto (fun g => |cuspVolume G g (n g - 1)^2 /
      (cuspVolume G g (n g) * cuspVolume G g (n g - 2)) - 1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun g => abs_nonneg _)) _ hbound
    filter_upwards [hn, eventually_ge_atTop g₀, eventually_ge_atTop 2] with g hng hg hg2
    have hs (m : ℕ) : Stable g m := by unfold Stable; omega
    rw [Geometry.cuspVolume_eq_volumeModel P G _ _ (hs _),
      Geometry.cuspVolume_eq_volumeModel P G _ _ (hs _),
      Geometry.cuspVolume_eq_volumeModel P G _ _ (hs _)]
    have he : n g - 1 + 1 = n g := by omega
    have he' : n g - 1 - 1 = n g - 2 := by omega
    simpa [he, he', mul_comm] using (hratio g hg).2 (n g - 1) (by omega)
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa [Real.norm_eq_abs] using hz)

lemma wpProbability_eventually_probability (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 1 ≤ n g) :
    ∀ᶠ g in atTop, IsProbabilityMeasure (wpProbability G g (n g)) := by
  filter_upwards [hn, eventually_ge_atTop 2] with g hng hg
  apply wpProbability_isProbabilityMeasure G g (n g) (by unfold Stable; omega)
  intro he
  have hv := spectral_cusp_volume_pos P G g (n g) hg hng
  simp [cuspVolume, wpVolume, he] at hv

/- Corollary 1.6, with the actual normalized WP measure and positive discrete
eigenvalues on the same explicit geometric family. -/
@[blueprint "cor:spectral"]
theorem vanishing_spectral_gap (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (S : SpectralGeometry H)
    (SW : ShenWuPantsBound H) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ∃ ℓ, S.positiveEigenvalue X 1 = some ℓ ∧ ℓ < ε}) atTop (𝓝 1) := by
  have hn2 := fast_cusps_eventually_two n hn
  have hμ := wpProbability_eventually_probability P G n (hn2.mono fun _ h => by omega)
  let A := fun g => {X : G.Moduli g (n g) (fun _ => 0) |
    1 ≤ H.pantsCount X (shenWuLength n g)}
  have hratio := geometric_discrete_ratio_tendsto_one P G n hn2
  have hprob : Tendsto (fun g => (wpProbability G g (n g)).real (A g)) atTop (𝓝 1) := by
    apply tendsto_one_of_liminf _ (fun _ => measureReal_nonneg)
    · filter_upwards [hμ] with g hg
      letI := hg
      simpa only [probReal_univ] using
        (measureReal_mono (μ := wpProbability G g (n g)) (Set.subset_univ (A g)))
    · simpa [hratio.liminf_eq] using SW.probability_liminf n hn
  obtain ⟨c, hc, hsingle⟩ := S.single_pant
  have hL := shenWuLength_tendsto_zero n hn
  have hcL : Tendsto (fun g => c * shenWuLength n g) atTop (𝓝 0) := by
    simpa using hL.const_mul c
  intro ε hε
  apply hprob.squeeze' tendsto_const_nhds
  · filter_upwards [hμ, eventually_ge_atTop 2, hn2,
      hL.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hcL.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)),
      hcL.eventually (gt_mem_nhds hε)] with g hμg hg hng hL1 hL4 hLε
    letI := hμg
    apply measureReal_mono (μ := wpProbability G g (n g)) _ (measure_ne_top _ _)
    intro X hX
    have hgp : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
    have hnp : (0 : ℝ) < n g := by exact_mod_cast (show 0 < n g by omega)
    have hLp : 0 < shenWuLength n g :=
      Real.sqrt_pos.mpr (div_pos (Real.sqrt_pos.mpr hgp) hnp)
    obtain ⟨ℓ, he, hle⟩ := hsingle g (n g) hg X (shenWuLength n g) hLp hL1.le hL4 hX
    exact ⟨ℓ, he, hle.trans_lt hLε⟩
  · filter_upwards [hμ] with g hg
    letI := hg
    simpa only [probReal_univ] using
      (measureReal_mono (μ := wpProbability G g (n g)) (Set.subset_univ
        {X | ∃ ℓ, S.positiveEigenvalue X 1 = some ℓ ∧ ℓ < ε}))

end WP.Spectral
