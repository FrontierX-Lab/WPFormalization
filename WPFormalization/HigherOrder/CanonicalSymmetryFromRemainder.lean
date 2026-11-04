import WPFormalization.HigherOrder.AsymptoticUniqueness
import WPFormalization.Statements.RecursiveRemainderTarget
import WPFormalization.Marked.QuadraticProfile
import WPFormalization.Marked.LogGrowth
import WPFormalization.Analysis.ComplexGermGluing
import WPFormalization.HigherOrder.ComplexTriangular
/-! Actual asymptotic uniqueness implies permutation symmetry of the prescribed jets.
The explicit uniform remainder hypothesis is a still-unproved paper goal, not a licensed external assumption. -/

noncomputable section
namespace WP.HigherOrder
open Filter Set PowerSeries
open scoped Topology

lemma profile_has_canonical_expansion_of_recursiveRemainder (P : PsiTheory)
    (hr : UniformRecursiveRemainderTarget P) (d : List ℕ) (hd : 1 ≤ d.length)
    (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    HasInversePowerExpansion (fun g => profile P g d Y)
      (fun g => (complexity g d.length : ℝ)) (profileCoefficient P Y d) := by
  obtain ⟨C, B, M, hC, hB, hM, hprofile, hscalar⟩ := hr
  intro K
  let D : ℝ := C * B ^ (K + 1) * profileOrderWeight (M : ℝ) (K + 1) d ^ (2 * (K + 1))
  have hdR : (0 : ℝ) < d.length := by exact_mod_cast (show 0 < d.length by omega)
  have hD : 0 < D := by dsimp [D, profileOrderWeight]; positivity
  refine ⟨D, hD, 2, ?_⟩
  intro g hg
  have hs : Stable g d.length := by unfold Stable; omega
  have hhN : 1 ≤ complexity g d.length := by unfold complexity; omega
  have hh : (0 : ℝ) < complexity g d.length := by exact_mod_cast (show 0 < complexity g d.length by omega)
  exact ⟨hh, hprofile g d hd hs hhN (K + 1) (by omega) Y hY⟩

lemma scalar_has_canonical_expansions_of_recursiveRemainder (P : PsiTheory)
    (hr : UniformRecursiveRemainderTarget P) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    HasInversePowerExpansion (fun g => cuspCorrection P g p Y)
      (fun g => (complexity g p : ℝ)) (cuspCoefficient P Y p) ∧
    HasInversePowerExpansion (fun g => genusCorrection P g p Y)
      (fun g => (complexity g p : ℝ)) (genusCoefficient P Y p) := by
  obtain ⟨C, B, M, hC, hB, hM, hprofile, hscalar⟩ := hr
  have hstep (K : ℕ) : ∃ D : ℝ, 0 < D ∧ ∃ G : ℕ, ∀ g ≥ G,
      0 < (complexity g p : ℝ) ∧
      |cuspCorrection P g p Y - ∑ j ∈ Finset.range (K + 1), cuspCoefficient P Y p j / (complexity g p : ℝ) ^ j| +
      |genusCorrection P g p Y - ∑ j ∈ Finset.range (K + 1), genusCoefficient P Y p j / (complexity g p : ℝ) ^ j| ≤
        D / (complexity g p : ℝ) ^ (K + 1) := by
    let D : ℝ := C * B ^ (K + 1) * scalarOrderWeight (M : ℝ) (K + 1) p ^ (2 * (K + 1))
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    refine ⟨D, by dsimp [D, scalarOrderWeight]; positivity, 2, ?_⟩
    intro g hg
    have hs : Stable g p := by unfold Stable; omega
    have hhN : 1 ≤ complexity g p := by unfold complexity; omega
    have hh : (0 : ℝ) < complexity g p := by exact_mod_cast (show 0 < complexity g p by omega)
    exact ⟨hh, hscalar g p hp hs hhN (K + 1) (by omega) Y hY⟩
  constructor
  · intro K
    obtain ⟨D, hD, G, hG⟩ := hstep K
    refine ⟨D, hD, G, ?_⟩
    intro g hg
    exact ⟨(hG g hg).1, (le_add_of_nonneg_right (abs_nonneg _)).trans (hG g hg).2⟩
  · intro K
    obtain ⟨D, hD, G, hG⟩ := hstep K
    refine ⟨D, hD, G, ?_⟩
    intro g hg
    exact ⟨(hG g hg).1, (le_add_of_nonneg_left (abs_nonneg _)).trans (hG g hg).2⟩

lemma profileCoefficient_perm_of_recursiveRemainder (P : PsiTheory)
    (hr : UniformRecursiveRemainderTarget P) {d e : List ℕ} (hde : d.Perm e)
    (hd : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    profileCoefficient P Y d = profileCoefficient P Y e := by
  have ha := profile_has_canonical_expansion_of_recursiveRemainder P hr d hd Y hY
  have hb := profile_has_canonical_expansion_of_recursiveRemainder P hr e (by simpa only [← hde.length_eq] using hd) Y hY
  have he : (fun g => profile P g e Y) = (fun g => profile P g d Y) := by
    funext g
    exact (profile_perm P g hde Y).symm
  rw [he, ← hde.length_eq] at hb
  exact inverse_power_expansion_unique _ _ _ _ (Analysis.complexity_real_tendsto_atTop d.length) ha hb

lemma formalProfile_perm_of_recursiveRemainder (P : PsiTheory)
    (hr : UniformRecursiveRemainderTarget P) {d e : List ℕ} (hde : d.Perm e)
    (hd : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) y₀) :
    formalProfile P Y d = formalProfile P Y e := by
  ext j
  simp only [formalProfile, PowerSeries.coeff_mk]
  exact congrFun (profileCoefficient_perm_of_recursiveRemainder P hr hde hd Y hY) j
end WP.HigherOrder

namespace WP.HigherOrder.ComplexCanonical
open Set Filter
open scoped Topology
lemma profileCoefficient_perm_on_complex_domain_of_recursiveRemainder
    (P : PsiTheory) (hr : WP.HigherOrder.UniformRecursiveRemainderTarget P)
    (Ω : Set ℂ) (hΩv : Convex ℝ Ω)
    (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω) (R : ℂ → ℂ)
    (hA : ∀ j : ℕ, ∀ d : List ℕ, 1 ≤ d.length →
      AnalyticOnNhd ℂ (fun z => profileCoefficient P R z d j) Ω)
    (hrestrict : ∀ j : ℕ, ∀ d : List ℕ, 1 ≤ d.length → ∀ Y ∈ Icc (0 : ℝ) y₀,
      profileCoefficient P R (Y : ℂ) d j = (WP.HigherOrder.profileCoefficient P Y d j : ℂ))
    {d e : List ℕ} (hde : d.Perm e) (hd : 1 ≤ d.length) (j : ℕ) :
    EqOn (fun z => profileCoefficient P R z d j) (fun z => profileCoefficient P R z e j) Ω := by
  have he : 1 ≤ e.length := by simpa only [← hde.length_eq] using hd
  have hc : y₀ / 2 ∈ Ioo (0 : ℝ) y₀ := by constructor <;> linarith [y₀_pos]
  have hreal : ∀ᶠ Y : ℝ in 𝓝 (y₀ / 2),
      profileCoefficient P R (Y : ℂ) d j = profileCoefficient P R (Y : ℂ) e j := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with Y hY
    rw [hrestrict j d hd Y ⟨hY.1.le, hY.2.le⟩, hrestrict j e he Y ⟨hY.1.le, hY.2.le⟩,
      congrFun (WP.HigherOrder.profileCoefficient_perm_of_recursiveRemainder P hr hde hd Y
        ⟨hY.1.le, hY.2.le⟩) j]
  exact WP.Analysis.complex_identity_of_real_germ _ _ Ω (y₀ / 2) (hA j d hd) (hA j e he)
    hΩv.isPreconnected (hcover _ ⟨hc.1.le, hc.2.le⟩) hreal
end WP.HigherOrder.ComplexCanonical
