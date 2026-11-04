import WPFormalization.Critical.ClusterWindowMoments
import WPFormalization.External.PantsFigureEight
import WPFormalization.Probability.TwoColorPointMeasuresIntensities

/-! Canonical cluster window counts and their finite moments. -/

noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External MeasureTheory ProbabilityTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology Classical

lemma figureEight_small_waist (L : ℝ) (hL : 2 * Real.arcosh 3 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      s < L ∧ 2 * Real.arcosh (2 + Real.cosh (s/2)) < L := by
  have hcont : ContinuousAt (fun s : ℝ => 2 * Real.arcosh (2 + Real.cosh (s/2))) 0 := by
    apply continuousAt_const.mul
    exact (Real.continuousOn_arcosh.continuousAt
      (Ici_mem_nhds (by norm_num))).comp (by fun_prop)
  have hlim : (∀ᶠ s : ℝ in 𝓝 0, 2 * Real.arcosh (2 + Real.cosh (s/2)) < L) :=
    hcont (isOpen_Iio.mem_nhds (by convert hL using 1 <;> norm_num))
  have hLpos : 0 < L := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (Real.arcosh_nonneg (by norm_num))) hL
  obtain ⟨ε,hε,h⟩ := Metric.eventually_nhds_iff.mp
    (hlim.and (show ∀ᶠ s : ℝ in 𝓝 0, s < L from Iio_mem_nhds hLpos))
  exact ⟨ε,hε,fun s hs hsε => by
    obtain ⟨h1,h2⟩ := h (y := s) (by simpa [Real.dist_eq, abs_of_pos hs] using hsε)
    exact ⟨h2,h1⟩⟩

lemma windowMultiplicity_ge_two (F : Family.{u, v}) (R : FigureEightClassics F)
    (L s : ℝ≥0) (hs : 0 < s) (hsL : s ≤ L)
    (hfig : 2 * Real.arcosh (2 + Real.cosh ((s : ℝ)/2)) ≤ L) :
    2 ≤ windowMultiplicity F L s := by
  let w : Waist := ⟨s, by exact_mod_cast hs⟩
  obtain ⟨γ,hγ,hlen⟩ := R w
  have ha : γ ∈ F.short w L := (F.mem_short w L γ).mpr (hlen.trans_le hfig)
  have hb : F.waistClass ∈ F.short w L :=
    (F.mem_short w L _).mpr (by rw [F.length_waist]; exact_mod_cast hsL)
  have hcard : 2 ≤ (F.short w L).card :=
    Finset.Nontrivial.two_le_card ⟨γ,ha,F.waistClass,hb,hγ⟩
  rw [windowMultiplicity_pos F L s hs, measure_Iic, ENNReal.toReal_natCast]
  have he : Nat.card {γ : F.Primitive // F.length w γ ≤ (L : ℝ)} = (F.short w L).card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun γ => (F.mem_short w L γ).symm))]
    simp [Nat.card_eq_fintype_card]
  change (2 : ℝ) ≤ (Nat.card {γ : F.Primitive // F.length w γ ≤ (L : ℝ)} : ℝ)
  rw [he]; exact_mod_cast hcard

lemma criticalPantsLengthIntensity_Ioo_pos (c : ℝ) (hc : 0 < c)
    (ε : ℝ≥0) (hε : 0 < ε) :
    0 < criticalPantsLengthIntensity c (Ioo 0 ε) := by
  have himage : NNReal.toReal '' (Ioo (0 : ℝ≥0) ε) = Ioo (0 : ℝ) ε := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact_mod_cast hy
    · intro hx; exact ⟨⟨x,hx.1.le⟩, by exact_mod_cast hx, rfl⟩
  rw [criticalPantsLengthIntensity, nonnegativeIntensity_apply, himage,
    Critical.surviving_criticalIntensity_apply c _ measurableSet_Ioo ε
      (fun s hs => ⟨hs.1.le,hs.2.le⟩), ENNReal.ofReal_pos]
  have hd (s : ℝ) (hs : 0 < s) : 0 < criticalIntensityDensity c s := by
    unfold criticalIntensityDensity
    exact mul_pos (div_pos (sq_pos_of_pos hc) (by positivity))
      (Real.sinh_pos_iff.mpr (by linarith))
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact (hd s hs.1).le)
    ((Critical.surviving_criticalIntensityDensity_continuous c).integrableOn_Icc.mono_set
      (show Ioo (0 : ℝ) ε ⊆ Icc 0 ε from Ioo_subset_Icc_self))).mpr
  have he : Function.support (criticalIntensityDensity c) ∩ Ioo (0 : ℝ) ε = Ioo (0 : ℝ) ε := by
    apply inter_eq_right.mpr
    intro s hs; exact ne_of_gt (hd s hs.1)
  rw [he, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by simpa only [sub_zero] using
    (show 0 < (ε : ℝ) by exact_mod_cast hε))

lemma clusterWindow_excess_pos (F : Family.{u, v}) (D : DeformationClassics F)
    (R : FigureEightClassics F)
    (hproper : ∀ (s : Waist) (L : ℝ≥0), 2 * (L : ℝ) < s.val → measure F s (Iic L) = 0)
    (c : ℝ) (hc : 0 < c) (L : ℝ≥0) (hL : 2 * Real.arcosh 3 < L) :
    0 < ∫ s, windowMultiplicity F L s * (windowMultiplicity F L s - 1)
      ∂criticalPantsLengthIntensity c := by
  have hn (s : ℝ≥0) : 0 ≤ windowMultiplicity F L s * (windowMultiplicity F L s - 1) := by
    obtain ⟨n,hn⟩ := windowMultiplicity_nat F L s
    rw [hn]
    rcases Nat.eq_zero_or_pos n with hz | hp
    · simp [hz]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hp
      positivity
  have hi : Integrable (fun s => windowMultiplicity F L s * (windowMultiplicity F L s - 1))
      (criticalPantsLengthIntensity c) := by
    have he : (fun s => windowMultiplicity F L s * (windowMultiplicity F L s - 1)) =
        fun s => (windowMultiplicity F L s)^2 - windowMultiplicity F L s := by funext s; ring
    rw [he]
    exact (windowMultiplicity_sq_integrable F D hproper L _).sub
      (windowMultiplicity_integrable F D hproper L _)
  apply (integral_pos_iff_support_of_nonneg hn hi).mpr
  obtain ⟨ε,hε,hsmall⟩ := figureEight_small_waist L hL
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  apply (criticalPantsLengthIntensity_Ioo_pos c hc e (by exact_mod_cast hε)).trans_le
  apply measure_mono
  intro s hs
  obtain ⟨hsL,hfig⟩ := hsmall s (by exact_mod_cast hs.1) (by exact_mod_cast hs.2)
  have hm := windowMultiplicity_ge_two F R L s hs.1 (by exact_mod_cast hsL.le) hfig.le
  have hp : 0 < windowMultiplicity F L s * (windowMultiplicity F L s - 1) :=
    mul_pos (by linarith) (by linarith)
  exact hp.ne'
end WP.Critical.PantsCluster
