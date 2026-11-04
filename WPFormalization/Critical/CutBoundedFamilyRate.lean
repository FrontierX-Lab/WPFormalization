import WPFormalization.Critical.CutFamilyEnvelope
import WPFormalization.Critical.MixedWindowMoments
/-! Quantitative bounds for the full finite bad and marked cut families,
including a bounded range of edge counts. All counts are actual MI counts. -/
noncomputable section
set_option maxHeartbeats 0
universe a b c d
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{a,b} P}
  {H : HyperbolicCurveGeometry.{a,b,c} G} (T : MulticurveTopology.{a,b,c,d} G H)
  (MI : MirzakhaniIntegration G H T)

include MI in
lemma critical_badPartitionCount_half_estimate_regime
    (k Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (S : CutSkeleton k Q) (hS : S.Connected)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, badPartitionCount T S L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold badPartitionCount
  apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
    (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp g
    by_cases hb : p.2.2.val ≠ 1 ∨ p.2.1.val ≠ 0
    · simpa only [ite_eq_left hb] using
        cutPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
    · simp only [ite_eq_right hb]
      exact measurable_const
  · intro p hp
    by_cases hb : p.2.2.val ≠ 1 ∨ p.2.1.val ≠ 0
    · obtain ⟨C, hC, hbound⟩ := critical_ordered_nonSurviving_estimate_regime G T MI
        k Q p.1.val p.2.1.val p.2.2.val hk hQ hb L hL n c hc hn
      refine ⟨C, hC, hbound.mono (fun g hg => ?_)⟩
      simpa only [ite_eq_left hb] using hg S hS
    · refine ⟨1, by norm_num, Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hb, lintegral_zero]
      exact bot_le

include MI in
lemma critical_markedPartitionFamilyCount_half_estimate_regime
    (k Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (S : CutSkeleton k Q) (hS : S.Connected)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, markedPartitionFamilyCount T S L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold markedPartitionFamilyCount
  apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
    (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp g
    exact cutMarkedPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
  · intro p hp
    obtain ⟨C, hC, hbound⟩ := critical_ordered_marked_half_estimate_regime T MI
      k Q p.1.val p.2.1.val p.2.2.val hk hQ L hL n c hc hn
    exact ⟨C, hC, hbound.mono (fun g hg => hg S hS)⟩

include MI in
lemma critical_badCutFamilyCount_half_estimate_regime
    (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, badCutFamilyCount T k L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold badCutFamilyCount
  apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
    (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro q hq g
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      exact Finset.measurable_sum univ (fun S _ => badPartitionCount_measurable T MI S.val L)
    · simp only [ite_eq_right hQ]
      exact measurable_const
  · intro q hq
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
        (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro S hS g
        exact badPartitionCount_measurable T MI S.val L
      · intro S hS
        exact critical_badPartitionCount_half_estimate_regime T MI k q.val hk hQ
          S.val S.property L hL n c hc hn
    · refine ⟨1, by norm_num, Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hQ, lintegral_zero]
      exact bot_le

include MI in
lemma critical_markedCutFamilyCount_half_estimate_regime
    (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, markedCutFamilyCount T k L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold markedCutFamilyCount
  apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
    (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro q hq g
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      exact Finset.measurable_sum univ (fun S _ => markedPartitionFamilyCount_measurable T MI S.val L)
    · simp only [ite_eq_right hQ]
      exact measurable_const
  · intro q hq
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      apply finite_lintegral_uniform_ofReal_envelope univ (fun g => wpProbability G g (n g))
        (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro S hS g
        exact markedPartitionFamilyCount_measurable T MI S.val L
      · intro S hS
        exact critical_markedPartitionFamilyCount_half_estimate_regime T MI k q.val hk hQ
          S.val S.property L hL n c hc hn
    · refine ⟨1, by norm_num, Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hQ, lintegral_zero]
      exact bot_le

def boundedComplexCutFamilyCount {g n : ℕ} (Kmax : ℕ) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ k ∈ Finset.Icc 1 Kmax, (badCutFamilyCount T k L X + markedCutFamilyCount T k L X)

lemma boundedComplexCutFamilyCount_zero {g n : ℕ} (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) : boundedComplexCutFamilyCount T 0 L X = 0 := by
  simp [boundedComplexCutFamilyCount]

include MI in
lemma boundedComplexCutFamilyCount_measurable {g n : ℕ} (Kmax : ℕ) (L : ℝ) :
    Measurable (boundedComplexCutFamilyCount T Kmax L (g:=g) (n:=n)) := by
  unfold boundedComplexCutFamilyCount
  apply Finset.measurable_sum
  intro k hk
  exact (badCutFamilyCount_measurable T MI k L).add (markedCutFamilyCount_measurable T MI k L)

include MI in
lemma boundedComplexCutFamilyCount_weighted_measurable {g n : ℕ}
    (D : ℝ) (Kmax : ℕ) (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      ENNReal.ofReal D * boundedComplexCutFamilyCount T Kmax L X) :=
  measurable_const.mul (boundedComplexCutFamilyCount_measurable T MI Kmax L)

include MI in
lemma critical_boundedComplexCutFamilyCount_half_estimate_regime
    (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, boundedComplexCutFamilyCount T Kmax L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold boundedComplexCutFamilyCount
  apply finite_lintegral_uniform_ofReal_envelope (Finset.Icc 1 Kmax)
    (fun g => wpProbability G g (n g))
    (fun g => (g:ℝ)^(-1/2:ℝ)) (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro k hk g
    exact (badCutFamilyCount_measurable T MI k L).add (markedCutFamilyCount_measurable T MI k L)
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    obtain ⟨Cb, hCb, hb⟩ := critical_badCutFamilyCount_half_estimate_regime T MI k hk1 L hL n c hc hn
    obtain ⟨Cm, hCm, hm⟩ := critical_markedCutFamilyCount_half_estimate_regime T MI k hk1 L hL n c hc hn
    refine ⟨Cb + Cm, add_pos hCb hCm, ?_⟩
    filter_upwards [hb, hm] with g hgb hgm
    rw [lintegral_add_left (badCutFamilyCount_measurable T MI k L)]
    calc
      _ ≤ ENNReal.ofReal (Cb * (g:ℝ)^(-1/2:ℝ)) + ENNReal.ofReal (Cm * (g:ℝ)^(-1/2:ℝ)) :=
        add_le_add hgb hgm
      _ = ENNReal.ofReal ((Cb + Cm) * (g:ℝ)^(-1/2:ℝ)) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hCb.le (Real.rpow_nonneg (Nat.cast_nonneg g) _))
          (mul_nonneg hCm.le (Real.rpow_nonneg (Nat.cast_nonneg g) _)), add_mul]

include MI in
lemma critical_boundedComplexCutFamilyCount_weighted_half_estimate_regime
    (D : ℝ) (hD : 0 < D) (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∫⁻ X, ENNReal.ofReal D * boundedComplexCutFamilyCount T Kmax L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  obtain ⟨C, hC, hb⟩ := critical_boundedComplexCutFamilyCount_half_estimate_regime T MI Kmax L hL n c hc hn
  refine ⟨D * C, mul_pos hD hC, hb.mono (fun g hg => ?_)⟩
  rw [lintegral_const_mul (ENNReal.ofReal D) (boundedComplexCutFamilyCount_measurable T MI Kmax L)]
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := mul_le_mul_right hg _
    _ = ENNReal.ofReal (D * C * (g:ℝ)^(-1/2:ℝ)) := by
      rw [← ENNReal.ofReal_mul hD.le, mul_assoc]

include MI in
lemma critical_boundedComplexCutFamilyCount_tendsto_zero
    (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X, boundedComplexCutFamilyCount T Kmax L X
      ∂wpProbability G g (n g)) atTop (𝓝 0) :=
  critical_half_envelope_tendsto_zero _
    (critical_boundedComplexCutFamilyCount_half_estimate_regime T MI Kmax L hL n c hc hn)

include MI in
lemma critical_boundedComplexCutFamilyCount_weighted_tendsto_zero
    (D : ℝ) (hD : 0 < D) (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X, ENNReal.ofReal D * boundedComplexCutFamilyCount T Kmax L X
      ∂wpProbability G g (n g)) atTop (𝓝 0) :=
  critical_half_envelope_tendsto_zero _
    (critical_boundedComplexCutFamilyCount_weighted_half_estimate_regime T MI D hD Kmax L hL n c hc hn)
end WP.Critical
