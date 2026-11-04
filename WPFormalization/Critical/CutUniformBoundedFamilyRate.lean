import WPFormalization.Critical.CutUniformEnvelope
import WPFormalization.Critical.CutUniformRegimeRate
/-! Uniform half-power bounds for entire finite cut families. Constants precede
all critical cusp sequences; only the eventual threshold may depend on them. -/
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
lemma critical_badPartitionCount_half_uniform_sequences
    (k Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (S : CutSkeleton k Q) (hS : S.Connected)
    (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, badPartitionCount T S L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold badPartitionCount
  apply finite_lintegral_parameter_uniform_ofReal_envelope univ
    (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp n g
    by_cases hb : p.2.2.val ≠ 1 ∨ p.2.1.val ≠ 0
    · simpa only [ite_eq_left hb] using
        cutPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
    · simp only [ite_eq_right hb]
      exact measurable_const
  · intro p hp
    by_cases hb : p.2.2.val ≠ 1 ∨ p.2.1.val ≠ 0
    · obtain ⟨C,hC,hbound⟩ := critical_ordered_nonSurviving_half_uniform_sequences T MI
        k Q p.1.val p.2.1.val p.2.2.val hk hQ hb L hL c hc
      refine ⟨C,hC,fun n hn => (hbound n hn).mono (fun g hg => ?_)⟩
      simpa only [ite_eq_left hb] using hg S hS
    · refine ⟨1,by norm_num,fun n hn => Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hb,lintegral_zero]
      exact bot_le

include MI in
lemma critical_markedPartitionFamilyCount_half_uniform_sequences
    (k Q : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (S : CutSkeleton k Q) (hS : S.Connected)
    (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, markedPartitionFamilyCount T S L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold markedPartitionFamilyCount
  apply finite_lintegral_parameter_uniform_ofReal_envelope univ
    (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp n g
    exact cutMarkedPartitionCount_measurable T MI S p.1.val p.2.1.val p.2.2.val L
  · intro p hp
    obtain ⟨C,hC,hbound⟩ := critical_ordered_marked_half_uniform_sequences T MI
      k Q p.1.val p.2.1.val p.2.2.val hk hQ L hL c hc
    exact ⟨C,hC,fun n hn => (hbound n hn).mono (fun g hg => hg S hS)⟩

include MI in
lemma critical_badCutFamilyCount_half_uniform_sequences
    (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, badCutFamilyCount T k L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold badCutFamilyCount
  apply finite_lintegral_parameter_uniform_ofReal_envelope univ
    (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro q hq n g
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      exact Finset.measurable_sum univ (fun S _ => badPartitionCount_measurable T MI S.val L)
    · simp only [ite_eq_right hQ]
      exact measurable_const
  · intro q hq
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      apply finite_lintegral_parameter_uniform_ofReal_envelope univ
        (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
        (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
        (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro S hS n g
        exact badPartitionCount_measurable T MI S.val L
      · intro S hS
        exact critical_badPartitionCount_half_uniform_sequences T MI k q.val hk hQ
          S.val S.property L hL c hc
    · refine ⟨1,by norm_num,fun n hn => Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hQ,lintegral_zero]
      exact bot_le

include MI in
lemma critical_markedCutFamilyCount_half_uniform_sequences
    (k : ℕ) (hk : 1 ≤ k) (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, markedCutFamilyCount T k L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold markedCutFamilyCount
  apply finite_lintegral_parameter_uniform_ofReal_envelope univ
    (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro q hq n g
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      exact Finset.measurable_sum univ (fun S _ => markedPartitionFamilyCount_measurable T MI S.val L)
    · simp only [ite_eq_right hQ]
      exact measurable_const
  · intro q hq
    by_cases hQ : 1 ≤ q.val
    · simp only [ite_eq_left hQ]
      apply finite_lintegral_parameter_uniform_ofReal_envelope univ
        (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
        (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
        (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · intro S hS n g
        exact markedPartitionFamilyCount_measurable T MI S.val L
      · intro S hS
        exact critical_markedPartitionFamilyCount_half_uniform_sequences T MI k q.val hk hQ
          S.val S.property L hL c hc
    · refine ⟨1,by norm_num,fun n hn => Eventually.of_forall (fun g => ?_)⟩
      simp only [ite_eq_right hQ,lintegral_zero]
      exact bot_le

include MI in
lemma critical_boundedComplexCutFamilyCount_half_uniform_sequences
    (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, boundedComplexCutFamilyCount T Kmax L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  unfold boundedComplexCutFamilyCount
  apply finite_lintegral_parameter_uniform_ofReal_envelope (Finset.Icc 1 Kmax)
    (fun n : ℕ → ℕ => Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (fun n g => wpProbability G g (n g)) (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro k hk n g
    exact (badCutFamilyCount_measurable T MI k L).add (markedCutFamilyCount_measurable T MI k L)
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    obtain ⟨Cb,hCb,hb⟩ := critical_badCutFamilyCount_half_uniform_sequences T MI k hk1 L hL c hc
    obtain ⟨Cm,hCm,hm⟩ := critical_markedCutFamilyCount_half_uniform_sequences T MI k hk1 L hL c hc
    refine ⟨Cb+Cm,add_pos hCb hCm,?_⟩
    intro n hn
    filter_upwards [hb n hn,hm n hn] with g hgb hgm
    rw [lintegral_add_left (badCutFamilyCount_measurable T MI k L)]
    calc
      _ ≤ ENNReal.ofReal (Cb * (g:ℝ)^(-1/2:ℝ)) + ENNReal.ofReal (Cm * (g:ℝ)^(-1/2:ℝ)) :=
        add_le_add hgb hgm
      _ = ENNReal.ofReal ((Cb+Cm) * (g:ℝ)^(-1/2:ℝ)) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hCb.le (Real.rpow_nonneg (Nat.cast_nonneg g) _))
          (mul_nonneg hCm.le (Real.rpow_nonneg (Nat.cast_nonneg g) _)),add_mul]

include MI in
lemma critical_boundedComplexCutFamilyCount_weighted_half_uniform_sequences
    (D : ℝ) (hD : 0 < D) (Kmax : ℕ) (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop,
        (∫⁻ X, ENNReal.ofReal D * boundedComplexCutFamilyCount T Kmax L X
          ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := critical_boundedComplexCutFamilyCount_half_uniform_sequences T MI Kmax L hL c hc
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro n hn
  filter_upwards [hb n hn] with g hg
  rw [lintegral_const_mul (ENNReal.ofReal D) (boundedComplexCutFamilyCount_measurable T MI Kmax L)]
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := mul_le_mul_right hg _
    _ = ENNReal.ofReal (D*C * (g:ℝ)^(-1/2:ℝ)) := by
      rw [← ENNReal.ofReal_mul hD.le,mul_assoc]
end WP.Critical
