import WPFormalization.Critical.CutBoundedFamilyRate
/-! Critical sequence bounds with constants chosen before the cusp sequence. -/
noncomputable section
set_option maxHeartbeats 0
universe a b c d
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter Finset
open scoped Classical ENNReal Topology

lemma critical_cusp_regime_eventually_fixed (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    ∀ᶠ g in atTop, 1 ≤ n g ∧ (n g : ℝ) ≤ (c+1) * Real.sqrt g := by
  have hu : ∀ᶠ g : ℕ in atTop, (n g : ℝ)/Real.sqrt g < c+1 :=
    hn.eventually (Iio_mem_nhds (by linarith))
  have hl : ∀ᶠ g : ℕ in atTop, 0 < (n g : ℝ)/Real.sqrt g :=
    hn.eventually (Ioi_mem_nhds hc)
  filter_upwards [hu, hl, eventually_ge_atTop 1] with g hgu hgl hg
  have hs : 0 < Real.sqrt (g : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hg)
  have hnpos : 0 < (n g : ℝ) := (div_pos_iff_of_pos_right hs).mp hgl
  refine ⟨by exact_mod_cast (by exact_mod_cast hnpos : 0 < n g), ?_⟩
  exact ((div_lt_iff₀ hs).mp hgu).le

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{a,b} P}
  {H : HyperbolicCurveGeometry.{a,b,c} G} (T : MulticurveTopology.{a,b,c,d} G H)
  (MI : MirzakhaniIntegration G H T)

include MI in
lemma critical_cut_estimate_uniform_sequences
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop, ∀ S : CutSkeleton k Q, S.Connected →
        (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_estimate G T MI k Q u v w hk hQ
    (c+1) L (by linarith) hL
  refine ⟨C,hC,?_⟩
  intro n hn
  filter_upwards [critical_cusp_regime_eventually_fixed n c hc hn,
    eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2

include MI in
lemma critical_cut_marked_estimate_uniform_sequences
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop, ∀ S : CutSkeleton k Q, S.Connected →
        (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by
  obtain ⟨C,hC,G₀,hr⟩ := critical_cut_marked_estimate G T MI k Q u v w hk hQ
    (c+1) L (by linarith) hL
  refine ⟨C,hC,?_⟩
  intro n hn
  filter_upwards [critical_cusp_regime_eventually_fixed n c hc hn,
    eventually_ge_atTop G₀] with g hg hG
  exact hr g hG (n g) hg.1 hg.2

include MI in
lemma critical_ordered_nonSurviving_half_uniform_sequences
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hbad : w ≠ 1 ∨ v ≠ 0)
    (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop, ∀ S : CutSkeleton k Q, S.Connected →
        (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,hr⟩ := critical_cut_estimate_uniform_sequences T MI k Q u v w hk hQ L hL c hc
    refine ⟨C,hC,?_⟩
    intro n hn
    filter_upwards [hr n hn,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (nonSurviving_cut_exponent hw hbad)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    intro n hn
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    simp only [cutPartitionCount,partitionOrbits_zero_stable T S u v hg,sum_empty,lintegral_zero]
    exact bot_le

include MI in
lemma critical_ordered_marked_half_uniform_sequences
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (L : ℝ) (hL : 0 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠ g in atTop, ∀ S : CutSkeleton k Q, S.Connected →
        (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
          ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,hr⟩ := critical_cut_marked_estimate_uniform_sequences T MI k Q u v w hk hQ L hL c hc
    refine ⟨C,hC,?_⟩
    intro n hn
    filter_upwards [hr n hn,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hwR : (1:ℝ) ≤ w := by exact_mod_cast hw
    have hvR : (0:ℝ) ≤ v := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (by linarith)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    intro n hn
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    simp only [cutMarkedPartitionCount,markedPartitionOrbits_zero_stable T S u v hg,sum_empty,lintegral_zero]
    exact bot_le
end WP.Critical
