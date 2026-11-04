import WPFormalization.Critical.CriticalSpectrumBadEvents

/- Actual physical spectrum comparison events. The separating term is the
true already measurable geometric count. The two G3 majorants are ordinary
explicit arguments until their actual finite recording producers are supplied.
No spectrum comparison, coverage, or probability limit is made an external input. -/
noncomputable section
set_option maxHeartbeats 500000
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
  {g n : ℕ} (L : ℝ≥0)

def physicalSpectrumComparisonMajorant
    (Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  Mns X + Mint X + separatingNonPantsCount T X L

def physicalSpectrumComparisonBadSet
    (Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞) :
    Set (G.Moduli g n (fun _ => 0)) :=
  {X | 1 ≤ physicalSpectrumComparisonMajorant T L Mns Mint X}

lemma physicalSpectrumComparisonMajorant_measurable
    (MI : MirzakhaniIntegration G H T) (hg : 1≤g)
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (hns : Measurable Mns) (hint : Measurable Mint) :
    Measurable (physicalSpectrumComparisonMajorant T L Mns Mint) :=
  (hns.add hint).add (separatingNonPantsCount_measurable T MI hg L)

lemma physicalSpectrumComparisonBadSet_measurable
    (MI : MirzakhaniIntegration G H T) (hg : 1≤g)
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (hns : Measurable Mns) (hint : Measurable Mint) :
    MeasurableSet (physicalSpectrumComparisonBadSet T L Mns Mint) :=
  measurableSet_le measurable_const
    (physicalSpectrumComparisonMajorant_measurable T L MI hg hns hint)

lemma physicalSpectrumComparison_majorants_lt_one
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (X : G.Moduli g n (fun _ => 0))
    (hX : X∉physicalSpectrumComparisonBadSet T L Mns Mint) :
    Mns X<1 ∧ Mint X<1 ∧ separatingNonPantsCount T X L<1 := by
  have hh : Mns X+Mint X+separatingNonPantsCount T X L<1 := lt_of_not_ge hX
  refine ⟨lt_of_le_of_lt ?_ hh,lt_of_le_of_lt ?_ hh,lt_of_le_of_lt ?_ hh⟩
  · exact le_trans le_self_add le_self_add
  · exact le_trans le_add_self le_self_add
  · exact le_add_self

lemma physicalSpectrumComparison_no_separating_nonpants
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (X : G.Moduli g n (fun _ => 0))
    (hX : X∉physicalSpectrumComparisonBadSet T L Mns Mint) :
    ¬HasShortSeparatingNonPants T L X := by
  intro hb
  exact not_le_of_gt (physicalSpectrumComparison_majorants_lt_one T L X hX).2.2
    (one_le_separatingNonPantsCount_of_bad T L X hb)

lemma physicalSpectrumComparison_no_intersecting_pants
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (hdom : ∀X,allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤ Mint X)
    (X : G.Moduli g n (fun _ => 0))
    (hX : X∉physicalSpectrumComparisonBadSet T L Mns Mint) :
    ¬HasIntersectingShortPants T (2*(L:ℝ)) X := by
  intro hb
  exact not_le_of_gt (physicalSpectrumComparison_majorants_lt_one T L X hX).2.1
    ((one_le_allShortIntersecting_count_of_pants_bad T _ X hb).trans (hdom X))

lemma critical_physicalSpectrumComparisonBadSet_probability_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (Mns Mint : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hns : ∀ᶠg in atTop,Measurable (Mns g))
    (hint : ∀ᶠg in atTop,Measurable (Mint g))
    (hnsmean : Tendsto (fun g => ∫⁻X,Mns g X ∂wpProbability G g (n g)) atTop (𝓝 0))
    (hintmean : Tendsto (fun g => ∫⁻X,Mint g X ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => wpProbability G g (n g)
      (physicalSpectrumComparisonBadSet T L (Mns g) (Mint g))) atTop (𝓝 0) := by
  apply bad_event_probability_tendsto_zero_of_measurable_majorant
    (fun g => wpProbability G g (n g)) _
    (fun g => physicalSpectrumComparisonMajorant T L (Mns g) (Mint g))
  · filter_upwards [hns,hint,eventually_ge_atTop (1:ℕ)] with g hng hig hg
    exact (physicalSpectrumComparisonMajorant_measurable T L MI hg hng hig).aemeasurable
  · exact Eventually.of_forall (fun _ _ hX => hX)
  · have hm := (hnsmean.add hintmean).add
      (critical_separatingNonPantsCount_tendsto_zero T MI L L.2 n c hc hn)
    simp only [add_zero] at hm
    apply hm.congr'
    filter_upwards [hns,hint] with g hng hig
    exact (lintegral_add_left (hng.add hig) _).trans
      (congrArg (fun a => a+∫⁻X,separatingNonPantsCount T X L
        ∂wpProbability G g (n g)) (lintegral_add_left hng _)) |>.symm

lemma critical_physicalSpectrumComparisonBadSet_probability_real_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (Mns Mint : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hns : ∀ᶠg in atTop,Measurable (Mns g))
    (hint : ∀ᶠg in atTop,Measurable (Mint g))
    (hnsmean : Tendsto (fun g => ∫⁻X,Mns g X ∂wpProbability G g (n g)) atTop (𝓝 0))
    (hintmean : Tendsto (fun g => ∫⁻X,Mint g X ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      (physicalSpectrumComparisonBadSet T L (Mns g) (Mint g))) atTop (𝓝 0) := by
  simpa only [Measure.real,ENNReal.toReal_zero,Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (critical_physicalSpectrumComparisonBadSet_probability_tendsto_zero
        T L MI n c hc hn Mns Mint hns hint hnsmean hintmean)

end WP.Critical
