import WPFormalization.Tight.ConnectedOrbitIntegration
import WPFormalization.Tight.ConnectedOrbitRealization
import WPFormalization.Tight.SpectrumTupleExtensionsOrbitSum

/-! The actual ordered connected-complement tight tuple contribution in F.4.
The finite full-geodesic count is identified with its topological orbit sum,
then with the true BL integral and the established F.2 coefficient asymptotic.
All cusp counts and bounded Borel product windows are retained. -/
noncomputable section
namespace WP.TightConnected
open Set Filter Finset MeasureTheory External
open scoped Topology BigOperators ENNReal Pointwise

def connectedCuspProbability {P : PsiTheory} (G : WeilPeterssonGeometry P) (g n : ℕ) :
    Measure (TightSurface G g 0 n (fun _=>0) (fun _=>0)) :=
  (G.wpMeasure g n (fun _=>0) univ)⁻¹ •
    G.wpMeasure g (0+n) (Fin.append (fun _ : Fin 0=>0) (fun _ : Fin n=>0))

lemma connected_cusp_probability_measurePreserving {P : PsiTheory}
    (G : WeilPeterssonGeometry P) (g n : ℕ) :
    MeasurePreserving (tightCuspMeasurableEquiv G g n)
      (connectedCuspProbability G g n) (wpProbability G g n) :=
  tightCuspMeasurableEquiv_wpProbability G g n

def connectedScaledWindow (g k n : ℕ) (I : Fin k→Set ℝ) : Set (Fin k→ℝ) :=
  {x|∀i,tightScale ((n:ℝ)/(g:ℝ))*x i∈I i}

def connectedWindowOrbitSum {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology G T H Q)
    (g k n : ℕ) (I : Fin k→Set ℝ)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : ℝ≥0∞ :=
  ∑o∈connectedOrbitFinset A g k,A.orbitSum o ((connectedScaledWindow g k n I).indicator (fun _=>1)) X

def connectedScaledWindowCount {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
    (g k n : ℕ) (I : Fin k→Set ℝ)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : ℕ :=
  Nat.card {Γ : Fin k→Q.Geodesic g 0 n (fun _=>0) (fun _=>0) X //
    Tight.SpectrumTupleExtensions.FilteredOrbitWindowTuple Q A X
      (fun o : A.Orbit g 0 k=>(A.cut o).components=1) (connectedScaledWindow g k n I) Γ}

lemma connected_scaled_window_count_eq_orbit_sum {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
    (g k n : ℕ) (hg : 2≤g) (I : Fin k→Set ℝ)
    (B : ℝ) (hIB : ∀i,I i⊆Icc (0:ℝ) B)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) :
    (connectedScaledWindowCount Q A g k n I X : ℝ≥0∞)=connectedWindowOrbitSum A g k n I X := by
  have hα : 0<tightScale ((n:ℝ)/(g:ℝ)) := tightScale_pos _ (by positivity)
  unfold connectedScaledWindowCount connectedWindowOrbitSum connectedOrbitFinset
  classical
  convert Tight.SpectrumTupleExtensions.filtered_window_count_eq_orbit_sum Q A X
    (fun o : A.Orbit g 0 k=>(A.cut o).components=1) (connectedScaledWindow g k n I)
    (B/tightScale ((n:ℝ)/(g:ℝ)))
    (fun x hx i=>(le_div_iff₀ hα).mpr (by simpa only [mul_comm] using (hIB i (hx i)).2))
    (by unfold Stable;omega) using 1 <;> try rfl
  apply Finset.sum_congr
  · ext o
    simp
  · intro o ho
    unfold TightMulticurveTopology.orbitSum
    apply tsum_congr
    intro Γ
    by_cases hmem : A.orbitMem o X Γ
    · simp only [hmem,ite_true]
    · simp only [hmem,ite_false]

lemma connected_scaled_window_count_measurable {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A)
    (g k n : ℕ) (hg : 2≤g) (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Measurable (fun X=>(connectedScaledWindowCount Q A g k n I X : ℝ≥0∞)) := by
  have hW : MeasurableSet (connectedScaledWindow g k n I) :=
    RandomGeometry.pants_numeric_window_set_measurable k
      (fun i=>{t|tightScale ((n:ℝ)/(g:ℝ))*t∈I i})
      (fun i=>(measurable_const.mul measurable_id) (hI i))
  have hm : Measurable (connectedWindowOrbitSum A g k n I) := by
    unfold connectedWindowOrbitSum
    apply Finset.measurable_sum
    intro o ho
    exact MI.orbitSum_measurable o (fun _=>0) (fun _=>0) _ (measurable_const.indicator hW)
  have he : (fun X=>(connectedScaledWindowCount Q A g k n I X : ℝ≥0∞)) =
      connectedWindowOrbitSum A g k n I :=
    funext (connected_scaled_window_count_eq_orbit_sum Q A g k n hg I B hIB)
  rw [he]
  exact hm

lemma connected_window_orbit_expectation_tendsto {P : PsiTheory}
    {G : WeilPeterssonGeometry P} (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {H : HyperbolicCurveGeometry G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫⁻X,connectedWindowOrbitSum A (gs j) k (ns j) I X
      ∂connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (ENNReal.ofReal (∏i,∫t in I i,tightIntensityDensity t))) := by
  classical
  let gs' : ℕ→ℕ := fun j=>max (k+2) (gs j)
  have hgs' : Tendsto gs' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hgs
  let os : (j:ℕ)→A.Orbit (gs' j) 0 k := fun j=>
    Classical.choose (connected_orbit_exists_unique A (gs' j) k (by dsimp [gs'];omega) (by dsimp [gs'];omega))
  have hos (j:ℕ) : (A.cut (os j)).components=1 :=
    (Classical.choose_spec (connected_orbit_exists_unique A (gs' j) k
      (by dsimp [gs'];omega) (by dsimp [gs'];omega))).1
  let Ds := fun j=>A.cut (os j)
  let cs : (j:ℕ)→Fin (Ds j).components := fun j=>(finCongr (hos j)).symm 0
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (connected_cut_scaled_coefficient_integral_tendsto P k gs' ns hgs' Ds hos cs I hI B hB hIB)
  obtain ⟨N,hN⟩ := connected_cusp_volume_positive_eventually P G
  have ht' : Tendsto (fun j=>∫⁻X,connectedWindowOrbitSum A (gs' j) k (ns j) I X
      ∂connectedCuspProbability G (gs' j) (ns j)) atTop
      (𝓝 (ENNReal.ofReal (∏i,∫t in I i,tightIntensityDensity t))) := by
    apply ht.congr'
    filter_upwards [hgs'.eventually_ge_atTop N] with j hj
    symm
    calc
      _ = ∫⁻X,A.orbitSum (os j) ((connectedScaledWindow (gs' j) k (ns j) I).indicator (fun _=>1)) X
          ∂connectedCuspProbability G (gs' j) (ns j) := by
        apply lintegral_congr
        intro X
        unfold connectedWindowOrbitSum
        rw [connected_orbit_finset_singleton A (os j) (hos j)]
        simp
      _ = _ := connected_orbit_scaled_window_expectation_eq T BZ A MI (gs' j) k (ns j)
        (by dsimp [gs'];omega) (os j) (hos j) (cs j) (hN (gs' j) hj (ns j)) I hI B hB hIB
  apply ht'.congr'
  filter_upwards [hgs.eventually_ge_atTop (k+2)] with j hj
  have he : gs' j=gs j := max_eq_right hj
  exact congrArg (fun g=>∫⁻X,connectedWindowOrbitSum A g k (ns j) I X
    ∂connectedCuspProbability G g (ns j)) he

lemma connected_scaled_window_count_expectation_tendsto {P : PsiTheory}
    {G : WeilPeterssonGeometry P} (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {H : HyperbolicCurveGeometry G} (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫⁻X,(connectedScaledWindowCount Q A (gs j) k (ns j) I X : ℝ≥0∞)
      ∂connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (ENNReal.ofReal (∏i,∫t in I i,tightIntensityDensity t))) := by
  apply (connected_window_orbit_expectation_tendsto T BZ A MI k gs ns hgs I hI B hB hIB).congr'
  filter_upwards [hgs.eventually_ge_atTop 2] with j hj
  apply lintegral_congr
  intro X
  exact (connected_scaled_window_count_eq_orbit_sum Q A (gs j) k (ns j) hj I B hIB X).symm

lemma tight_intensity_nonnegative {t : ℝ} (ht : 0≤t) : 0≤tightIntensityDensity t := by
  rw [Critical.surviving_loop_intensity_eq_boundaryFactor]
  positivity

lemma tight_intensity_window_measure (I : Set ℝ) (hI : MeasurableSet I)
    (B : ℝ) (hIB : I⊆Icc (0:ℝ) B) :
    tightIntensity I=ENNReal.ofReal (∫t in I,tightIntensityDensity t) := by
  have hsub : I⊆Ici (0:ℝ) := fun t ht=>(hIB ht).1
  have hnonneg : 0≤ᵐ[volume.restrict I] tightIntensityDensity := by
    filter_upwards [ae_restrict_mem hI] with t ht
    exact tight_intensity_nonnegative (hsub ht)
  have hint : IntegrableOn tightIntensityDensity I :=
    tightIntensityDensity_continuous.integrableOn_Icc.mono_set hIB
  rw [tightIntensity,withDensity_apply _ hI,
    Measure.restrict_restrict hI,inter_eq_left.mpr hsub,
    ofReal_integral_eq_lintegral_ofReal hint hnonneg]

lemma connected_window_intensity_product (k : ℕ) (I : Fin k→Set ℝ)
    (hI : ∀i,MeasurableSet (I i)) (B : ℝ) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    ENNReal.ofReal (∏i,∫t in I i,tightIntensityDensity t)=∏i,tightIntensity (I i) := by
  simp_rw [tight_intensity_window_measure _ (hI _) B (hIB _)]
  apply ENNReal.ofReal_prod_of_nonneg
  intro i hi
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (hI i)] with t ht
  exact tight_intensity_nonnegative (hIB i ht).1

lemma connected_scaled_window_count_expectation_tendsto_intensity {P : PsiTheory}
    {G : WeilPeterssonGeometry P} (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    {H : HyperbolicCurveGeometry G} (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology G T H Q) (MI : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (I : Fin k→Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (B : ℝ) (hB : 0≤B) (hIB : ∀i,I i⊆Icc (0:ℝ) B) :
    Tendsto (fun j=>∫⁻X,(connectedScaledWindowCount Q A (gs j) k (ns j) I X : ℝ≥0∞)
      ∂connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (∏i,tightIntensity (I i))) := by
  rw [←connected_window_intensity_product k I hI B hIB]
  exact connected_scaled_window_count_expectation_tendsto T BZ Q A MI k gs ns hgs I hI B hB hIB

end WP.TightConnected
