import WPFormalization.RandomGeometry.PrimitiveSeparatingMoments

/-! The actual positive-genus separating competitors vanish on every bounded
original rescaled window. Only the already proved true volume-sum estimate is
used; no expectation or rare-event conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter Finset
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n : ℕ}

lemma primitiveSeparatingWindowSum_ge_one_of_exists (X : G.Moduli g n (fun _=>0))
    (L : ℝ) (hL : 0≤L) (hγ : ∃γ : H.Primitive g n X,H.length γ≤L ∧IsPositiveGenusSeparating T γ) :
    1≤primitiveSeparatingWindowSum T X L := by
  obtain ⟨γ,hγ,o,ho⟩ := hγ
  let τ : {τ : Fin 1→H.Primitive g n X //T.orbitMem o.val X τ} := ⟨fun _=>γ,ho⟩
  have ht : (1:ℝ≥0∞)≤T.orbitSum o.val (pantsWindowTest (fun _ : Fin 1=>Icc 0 L)) X := by
    have hw : pantsWindowTest (fun _ : Fin 1=>Icc 0 L) (fun i=>H.length (τ.val i))=1 := by
      simp only [pantsWindowTest,τ]
      exact if_pos (fun _=>⟨(H.length_pos γ).le,hγ⟩)
    rw [←hw]
    exact ENNReal.le_tsum (f:=fun δ : {δ : Fin 1→H.Primitive g n X //T.orbitMem o.val X δ}=>
      pantsWindowTest (fun _ : Fin 1=>Icc 0 L) (fun i=>H.length (δ.val i))) τ
  apply ht.trans
  unfold primitiveSeparatingWindowSum
  exact Finset.single_le_sum
    (f:=fun p : PrimitiveSeparatingOrbit T g n=>T.orbitSum p.val (pantsWindowTest (fun _ : Fin 1=>Icc 0 L)) X)
    (fun _ _=>bot_le) (Finset.mem_univ o)

include MI in
lemma primitiveSeparating_probability_le_mean (L : ℝ) (hL : 0≤L) :
    wpProbability G g n {X |∃γ : H.Primitive g n X,H.length γ≤L ∧IsPositiveGenusSeparating T γ}≤
      ∫⁻X : G.Moduli g n (fun _=>0),primitiveSeparatingWindowSum T X L ∂wpProbability G g n := by
  exact meas_le_lintegral₀ (primitiveSeparatingWindowSum_measurable T MI L).aemeasurable
    (fun X hX=>primitiveSeparatingWindowSum_ge_one_of_exists T X L hL hX)

include MI in
lemma primitiveSeparating_probability_upper (hg : 3≤g) (L : ℝ) (hL : 0≤L)
    (hV : 0<volumeModel P g n) :
    (wpProbability G g n).real {X |∃γ : H.Primitive g n X,H.length γ≤L ∧IsPositiveGenusSeparating T γ}≤
      primitiveSeparatingWindowEnvelope P g n L := by
  have hi := (primitiveSeparating_probability_le_mean T MI (g:=g) (n:=n) L hL).trans
    (primitiveSeparating_probability_lintegral_upper T MI (g:=g) (n:=n) hg L hL hV)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  have henv : 0≤primitiveSeparatingWindowEnvelope P g n L := by
    unfold primitiveSeparatingWindowEnvelope
    have hs : 0≤∑a : Fin (g-1)×(Fin n→Fin 2),primitiveSeparatingAllocationWeight P g n a :=
      Finset.sum_nonneg (fun a _=>primitiveSeparatingAllocationWeight_nonneg P g n a)
    rw [primitiveSeparatingAllocationWeight_sum] at hs
    have hr := div_nonneg hs hV.le
    have hA : 0≤primitiveSeparatingVolumeSum P g n := by
      simpa only [primitiveSeparatingVolumeSum,Finset.sum_div] using hr
    exact mul_nonneg (by positivity) hA
  simpa only [Measure.real,ENNReal.toReal_ofReal henv] using hh

include MI in
theorem primitiveSeparating_probability_tendsto_zero (n : ℕ→ℕ)
    (hn : Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun g=>(wpProbability G g (n g)).real {X |∃γ : H.Primitive g (n g) X,
      H.length γ≤t/Real.sqrt (pantsScale g (n g)) ∧IsPositiveGenusSeparating T γ}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _=>ENNReal.toReal_nonneg)) ?_
    (primitive_separating_window_envelope_tendsto_zero P n hn t)
  filter_upwards [eventually_ge_atTop (3:ℕ),WP.Spectral.fast_cusps_eventually_two n hn] with g hg hn1
  exact primitiveSeparating_probability_upper T MI hg _ (div_nonneg ht (Real.sqrt_nonneg _))
    (diagonal_volume_pos_nonempty P g (n g) (by omega) (by unfold Stable;omega))

end WP.RandomGeometry
