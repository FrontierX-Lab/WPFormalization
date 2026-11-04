import WPFormalization.Critical.CutFiniteCatalogRate
import WPFormalization.Probability.MeasurableMajorantRate

/-! The finite actual cut catalogue is measurable by Mirzakhani integration.
Geometric recording and its pointwise domination remain separate proof
obligations; none is an external/classical interface field here. -/
noncomputable section
universe a b c d
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{a, b} P}
  {H : HyperbolicCurveGeometry.{a, b, c} G}
  (T : MulticurveTopology.{a, b, c, d} G H)
  {ι : Type*} [Fintype ι] (k Q u v w : ι → ℕ)
  (S : ∀ i, CutSkeleton (k i) (Q i)) (marked : ι → Bool) (L : ι → ℝ)

def finiteCutCatalogCount {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑ i, if marked i then
    cutMarkedPartitionCount T (S i) (u i) (v i) (w i) (L i) X
    else cutPartitionCount T (S i) (u i) (v i) (w i) (L i) X

include T in
lemma finiteCutCatalogCount_measurable (MI : MirzakhaniIntegration G H T)
    (g n : ℕ) :
    Measurable (finiteCutCatalogCount T k Q u v w S marked L (g:=g) (n:=n)) := by
  apply Finset.measurable_sum
  intro i hi
  cases hm : marked i with
  | false => simpa only [hm, Bool.false_eq_true, ite_false] using
      cutPartitionCount_measurable T MI (S i) (u i) (v i) (w i) (L i)
  | true => simpa only [hm, ite_true] using
      cutMarkedPartitionCount_measurable T MI (S i) (u i) (v i) (w i) (L i)

lemma finiteCutCatalogCount_lintegral (MI : MirzakhaniIntegration G H T)
    (g n : ℕ) :
    (∫⁻ X, finiteCutCatalogCount T k Q u v w S marked L X ∂wpProbability G g n) =
      ∑ i, ∫⁻ X, (if marked i then
        cutMarkedPartitionCount T (S i) (u i) (v i) (w i) (L i) X
        else cutPartitionCount T (S i) (u i) (v i) (w i) (L i) X)
          ∂wpProbability G g n := by
  apply lintegral_finsetSum
  intro i hi
  cases hm : marked i with
  | false => simpa only [hm, Bool.false_eq_true, ite_false] using
      cutPartitionCount_measurable T MI (S i) (u i) (v i) (w i) (L i)
  | true => simpa only [hm, ite_true] using
      cutMarkedPartitionCount_measurable T MI (S i) (u i) (v i) (w i) (L i)

variable (MI : MirzakhaniIntegration G H T)
  (hk : ∀ i, 1 ≤ k i) (hQ : ∀ i, 1 ≤ Q i) (hS : ∀ i, (S i).Connected)
  (hbad : ∀ i, marked i = false → w i ≠ 1 ∨ v i ≠ 0)
  (hL : ∀ i, 0 ≤ L i) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
  (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c))

include MI hk hQ hS hbad hL hc hn

lemma finiteCutCatalogCount_half_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop,
      (∫⁻ X, finiteCutCatalogCount T k Q u v w S marked L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  simp_rw [finiteCutCatalogCount_lintegral T k Q u v w S marked L MI]
  exact critical_finite_cut_catalog_half_estimate_regime T MI k Q u v w S marked
    hk hQ hS hbad L hL n c hc hn

lemma weighted_finiteCutCatalogCount_half_estimate (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop,
      (∫⁻ X, ENNReal.ofReal D * finiteCutCatalogCount T k Q u v w S marked L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  obtain ⟨C, hC, hb⟩ := finiteCutCatalogCount_half_estimate T k Q u v w S marked L
    MI hk hQ hS hbad hL n c hc hn
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  filter_upwards [hb] with g hg
  rw [lintegral_const_mul _ (finiteCutCatalogCount_measurable T k Q u v w S marked L MI g (n g))]
  calc
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := mul_le_mul' le_rfl hg
    _ = ENNReal.ofReal (D * C * (g:ℝ)^(-1/2:ℝ)) := by
      rw [← ENNReal.ofReal_mul hD.le, mul_assoc]

/- Internal consumer: the ordinary hdom is precisely the finite-recording
obligation still to be supplied by the geometry, not a classical premise. -/
lemma count_half_estimate_of_finite_cut_catalog
    (D : ℝ) (hD : 0 < D)
    (N : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hdom : ∀ᶠ g in atTop, ∀ X, N g X ≤
      ENNReal.ofReal D * finiteCutCatalogCount T k Q u v w S marked L X) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop,
      (∫⁻ X, N g X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  obtain ⟨C, hC, hb⟩ := weighted_finiteCutCatalogCount_half_estimate
    T k Q u v w S marked L MI hk hQ hS hbad hL n c hc hn D hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdom, hb] with g hd hb
  exact (lintegral_mono hd).trans hb

lemma event_half_estimate_of_finite_cut_catalog
    (D : ℝ) (hD : 0 < D)
    (A : (g : ℕ) → Set (G.Moduli g (n g) (fun _ => 0)))
    (hdom : ∀ᶠ g in atTop, ∀ X ∈ A g, 1 ≤
      ENNReal.ofReal D * finiteCutCatalogCount T k Q u v w S marked L X) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop,
      wpProbability G g (n g) (A g) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  refine WP.Probability.outer_probability_rate_of_majorant
    (fun g => wpProbability G g (n g)) A
    (fun _ X => ENNReal.ofReal D * finiteCutCatalogCount T k Q u v w S marked L X)
    (fun g => (g:ℝ)^(-1/2:ℝ)) ?_ hdom ?_
  · exact Eventually.of_forall (fun g =>
      (measurable_const.mul (finiteCutCatalogCount_measurable
        T k Q u v w S marked L MI g (n g))).aemeasurable)
  · exact weighted_finiteCutCatalogCount_half_estimate
      T k Q u v w S marked L MI hk hQ hS hbad hL n c hc hn D hD

end WP.Critical
