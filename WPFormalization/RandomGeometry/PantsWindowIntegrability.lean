import WPFormalization.RandomGeometry.PantsOrderedMoments
import WPFormalization.RandomGeometry.PantsMixedFactorialCount

/-! Finite genuine moments of the actual window counts. These estimates justify
passing between real integrals and nonnegative factorial moments. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n r : ℕ}

lemma wpProbability_isFinite (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) :
    IsFiniteMeasure (wpProbability G g n) := by
  constructor
  change (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
    G.wpMeasure g n (fun _ => 0) Set.univ < ⊤
  by_cases h0 : G.wpMeasure g n (fun _ => 0) Set.univ=0
  · simp [h0]
  by_cases ht : G.wpMeasure g n (fun _ => 0) Set.univ=⊤
  · simp [ht]
  rw [ENNReal.inv_mul_cancel h0 ht]
  exact ENNReal.one_lt_top

lemma pantsWindowCount_le_factorial (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : Fin r → Set ℝ) :
    pantsWindowCount H X L I ≤ (H.pantsCount X L).descFactorial r := by
  unfold pantsWindowCount
  calc
    _ ≤ Nat.card (H.OrderedPlanarTuple X 2 L r) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := H.orderedPantsTuple_card X L r

lemma pantsWindowCount_le_pow (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (hg : 1 ≤ g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) : pantsWindowCount H X L I ≤ n^r := by
  have hb := short_pants_count_bound T C hg L hL X
  have hn : H.pantsCount X L ≤ n := by omega
  exact (pantsWindowCount_le_factorial H X L I).trans
    ((Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left hn r))

lemma pantsWindowCount_measurable_all_orders (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => (pantsWindowCount H X L I : ℝ)) := by
  by_cases hr : r=0
  · subst r
    simp_rw [pantsWindowCount_zero G H]
    exact measurable_const
  · exact pantsWindowCount_measurable H T C MI hg (by omega) L hL I hI hsub

lemma pantsWindowCount_memLp (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L)
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun X => (pantsWindowCount H X L I : ℝ)) p μ := by
  apply MemLp.of_bound
    (pantsWindowCount_measurable_all_orders H T C MI hg L hL I hI hsub).aestronglyMeasurable
    ((n^r : ℕ) : ℝ)
  filter_upwards [] with X
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (pantsWindowCount H X L I : ℝ) by positivity)]
  exact Nat.cast_le.mpr (pantsWindowCount_le_pow H T C hg X L hL I)

lemma pantsWindowCount_integrable (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L)
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] :
    Integrable (fun X => (pantsWindowCount H X L I : ℝ)) μ :=
  memLp_one_iff_integrable.mp (pantsWindowCount_memLp H T C MI hg L hL I hI hsub μ 1)

lemma pantsWindowCount_lintegral_eq_ofReal_integral (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L)
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] :
    (∫⁻ X, (pantsWindowCount H X L I : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (∫ X, (pantsWindowCount H X L I : ℝ) ∂μ) := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (pantsWindowCount_integrable H T C MI hg L hL I hI hsub μ)
    (Filter.Eventually.of_forall (fun X =>
      show 0 ≤ (pantsWindowCount H X L I : ℝ) by positivity))
  simpa using h.symm

lemma pants_mixed_factorial_integrable {ι : Type*} [Fintype ι]
    (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : ι → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L)
    (a : ι → ℕ) (hdis : Pairwise (fun j k => Disjoint (I j) (I k)))
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] :
    Integrable (fun X => ∏j,
      ((pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ)) μ := by
  simp_rw [pants_mixed_factorial_eq_expandedWindowCount_real H _ L I a hdis]
  exact pantsWindowCount_integrable H T C MI hg L hL (expandedWindows a I)
    (fun i => hI _) (fun i => hsub _) μ

lemma pants_mixed_factorial_lintegral_eq_ofReal_integral {ι : Type*} [Fintype ι]
    (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : ι → Set ℝ) (hI : ∀i, MeasurableSet (I i))
    (hsub : ∀i, I i ⊆ Set.Icc 0 L)
    (a : ι → ℕ) (hdis : Pairwise (fun j k => Disjoint (I j) (I k)))
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] :
    (∫⁻ X, ∏j, ((pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (∫ X, ∏j,
        ((pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ) ∂μ) := by
  simp_rw [pants_mixed_factorial_eq_expandedWindowCount_real H _ L I a hdis,
    pants_mixed_factorial_eq_expandedWindowCount_ennreal H _ L I a hdis]
  exact pantsWindowCount_lintegral_eq_ofReal_integral H T C MI hg L hL
    (expandedWindows a I) (fun i => hI _) (fun i => hsub _) μ

end WP.RandomGeometry
