import WPFormalization.RandomGeometry.GeneralPlanarWindowCount
import WPFormalization.RandomGeometry.GeneralPlanarStarWindowMoments

/-! Genuine finite actual moments split into the exact star integral and a
nonnegative, explicitly retained actual nonstar contribution. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

include C in
lemma generalPlanar_window_ennreal_decomposition (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hsub : ∀i,I i⊆Set.Icc 0 L) :
    (generalPlanarWindowCount H X k L I : ℝ≥0∞) =
      generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X +
        generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X := by
  rw [←generalPlanarTupleWindowSum_test_eq_count H X k L I]
  exact generalPlanar_actual_star_remainder T C hg X k L hL _ (pantsWindowTest_support I L hsub)

include C in
lemma generalPlanar_star_le_count (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hsub : ∀i,I i⊆Set.Icc 0 L) :
    generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X≤
      (generalPlanarWindowCount H X k L I : ℝ≥0∞) := by
  rw [generalPlanar_window_ennreal_decomposition H T C hg X k L hL I hsub]
  exact le_self_add

include C in
lemma generalPlanar_remainder_le_count (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hsub : ∀i,I i⊆Set.Icc 0 L) :
    generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X≤
      (generalPlanarWindowCount H X k L I : ℝ≥0∞) := by
  rw [generalPlanar_window_ennreal_decomposition H T C hg X k L hL I hsub]
  exact le_add_self

include MI in
lemma generalPlanarStarWindowSum_measurable (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i)) :
    Measurable (generalPlanarStarWindowSum T g n r k (pantsWindowTest I)) :=
  Measurable.ennreal_tsum (fun o => MI.orbitSum_measurable o.val _ (pantsWindowTest_measurable I hI))

include MI in
lemma generalPlanarRemainderWindowSum_measurable (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i)) :
    Measurable (generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I)) :=
  Measurable.ennreal_tsum (fun o => MI.orbitSum_measurable o.val.val _ (pantsWindowTest_measurable I hI))

lemma nat_bounded_ennreal_memLp {A : Type*} [MeasurableSpace A]
    (f : A → ℝ≥0∞) (hf : Measurable f) (B : ℕ) (hb : ∀x,f x≤(B : ℝ≥0∞))
    (μ : Measure A) [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp (fun x => (f x).toReal) p μ := by
  apply MemLp.of_bound hf.ennreal_toReal.aestronglyMeasurable (B : ℝ)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono (by simp : (B : ℝ≥0∞)≠⊤) (hb x)

include C MI in
lemma generalPlanarStarWindowSum_memLp (hg : 1≤g) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) (μ : Measure (G.Moduli g n (fun _ => 0)))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun X => (generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X).toReal) p μ := by
  apply nat_bounded_ennreal_memLp _ (generalPlanarStarWindowSum_measurable H T MI k I hI) ((3*g+n-3)^r)
  intro X
  exact (generalPlanar_star_le_count H T C hg X k L hL I hsub).trans
    (Nat.cast_le.mpr (generalPlanarWindowCount_le_pow H T C X k L hL I))

include C MI in
lemma generalPlanarRemainderWindowSum_memLp (hg : 1≤g) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) (μ : Measure (G.Moduli g n (fun _ => 0)))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun X => (generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X).toReal) p μ := by
  apply nat_bounded_ennreal_memLp _ (generalPlanarRemainderWindowSum_measurable H T MI k I hI) ((3*g+n-3)^r)
  intro X
  exact (generalPlanar_remainder_le_count H T C hg X k L hL I hsub).trans
    (Nat.cast_le.mpr (generalPlanarWindowCount_le_pow H T C X k L hL I))

include C MI in
lemma generalPlanar_actual_moment_decomposition (hg : 2≤g)
    (k : Fin r → ℕ) (hk : ∀i,2≤k i) (hgn : (g,n)≠(2,0)) (L : ℝ)
    (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0),(generalPlanarWindowCount H X k L I : ℝ) ∂wpProbability G g n) =
      generalPlanarStarWindowCut P g n r k I +
        ∫X,(generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X).toReal ∂wpProbability G g n := by
  let μ := wpProbability G g n
  letI := wpProbability_isFinite G g n
  have h1 : 1≤g := by omega
  have hsfinite : ∀X,generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X≠⊤ := by
    intro X
    exact ne_top_of_le_ne_top (by simp : (generalPlanarWindowCount H X k L I : ℝ≥0∞)≠⊤)
      (generalPlanar_star_le_count H T C h1 X k L hL I hsub)
  have hrfinite : ∀X,generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X≠⊤ := by
    intro X
    exact ne_top_of_le_ne_top (by simp : (generalPlanarWindowCount H X k L I : ℝ≥0∞)≠⊤)
      (generalPlanar_remainder_le_count H T C h1 X k L hL I hsub)
  have hsint := memLp_one_iff_integrable.mp
    (generalPlanarStarWindowSum_memLp H T C MI h1 k L hL I hI hsub μ 1)
  have hrint := memLp_one_iff_integrable.mp
    (generalPlanarRemainderWindowSum_memLp H T C MI h1 k L hL I hI hsub μ 1)
  have he : (fun X : G.Moduli g n (fun _ => 0) => (generalPlanarWindowCount H X k L I : ℝ)) =
      fun X => (generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X).toReal +
        (generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X).toReal := by
    funext X
    have h := congrArg ENNReal.toReal (generalPlanar_window_ennreal_decomposition H T C h1 X k L hL I hsub)
    simpa only [ENNReal.toReal_natCast,ENNReal.toReal_add (hsfinite X) (hrfinite X)] using h
  rw [he,integral_add hsint hrint]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun X => ENNReal.toReal_nonneg))
    (generalPlanarStarWindowSum_measurable H T MI k I hI).ennreal_toReal.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_toReal (hsfinite _)]
  exact generalPlanarStar_windows_moment_toReal G H T MI k hg hk hgn I hI
    (fun i x hx => (hsub i hx).1)
end WP.RandomGeometry
