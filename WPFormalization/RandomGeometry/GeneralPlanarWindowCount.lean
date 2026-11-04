import WPFormalization.RandomGeometry.GeneralPlanarOrbitDecomposition
import WPFormalization.RandomGeometry.ShortCurveTopologicalBound
import WPFormalization.RandomGeometry.PantsWindowIntegrability

/-! Literal finite ordered counts for variable planar cusp types, with genuine
uniform finite moments justified by the actual primitive catalog. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n r : ℕ}

def generalPlanarWindowCount (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (I : Fin r → Set ℝ) : ℕ :=
  Nat.card {γ : OrderedGeneralPlanarTuple (H:=H) X k L // ∀i, H.length (γ.val i) ∈ I i}

lemma generalPlanarTupleWindowSum_test_eq_count (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (I : Fin r → Set ℝ) :
    generalPlanarTupleWindowSum (H:=H) X k L (pantsWindowTest I) = (generalPlanarWindowCount H X k L I : ℝ≥0∞) := by
  classical
  let p := fun γ : OrderedGeneralPlanarTuple (H:=H) X k L => ∀i, H.length (γ.val i) ∈ I i
  have hs := tsum_subtype {γ : OrderedGeneralPlanarTuple (H:=H) X k L | p γ} (fun _ => (1 : ℝ≥0∞))
  let e : {γ : OrderedGeneralPlanarTuple (H:=H) X k L | p γ} ≃
      {γ : OrderedGeneralPlanarTuple (H:=H) X k L // p γ} := Equiv.refl _
  calc
    _ = ∑' γ : OrderedGeneralPlanarTuple (H:=H) X k L,
        ({γ : OrderedGeneralPlanarTuple (H:=H) X k L | p γ}).indicator (fun _ => (1 : ℝ≥0∞)) γ := by
      apply tsum_congr
      intro γ
      by_cases hp : p γ <;> simp [pantsWindowTest,Set.indicator,p,hp]
    _ = ∑' _ : {γ : OrderedGeneralPlanarTuple (H:=H) X k L | p γ}, (1 : ℝ≥0∞) := hs.symm
    _ = ∑' _ : {γ : OrderedGeneralPlanarTuple (H:=H) X k L // p γ}, (1 : ℝ≥0∞) :=
      e.tsum_eq (fun _ => (1 : ℝ≥0∞))
    _ = _ := by rw [tsum_fintype]; simp [generalPlanarWindowCount,Nat.card_eq_fintype_card,p]


lemma generalPlanarTuple_card_le_primitive_pow (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) :
    Nat.card (OrderedGeneralPlanarTuple (H:=H) X k L)≤(H.primitiveCount X L)^r := by
  classical
  let f : OrderedGeneralPlanarTuple (H:=H) X k L →
      (Fin r → {γ // γ∈H.shortPrimitive X L}) := fun γ i =>
    ⟨γ.val i,(H.mem_shortPrimitive X L _).2
      (((H.mem_shortPlanar X (k i) L _).1 (γ.property.2 i)).1)⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc
    _ ≤ Nat.card (Fin r → {γ //γ∈H.shortPrimitive X L}) := Nat.card_le_card_of_injective f hi
    _ = _ := by simp [Nat.card_eq_fintype_card,H.primitiveCount_eq_card]

lemma generalPlanarWindowCount_le_pow (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ)
    (L : ℝ) (hL : L<2*Real.arsinh 1) (I : Fin r → Set ℝ) :
    generalPlanarWindowCount H X k L I≤(3*g+n-3)^r := by
  unfold generalPlanarWindowCount
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    ((generalPlanarTuple_card_le_primitive_pow H X k L).trans
      (Nat.pow_le_pow_left (short_primitive_count_le T C L hL X) r))

lemma generalPlanarWindowCount_measurable (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1≤g) (k : Fin r → ℕ) (L : ℝ) (hL : L<2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => (generalPlanarWindowCount H X k L I : ℝ)) := by
  have hm : Measurable (fun X : G.Moduli g n (fun _ => 0) =>
    ∑'o : GeneralPlanarOrbit T g n r k,T.orbitSum o.val (pantsWindowTest I) X) :=
    Measurable.ennreal_tsum (fun o => MI.orbitSum_measurable o.val _ (pantsWindowTest_measurable I hI))
  have he : (fun X : G.Moduli g n (fun _ => 0) =>
    ∑'o : GeneralPlanarOrbit T g n r k,T.orbitSum o.val (pantsWindowTest I) X) =
      fun X => (generalPlanarWindowCount H X k L I : ℝ≥0∞) := by
    funext X
    exact (generalPlanar_weighted_orbit_sum T C hg X k L hL _ (pantsWindowTest_support I L hsub)).trans
      (generalPlanarTupleWindowSum_test_eq_count H X k L I)
  rw [he] at hm
  simpa using hm.ennreal_toReal

lemma generalPlanarWindowCount_memLp (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1≤g) (k : Fin r → ℕ) (L : ℝ) (hL : L<2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) (μ : Measure (G.Moduli g n (fun _ => 0)))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun X => (generalPlanarWindowCount H X k L I : ℝ)) p μ := by
  apply MemLp.of_bound
    (generalPlanarWindowCount_measurable H T C MI hg k L hL I hI hsub).aestronglyMeasurable
    (((3*g+n-3)^r : ℕ) : ℝ)
  filter_upwards [] with X
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤(generalPlanarWindowCount H X k L I : ℝ) by positivity)]
  exact Nat.cast_le.mpr (generalPlanarWindowCount_le_pow H T C X k L hL I)

lemma generalPlanarWindowCount_integrable (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1≤g) (k : Fin r → ℕ) (L : ℝ) (hL : L<2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hsub : ∀i,I i⊆Set.Icc 0 L) (μ : Measure (G.Moduli g n (fun _ => 0)))
    [IsFiniteMeasure μ] : Integrable (fun X => (generalPlanarWindowCount H X k L I : ℝ)) μ :=
  memLp_one_iff_integrable.mp (generalPlanarWindowCount_memLp H T C MI hg k L hL I hI hsub μ 1)
end WP.RandomGeometry
