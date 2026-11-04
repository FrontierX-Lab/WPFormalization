import WPFormalization.Tight.SpectrumPrefixConnected
import WPFormalization.Tight.SpectrumTupleExtensionsMeasurability
import WPFormalization.Tight.SpectrumTupleExtensionsOrbitSum
/- The complete prefix connectedness event is Borel. Its characterization
uses the actual full primitive tight cardinality and the actual connected
ordered tuple count, rather than adding a measurability interface field. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H} {g n : ℕ}

lemma finite_connected_prefix_tuples (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (r : ℕ) (b : ℝ) :
    Finite {Γ : Fin r→Curve Q X // ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ} := by
  letI:=finite_window_tuples Q X (fun _ : Fin r=>0) (fun _=>b) b (fun _=>le_rfl)
  apply Finite.of_injective (fun Γ : {Γ : Fin r→Curve Q X //
    ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ}=>
    (⟨Γ.val,Γ.property.1⟩ : {Γ : Fin r→Curve Q X //WindowTuple Q X (fun _=>0) (fun _=>b) Γ}))
  intro Γ Δ h
  exact Subtype.ext (Subtype.mk.inj h)

lemma full_prefix_connected_iff_count (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    FullPrefixConnected Q A X b ↔ ∃r : ℕ,fullPrefixCount Q X b=r ∧
      0<(Nat.card {Γ : Fin r→Curve Q X //ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ} : ℝ≥0∞) := by
  classical
  letI : Finite (PrefixCurve Q X b):=finite_prefix_curve (Q:=Q) X b
  constructor
  · rintro ⟨r,Γ,hgood,hall,horbit⟩
    let f : Fin r→PrefixCurve Q X b:=fun i=>⟨Γ i,(hall (Γ i)).mpr ⟨i,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j h
        exact hgood.1 (congrArg (fun γ : PrefixCurve Q X b=>γ.val) h)
      · intro γ
        obtain ⟨i,hi⟩:=(hall γ.val).mp γ.property
        exact ⟨i,Subtype.ext hi⟩
    have hc : fullPrefixCount Q X b=r := by
      simpa only [Nat.card_fin,fullPrefixCount] using (Nat.card_eq_of_bijective f hf).symm
    have hΓ : ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ := by
      refine ⟨⟨hgood,fun i=>⟨(Q.length_pos _).le,?_⟩⟩,horbit⟩
      exact ((hall (Γ i)).mpr ⟨i,rfl⟩).2.2
    have hn : 0<Nat.card {Δ : Fin r→Curve Q X //ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Δ} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨Γ,hΓ⟩⟩,finite_connected_prefix_tuples A X r b⟩
    exact ⟨r,hc,by exact_mod_cast hn⟩
  · rintro ⟨r,hc,hpos⟩
    have hn : 0<Nat.card {Γ : Fin r→Curve Q X //ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ} :=
      by exact_mod_cast hpos
    obtain ⟨Γ⟩:=(Nat.card_pos_iff.mp hn).1
    let f : Fin r→PrefixCurve Q X b:=fun i=>⟨Γ.val i,
      (Γ.property.1.1.2.1 i).1,(Γ.property.1.1.2.1 i).2.1,(Γ.property.1.2 i).2⟩
    have hf : Function.Bijective f := by
      apply (Nat.bijective_iff_injective_and_card f).mpr
      refine ⟨?_,?_⟩
      · intro i j h
        exact Γ.property.1.1.1 (congrArg (fun γ : PrefixCurve Q X b=>γ.val) h)
      · simpa only [Nat.card_fin,fullPrefixCount] using hc.symm
    refine ⟨r,Γ.val,Γ.property.1.1,?_,Γ.property.2⟩
    intro γ
    constructor
    · intro hγ
      obtain ⟨i,hi⟩:=hf.2 ⟨γ,hγ⟩
      exact ⟨i,congrArg (fun δ : PrefixCurve Q X b=>δ.val) hi⟩
    · rintro ⟨i,rfl⟩
      exact (f i).property

lemma measurableSet_full_prefix_connected (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (hg : 2≤g)
    (BM : TightGeodesicBorelModel G T H Q g n hg) (b : ℝ) :
    MeasurableSet {X : TightSurface G g 0 n (fun _=>0) (fun _=>0) | FullPrefixConnected Q A X b} := by
  have hN : Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>fullPrefixCount Q X b) := by
    convert measurable_actual_tight_count BM (Iic b) measurableSet_Iic using 1
    funext X
    exact full_prefix_count_eq_actual X b
  have hC (r : ℕ) : Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
      (Nat.card {Γ : Fin r→Curve Q X //ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ} : ℝ≥0∞)) := by
    have hm : Measurable (fun X : TightSurface G g 0 n (fun _=>0) (fun _=>0)=>
      ∑o ∈ Finset.univ.filter (fun o : A.Orbit g 0 r=>(A.cut o).components=1),
        A.orbitSum o ((Icc (fun _ : Fin r=>0) (fun _=>b)).indicator (fun _=>1)) X) := by
      apply Finset.measurable_sum
      intro o ho
      exact MI.orbitSum_measurable o _ _ _ (measurable_const.indicator measurableSet_Icc)
    convert hm using 1
    funext X
    exact connected_window_count_eq_orbit_sum Q A X (fun _ : Fin r=>0) (fun _=>b) b
      (fun _=>le_rfl) (by unfold Stable;omega)
  have he : {X : TightSurface G g 0 n (fun _=>0) (fun _=>0) | FullPrefixConnected Q A X b}=
      ⋃r : ℕ,{X |fullPrefixCount Q X b=r} ∩
        {X |0<(Nat.card {Γ : Fin r→Curve Q X //ConnectedWindowTuple Q A X (fun _=>0) (fun _=>b) Γ} : ℝ≥0∞)} := by
    ext X
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
    exact full_prefix_connected_iff_count A X b
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  exact (measurableSet_eq_fun hN measurable_const).inter (measurableSet_lt measurable_const (hC r))

end WP.Tight
