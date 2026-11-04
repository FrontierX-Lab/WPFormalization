import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments
import WPFormalization.Tight.SpectrumTupleExtensionsIdentification

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H} {g n : ℕ}

/-- The entire actual primitive tight prefix; no simplicity condition. -/
def PrefixCurve (Q : TightGeodesicGeometry G T H)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :=
  {γ : Curve Q X // Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ≤b}

lemma finite_prefix_curve (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    Finite (PrefixCurve Q X b) := by
  apply Finite.of_injective (fun γ : PrefixCurve Q X b=>
    (⟨⟨γ.val,γ.property.1⟩,(Q.mem_shortPrimitive X b _).mpr γ.property.2.2⟩ :
      ↥(Q.shortPrimitive X b)))
  intro γ δ h
  exact Subtype.ext (congrArg (fun e=>e.val.val) h)

def fullPrefixCount (Q : TightGeodesicGeometry G T H)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) : ℕ :=
  Nat.card (PrefixCurve Q X b)

/-- Every curve in the full prefix occurs, and every coordinate lies in it. -/
def EnumeratesFullPrefix (Q : TightGeodesicGeometry G T H)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    {r : ℕ} (Γ : Fin r→Curve Q X) : Prop :=
  ∀γ, (Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ≤b) ↔ ∃i,Γ i=γ

/-- A good tuple enumerates ALL primitive tight curves in the prefix, and its
actual cut has exactly one component after filling the free cusps. -/
def FullPrefixConnected (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) : Prop :=
  ∃r,∃Γ : Fin r→Curve Q X, Q.GoodTuple Γ ∧ EnumeratesFullPrefix Q X b Γ ∧
    ∃o : A.Orbit g 0 r,A.orbitMem o X Γ ∧ (A.cut o).components=1

lemma zero_edge_cut_components_one
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (o : A.Orbit g 0 0) :
    (A.cut o).components=1 := by
  obtain ⟨a,ha⟩ := (A.cut_connected o).1
  have heq : ∀a b : Fin (A.cut o).components,a=b := by
    intro a b
    have hrel := (A.cut_connected o).2 a (Finset.mem_univ _) b (Finset.mem_univ _)
    induction hrel with
    | refl => rfl
    | @tail b c hab hbc ih =>
      rcases hbc with ⟨_,_,e,_⟩
      exact Fin.elim0 e
  have hc : Fintype.card (Fin (A.cut o).components)=1 :=
    Fintype.card_eq_one_iff.mpr ⟨a,fun b=>heq b a⟩
  simpa only [Fintype.card_fin] using hc

lemma exists_full_prefix_enumeration
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    ∃Γ : Fin (fullPrefixCount Q X b)→Curve Q X,
      Function.Injective Γ ∧ EnumeratesFullPrefix Q X b Γ := by
  classical
  let : Finite (PrefixCurve Q X b) := finite_prefix_curve X b
  letI := Fintype.ofFinite (PrefixCurve Q X b)
  let e : Fin (fullPrefixCount Q X b)≃PrefixCurve Q X b :=
    (finCongr (by simp only [fullPrefixCount,Nat.card_eq_fintype_card])).trans
      (Fintype.equivFin (PrefixCurve Q X b)).symm
  refine ⟨fun i=>(e i).val,?_,?_⟩
  · intro i j h
    exact e.injective (Subtype.ext h)
  · intro γ
    constructor
    · intro hγ
      exact ⟨e.symm ⟨γ,hγ⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩
    · rintro ⟨i,rfl⟩
      exact (e i).property

lemma full_prefix_good_of_not_bad
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    {r : ℕ} (Γ : Fin r→Curve Q X) (hΓ : Function.Injective Γ)
    (hall : EnumeratesFullPrefix Q X b Γ) (hbad : ¬BadConfiguration Q X b) :
    WindowTuple Q X (fun _=>0) (fun _=>b) Γ := by
  apply (windowTuple_iff_tightWindowTuple_of_not_bad Q X
    (fun _=>0) (fun _=>b) b (fun _=>le_rfl) hbad Γ).mpr
  refine ⟨hΓ,fun i=>?_⟩
  have hi := (hall (Γ i)).mpr ⟨i,rfl⟩
  exact ⟨hi.1,hi.2.1,(Q.length_pos _).le,hi.2.2⟩

lemma full_prefix_failure_gives_separating
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    (hg : 2≤g) (hbad : ¬BadConfiguration Q X b)
    (hnot : ¬FullPrefixConnected Q A X b) :
    0<fullPrefixCount Q X b ∧
      1≤Nat.card {Γ : Fin (fullPrefixCount Q X b)→Curve Q X //
        SeparatingTuple Q A X (fullPrefixCount Q X b) b Γ} := by
  obtain ⟨Γ,hinj,hall⟩ := exists_full_prefix_enumeration X b
  have hgood := full_prefix_good_of_not_bad X b Γ hinj hall hbad
  obtain ⟨o,ho,_⟩ := A.orbit_partition X Γ (by unfold Stable;omega) hgood.1
  have hne : (A.cut o).components≠1 := fun h=>hnot ⟨_,Γ,hgood.1,hall,o,ho,h⟩
  obtain ⟨c,hc⟩ := (A.cut_connected o).1
  have hcomp : 2≤(A.cut o).components := by have := c.isLt;omega
  have hpos : 0<fullPrefixCount Q X b := by
    by_contra h
    have hz : fullPrefixCount Q X b=0 := by omega
    have hzlemma : ∀r (o : A.Orbit g 0 r),r=0→(A.cut o).components=1 := by
      intro r o hr
      subst r
      exact zero_edge_cut_components_one A o
    exact hne (hzlemma _ o hz)
  refine ⟨hpos,?_⟩
  letI := finite_separating_tuples Q A X (fullPrefixCount Q X b) b
  let : Nonempty {Γ : Fin (fullPrefixCount Q X b)→Curve Q X //
      SeparatingTuple Q A X (fullPrefixCount Q X b) b Γ} :=
    ⟨⟨Γ,hgood.1,⟨o,ho,hcomp⟩,fun i=>(hgood.2 i).2⟩⟩
  exact Nat.succ_le_iff.mpr Nat.card_pos


/-- The prefix is exactly the full actual H.Primitive tight catalogue. -/
def prefixCurveEquivActual
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    PrefixCurve Q X b ≃
      {γ : H.Primitive g n (tightCuspSurface G X) // Q.cuspTight X γ ∧ H.length γ≤b} where
  toFun γ:=⟨Q.cuspPrimitiveEquiv g n X ⟨γ.val,γ.property.1⟩,by
    refine ⟨?_,?_⟩
    · simpa only [TightGeodesicGeometry.cuspTight,Equiv.symm_apply_apply] using γ.property.2.1
    · simpa only [Q.cuspPrimitive_length] using γ.property.2.2⟩
  invFun γ:=⟨((Q.cuspPrimitiveEquiv g n X).symm γ.val).val,
    ((Q.cuspPrimitiveEquiv g n X).symm γ.val).property,γ.property.1,by
      have hl:=Q.cuspPrimitive_length g n X ((Q.cuspPrimitiveEquiv g n X).symm γ.val)
      rw [Equiv.apply_symm_apply] at hl
      exact hl.symm.le.trans γ.property.2⟩
  left_inv γ:=by
    apply Subtype.ext
    exact congrArg (fun p : {c : Curve Q X // Q.primitive c}=>p.val)
      ((Q.cuspPrimitiveEquiv g n X).symm_apply_apply ⟨γ.val,γ.property.1⟩)
  right_inv γ:=Subtype.ext ((Q.cuspPrimitiveEquiv g n X).apply_symm_apply _)

lemma full_prefix_count_eq_actual
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    fullPrefixCount Q X b=Q.cuspTightCount X (Iic b) :=
  Nat.card_congr (prefixCurveEquivActual X b)

def prefixCurveEquivTightWindowOne
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ) :
    PrefixCurve Q X b ≃ {Γ : Fin 1→Curve Q X //
      TightWindowTuple Q X (fun _=>0) (fun _=>b) Γ} where
  toFun γ:=⟨fun _=>γ.val,fun _ _ _=>Subsingleton.elim _ _,
    fun _=>⟨γ.property.1,γ.property.2.1,(Q.length_pos _).le,γ.property.2.2⟩⟩
  invFun Γ:=⟨Γ.val 0,(Γ.property.2 0).1,(Γ.property.2 0).2.1,(Γ.property.2 0).2.2.2⟩
  left_inv γ:=rfl
  right_inv Γ:=by
    apply Subtype.ext
    funext i
    have hi : i=0 := Subsingleton.elim _ _
    rw [hi]

lemma full_prefix_count_eq_good_one_of_not_bad
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    (hbad : ¬BadConfiguration Q X b) :
    fullPrefixCount Q X b=Nat.card {Γ : Fin 1→Curve Q X //
      WindowTuple Q X (fun _=>0) (fun _=>b) Γ} := by
  exact (Nat.card_congr (prefixCurveEquivTightWindowOne X b)).trans
    (Nat.card_congr ((Equiv.refl _).subtypeEquiv (fun Γ=>
      (windowTuple_iff_tightWindowTuple_of_not_bad Q X (fun _=>0) (fun _=>b)
        b (fun _=>le_rfl) hbad Γ).symm)))

lemma one_le_sum_separating_of_full_prefix_failure
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    (hg : 2≤g) (N : ℕ) (hcount : fullPrefixCount Q X b≤N)
    (hbad : ¬BadConfiguration Q X b) (hnot : ¬FullPrefixConnected Q A X b) :
    1≤∑m : Fin N,Nat.card {Γ : Fin (1+m.val)→Curve Q X //
      SeparatingTuple Q A X (1+m.val) b Γ} := by
  obtain ⟨hpos,hsep⟩:=full_prefix_failure_gives_separating A X b hg hbad hnot
  let m : Fin N:=⟨fullPrefixCount Q X b-1,by omega⟩
  have hm : 1+m.val=fullPrefixCount Q X b := by dsimp only [m];omega
  have hterm : 1≤Nat.card {Γ : Fin (1+m.val)→Curve Q X //
      SeparatingTuple Q A X (1+m.val) b Γ} := by
    have hc := congrArg (fun r : ℕ=>Nat.card {Γ : Fin r→Curve Q X //
      SeparatingTuple Q A X r b Γ}) hm
    exact hc.symm ▸ hsep
  exact hterm.trans (Finset.single_le_sum
    (f:=fun i : Fin N=>Nat.card {Γ : Fin (1+i.val)→Curve Q X //
      SeparatingTuple Q A X (1+i.val) b Γ})
    (fun i _=>Nat.zero_le _) (Finset.mem_univ m))

lemma full_prefix_failure_subset_bad_tail_separating
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (b : ℝ)
    (hg : 2≤g) (N : ℕ) :
    {X : TightSurface G g 0 n (fun _=>0) (fun _=>0) | ¬FullPrefixConnected Q A X b} ⊆
      ({X | BadConfiguration Q X b} ∪
        {X | N<Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ}}) ∪
        {X | 1≤∑m : Fin N,Nat.card {Γ : Fin (1+m.val)→Curve Q X //
          SeparatingTuple Q A X (1+m.val) b Γ}} := by
  intro X hX
  by_cases hbad : BadConfiguration Q X b
  · exact Or.inl (Or.inl hbad)
  by_cases htail : N<Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ}
  · exact Or.inl (Or.inr htail)
  · refine Or.inr (one_le_sum_separating_of_full_prefix_failure A X b hg N ?_ hbad hX)
    rw [full_prefix_count_eq_good_one_of_not_bad X b hbad]
    exact le_of_not_gt htail

lemma full_prefix_connected_of_nonpos
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    (hg : 2≤g) (hb : b≤0) : FullPrefixConnected Q A X b := by
  let Γ : Fin 0→Curve Q X:=fun i=>Fin.elim0 i
  have hgood : Q.GoodTuple Γ := by
    refine ⟨?_,?_,?_⟩
    · intro i;exact Fin.elim0 i
    · intro i;exact Fin.elim0 i
    · intro i;exact Fin.elim0 i
  obtain ⟨o,ho,_⟩:=A.orbit_partition X Γ (by unfold Stable;omega) hgood
  refine ⟨0,Γ,hgood,?_,o,ho,zero_edge_cut_components_one A o⟩
  intro γ
  constructor
  · intro h
    exact ((Q.length_pos γ).not_ge (h.2.2.trans hb)).elim
  · rintro ⟨i,_⟩
    exact Fin.elim0 i


lemma full_prefix_connected_not_bad
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) (b : ℝ)
    (hfull : FullPrefixConnected Q A X b) : ¬BadConfiguration Q X b := by
  obtain ⟨r,Γ,hgood,hall,_⟩:=hfull
  rintro (⟨γ,hp,ht,hl,hns⟩|⟨γ,δ,hne,hp,hp',ht,ht',hl,hl',hnd⟩)
  · obtain ⟨i,hi⟩:=(hall γ).mp ⟨hp,ht,hl⟩
    exact hns (hi ▸ (hgood.2.1 i).2.2.1)
  · obtain ⟨i,hi⟩:=(hall γ).mp ⟨hp,ht,hl⟩
    obtain ⟨j,hj⟩:=(hall δ).mp ⟨hp',ht',hl'⟩
    have hij : i≠j := by
      intro h
      apply hne
      rw [←hi,←hj,h]
    exact hnd (by simpa only [hi,hj] using hgood.2.2 i j hij)


end WP.Tight
