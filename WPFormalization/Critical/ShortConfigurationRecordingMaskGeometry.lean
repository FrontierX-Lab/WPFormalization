import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingWindows
import WPFormalization.Critical.CutMaskedRecordingCount
import WPFormalization.Critical.ShortConfigurationRecordingSelectedCutFibers
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.Critical.PrimitivePacking
open scoped Classical ENNReal
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  {A:AmbientRealization H} (T:MulticurveTopology.{u,v,w,z} G H)
  {g n k:ℕ} (L:ℝ) (X:G.Moduli g n (fun _=>0))

def maskedWindowBase (a:CutMaskedWindowIndex T k L X) : ActualCutWindow T L X (k:=k) :=
  a.elim (fun w=>Sum.inl w.1) (fun w=>Sum.inr w.1)
def maskedWindowMask (a:CutMaskedWindowIndex T k L X) :
    Finset (Fin (actualCutWindowQ T L X (maskedWindowBase T L X a))) := by
  cases a with
  | inl w=>exact w.2
  | inr w=>exact w.2

def maskedWindowSelected (a:CutMaskedWindowIndex T k L X) :
    Finset (Fin (T.cut (actualCutWindowOrbit T L X (maskedWindowBase T L X a))).components) :=
  (maskedWindowMask T L X a).image (actualCutWindowVertices T L X (maskedWindowBase T L X a)).symm

lemma maskedWindowSelected_card_le (a:CutMaskedWindowIndex T k L X) :
    (maskedWindowSelected T L X a).card ≤ 2*k := by
  apply Finset.card_image_le.trans
  apply (Finset.card_le_card (Finset.subset_univ _)).trans
  cases a with
  | inl w=>simp only [card_univ,Fintype.card_fin];change w.1.1.1.val.val ≤ 2*k;have hq:=w.1.1.1.val.isLt;omega
  | inr w=>simp only [card_univ,Fintype.card_fin];change w.1.1.1.val.val ≤ 2*k;have hq:=w.1.1.1.val.isLt;omega

def makeMaskedWindow (a:ActualCutWindow T L X (k:=k))
    (selected:Finset (Fin (T.cut (actualCutWindowOrbit T L X a)).components)) :
    CutMaskedWindowIndex T k L X := by
  cases a with
  | inl w=>exact Sum.inl ⟨w,selected.image (actualCutWindowVertices T L X (Sum.inl w))⟩
  | inr w=>exact Sum.inr ⟨w,selected.image (actualCutWindowVertices T L X (Sum.inr w))⟩

lemma maskedWindowBase_makeMaskedWindow (a:ActualCutWindow T L X (k:=k))
    (selected:Finset (Fin (T.cut (actualCutWindowOrbit T L X a)).components)) :
    maskedWindowBase T L X (makeMaskedWindow T L X a selected)=a := by cases a <;> rfl

variable (RF:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
  CutComponentRealization A T o X κ hκ)

def maskedWindowRealization (a:CutMaskedWindowIndex T k L X) :=
  RF (actualCutWindowOrbit T L X (maskedWindowBase T L X a))
    (actualCutWindowTuple T L X (maskedWindowBase T L X a))
    (actualCutWindow_mem T L X (maskedWindowBase T L X a))

def ActualCutWindowGeometry (K:ℝ) (γ:H.Primitive g n X) (a:ActualCutWindow T L X (k:=k))
    (mask:Finset (Fin (actualCutWindowQ T L X a))) : Prop :=
  (∀c,actualCutWindowVertices T L X a c∈mask→
    (((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model.negativeEuler:ℝ) ≤ K) ∧
  ∃c,actualCutWindowVertices T L X a c∈mask ∧
    (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).point '' intrinsicInterior
        ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model

def MaskedWindowGeometry (K:ℝ) (γ:H.Primitive g n X) (a:CutMaskedWindowIndex T k L X) : Prop :=
  ActualCutWindowGeometry T L X RF K γ
    (maskedWindowBase T L X a) (maskedWindowMask T L X a)

lemma ActualCutWindowGeometry_selected (K:ℝ) (γ:H.Primitive g n X)
    (a:ActualCutWindow T L X (k:=k)) (mask:Finset (Fin (actualCutWindowQ T L X a)))
    (h:ActualCutWindowGeometry T L X RF K γ a mask) :
    (∀c∈mask.image (actualCutWindowVertices T L X a).symm,
      (((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model.negativeEuler:ℝ) ≤ K) ∧
    ∃c∈mask.image (actualCutWindowVertices T L X a).symm,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).point '' intrinsicInterior
        ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model := by
  constructor
  · intro c hc
    obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hc
    apply h.1
    simpa only [Equiv.apply_symm_apply] using hd
  · obtain ⟨c,hc,ht⟩:=h.2
    exact ⟨c,Finset.mem_image.mpr ⟨actualCutWindowVertices T L X a c,hc,by simp⟩,ht⟩

lemma MaskedWindowGeometry_selected (K:ℝ) (γ:H.Primitive g n X)
    (a:CutMaskedWindowIndex T k L X) (h:MaskedWindowGeometry T L X RF K γ a) :
    (∀c∈maskedWindowSelected T L X a,
      (((maskedWindowRealization T L X RF a).piece c).model.negativeEuler:ℝ) ≤ K) ∧
    ∃c∈maskedWindowSelected T L X a,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        ((maskedWindowRealization T L X RF a).piece c).point ''
          intrinsicInterior ((maskedWindowRealization T L X RF a).piece c).model := by
  exact ActualCutWindowGeometry_selected T L X RF K γ
    (maskedWindowBase T L X a) (maskedWindowMask T L X a) h

def MaskedRecordingGeometry (Kmax:ℕ) (K:ℝ) (γ:H.Primitive g n X)
    (a:CutMaskedRecordingIndex T Kmax L X) : Prop := MaskedWindowGeometry T L X RF K γ a.2

lemma intrinsic_selected_curve_card_bound {ι:Type*} {α:Type*}
    (B:ι→BorderedGeometry.{u,v}) (D:∀c,DoublingClassics (B c))
    (project:∀c,(B c).curves.Primitive→α) (selected:Finset ι) (K W:ℝ)
    (hK:∀c∈selected,((B c).negativeEuler:ℝ) ≤ K)
    (s:Finset α)
    (hlift:∀γ∈s,∃c∈selected,∃β,β∈(B c).curves.short W ∧ project c β=γ) :
    s.card ≤ selected.card*primitiveCountBound (4*Real.pi*K) W := by
  let pool:=selectedIntrinsicPrimitivePool B selected W
  have hc:∀γ:s,∃β:pool,project β.val.1 β.val.2=γ.val:=by
    intro γ
    obtain ⟨c,hc,β,hβ,hp⟩:=hlift γ.val γ.property
    exact ⟨⟨⟨c,β⟩,by simp [pool,selectedIntrinsicPrimitivePool,hc,hβ]⟩,hp⟩
  choose lift hlift using hc
  have hi:Function.Injective lift:=by
    intro γ δ h
    apply Subtype.ext
    exact (hlift γ).symm.trans ((congrArg (fun β:pool=>project β.val.1 β.val.2) h).trans (hlift δ))
  have hb:=Fintype.card_le_of_injective lift hi
  exact (show s.card ≤ pool.card by simpa only [Fintype.card_coe] using hb).trans
    (selectedIntrinsicPrimitivePool_card_le B D selected K W hK)

lemma actual_cut_selected_curve_card_bound {o:T.Orbit g n k}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    (R:CutComponentRealization A T o X κ hκ)
    (selected:Finset (Fin (T.cut o).components)) (K W:ℝ)
    (hK:∀c∈selected,((R.piece c).model.negativeEuler:ℝ) ≤ K)
    (s:Finset (H.Primitive g n X)) (hshort:∀γ∈s,H.length γ ≤ W)
    (hselected:∀γ∈s,∃c∈selected,(A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    s.card ≤ selected.card*primitiveCountBound (4*Real.pi*K) W := by
  apply intrinsic_selected_curve_card_bound (fun c=>(R.piece c).model) (fun c=>(R.piece c).double)
    (fun c β=>(A.primitiveEquiv g n X).symm ((R.piece c).primitiveProjection β)) selected K W hK s
  intro γ hγ
  obtain ⟨c,hc,β,hβ,hp,_⟩:=actual_cut_primitive_short_lift_in_selected R selected γ W (hshort γ hγ) (hselected γ hγ)
  exact ⟨c,hc,β,hβ,by rw [hp,Equiv.symm_apply_apply]⟩

lemma MaskedWindowGeometry_makeMaskedWindow (a:ActualCutWindow T L X (k:=k))
    (selected:Finset (Fin (T.cut (actualCutWindowOrbit T L X a)).components))
    (K:ℝ) (γ:H.Primitive g n X)
    (hK:∀c∈selected,(((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model.negativeEuler:ℝ) ≤ K)
    (htrace:∃c∈selected,(A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
      ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).point '' intrinsicInterior
        ((RF (actualCutWindowOrbit T L X a) (actualCutWindowTuple T L X a)
      (actualCutWindow_mem T L X a)).piece c).model) :
    MaskedWindowGeometry T L X RF K γ (makeMaskedWindow T L X a selected) := by
  have hbase:ActualCutWindowGeometry T L X RF K γ a
      (selected.image (actualCutWindowVertices T L X a)):=by
    constructor
    · intro c hc
      obtain ⟨d,hd,he⟩:=Finset.mem_image.mp hc
      have hdc:d=c:=(actualCutWindowVertices T L X a).injective he
      exact hdc ▸ hK d hd
    · obtain ⟨c,hc,ht⟩:=htrace
      exact ⟨c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,ht⟩
  cases a with
  | inl w=>exact hbase
  | inr w=>exact hbase

@[blueprint "ext:short-filling"]
lemma cut_masked_selected_curve_count_le (Kmax:ℕ) (K W:ℝ)
    (s:Finset (H.Primitive g n X)) (hshort:∀γ∈s,H.length γ ≤ W)
    (record:s→CutMaskedRecordingIndex T Kmax L X)
    (hgeom:∀γ:s,MaskedRecordingGeometry T L X RF Kmax K γ.val (record γ)) :
    (s.card:ℝ≥0∞) ≤
      ((2*Kmax*primitiveCountBound (4*Real.pi*K) W*2^(2*Kmax):ℕ):ℝ≥0∞)*
        ∑k∈Finset.Icc 1 Kmax,(badCutFamilyCount T k L X+markedCutFamilyCount T k L X) := by
  apply cut_masked_recording_count_le T Kmax L X s record
    (2*Kmax*primitiveCountBound (4*Real.pi*K) W)
  intro a
  let fiber:Finset s:=univ.filter (fun γ=>record γ=a)
  let sf:Finset (H.Primitive g n X):=fiber.image Subtype.val
  have hcard:Nat.card {γ:s // record γ=a}=sf.card:=by
    rw [Finset.card_image_of_injective fiber Subtype.val_injective]
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,mem_univ,true_and,fiber]
  rw [hcard]
  by_cases he:fiber.Nonempty
  · obtain ⟨γ,hγ⟩:=he
    have hγa:record γ=a:=(Finset.mem_filter.mp hγ).2
    have hkgeom:=MaskedWindowGeometry_selected T L X RF K γ.val a.2 (by
      have hh := hgeom γ
      rw [hγa] at hh
      exact hh)
    have hbound:=actual_cut_selected_curve_card_bound T X
      (maskedWindowRealization T L X RF a.2) (maskedWindowSelected T L X a.2) K W
      hkgeom.1 sf (fun δ hδ=>by
        obtain ⟨β,hβ,rfl⟩:=Finset.mem_image.mp hδ
        exact hshort β.val β.property) (fun δ hδ=>by
        obtain ⟨β,hβ,rfl⟩:=Finset.mem_image.mp hδ
        have hβa:record β=a:=(Finset.mem_filter.mp hβ).2
        exact (MaskedWindowGeometry_selected T L X RF K β.val a.2 (by
          have hh := hgeom β
          rw [hβa] at hh
          exact hh)).2)
    apply hbound.trans
    apply Nat.mul_le_mul_right
    exact (maskedWindowSelected_card_le T L X a.2).trans (Nat.mul_le_mul_left 2 (by have h:=a.1.val.isLt;omega))
  · have hf:fiber=∅:=Finset.not_nonempty_iff_eq_empty.mp he
    simp [sf,hf]
end WP.Critical.ShortConfiguration
