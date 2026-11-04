import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingMaskGeometry

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.Critical.PrimitivePacking
open scoped Classical ENNReal

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  {A : AmbientRealization H} (T : MulticurveTopology.{u,v,w,z} G H)
  {g n : ℕ} (Lcut : ℝ) (X : G.Moduli g n (fun _=>0))
  (RF : ∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
    CutComponentRealization A T o X κ hκ)

/-- Ordinary geometry of one actual tuple and its literal masked record.
The selected set and actual cut realization are the production decoders. -/
def MaskedTupleRecordingGeometry (Kmax : ℕ) (E : ℝ) (r : ℕ)
    (Γ : Fin r→H.Primitive g n X) (a : CutMaskedRecordingIndex T Kmax Lcut X) : Prop :=
  (maskedWindowSelected T Lcut X a.2).card≤r ∧
  (∀c∈maskedWindowSelected T Lcut X a.2,
    (((maskedWindowRealization T Lcut X RF a.2).piece c).model.negativeEuler:ℝ)≤E) ∧
  ∀i,(∃e,actualCutWindowTuple T Lcut X (maskedWindowBase T Lcut X a.2) e=Γ i) ∨
    ∃c∈maskedWindowSelected T Lcut X a.2,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X (Γ i))⊆
        ((maskedWindowRealization T Lcut X RF a.2).piece c).point ''
          intrinsicInterior ((maskedWindowRealization T Lcut X RF a.2).piece c).model

/- A literal record fiber is bounded by the actual edge-or-selected-piece
pool. Record existence and the displayed ordinary geometry remain frontend data. -/
@[blueprint "ext:short-filling"]
lemma masked_tuple_recording_fiber_card_le (Kmax : ℕ) (E L : ℝ) (r : ℕ)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀Γ∈s,∀i,H.length (Γ i)≤L)
    (record : s→CutMaskedRecordingIndex T Kmax Lcut X)
    (hgeom : ∀Γ:s,MaskedTupleRecordingGeometry T Lcut X RF Kmax E r Γ.val (record Γ))
    (a : CutMaskedRecordingIndex T Kmax Lcut X) :
    Nat.card {Γ:s // record Γ=a}≤(Kmax+r*primitiveCountBound (4*Real.pi*E) L)^r := by
  let fiber : Finset s:=univ.filter (fun Γ=>record Γ=a)
  let sf : Finset (Fin r→H.Primitive g n X):=fiber.image Subtype.val
  have hcard : Nat.card {Γ:s // record Γ=a}=sf.card := by
    rw [Finset.card_image_of_injective fiber Subtype.val_injective]
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,
      mem_univ,true_and,fiber]
  rw [hcard]
  by_cases he : fiber.Nonempty
  · obtain ⟨Γ,hΓ⟩:=he
    have hΓa : record Γ=a :=(Finset.mem_filter.mp hΓ).2
    have hΓgeom : MaskedTupleRecordingGeometry T Lcut X RF Kmax E r Γ.val a := by
      have hh:=hgeom Γ
      rw [hΓa] at hh
      exact hh
    have hbound:=actual_cut_selected_piece_or_edge_tuple_card_bound
      (maskedWindowRealization T Lcut X RF a.2) (maskedWindowSelected T Lcut X a.2)
      E L hΓgeom.2.1 sf
      (fun δ hδ i=>by
        obtain ⟨β,hβ,rfl⟩:=Finset.mem_image.mp hδ
        exact hshort β.val β.property i)
      (fun δ hδ i=>by
        obtain ⟨β,hβ,rfl⟩:=Finset.mem_image.mp hδ
        have hβa : record β=a :=(Finset.mem_filter.mp hβ).2
        have hh:=hgeom β
        rw [hβa] at hh
        exact hh.2.2 i)
    apply hbound.trans
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add (by have hk:=a.1.val.isLt;omega)
      (Nat.mul_le_mul_right _ hΓgeom.1)
  · have hf : fiber=∅:=Finset.not_nonempty_iff_eq_empty.mp he
    simp [sf,hf]

/-- Pure masked tuple counting: actual finite fibers are counted over the
full literal bad/marked record codomain, including all vertex masks. -/
lemma cut_masked_selected_tuple_count_le (Kmax : ℕ) (E L : ℝ) (r : ℕ)
    (s : Finset (Fin r→H.Primitive g n X))
    (hshort : ∀Γ∈s,∀i,H.length (Γ i)≤L)
    (record : s→CutMaskedRecordingIndex T Kmax Lcut X)
    (hgeom : ∀Γ:s,MaskedTupleRecordingGeometry T Lcut X RF Kmax E r Γ.val (record Γ)) :
    (s.card:ℝ≥0∞)≤
      (((Kmax+r*primitiveCountBound (4*Real.pi*E) L)^r*2^(2*Kmax):ℕ):ℝ≥0∞)*
        ∑k∈Finset.Icc 1 Kmax,
          (badCutFamilyCount T k Lcut X+markedCutFamilyCount T k Lcut X) := by
  apply cut_masked_recording_count_le T Kmax Lcut X s record
    ((Kmax+r*primitiveCountBound (4*Real.pi*E) L)^r)
  exact masked_tuple_recording_fiber_card_le T Lcut X RF Kmax E L r s hshort record hgeom

end WP.Critical.ShortConfiguration
