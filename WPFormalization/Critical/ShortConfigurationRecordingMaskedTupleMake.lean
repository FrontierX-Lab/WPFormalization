import WPFormalization.Critical.ShortConfigurationRecordingMaskedTupleCount

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped Classical

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  {A : AmbientRealization H} (T : MulticurveTopology.{u,v,w,z} G H)
  {g n k : ℕ} (Lcut : ℝ) (X : G.Moduli g n (fun _=>0))
  (RF : ∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
    CutComponentRealization A T o X κ hκ)

/-- Encoding a chosen set of components into the literal masked window preserves
its cardinality, Euler bound, and each original tuple coordinate. This is a
pure encoding lemma; all geometric premises are supplied by the caller. -/
lemma MaskedTupleRecordingGeometry_makeMaskedWindow
    (a : ActualCutWindow T Lcut X (k:=k))
    (selected : Finset (Fin (T.cut (actualCutWindowOrbit T Lcut X a)).components))
    (Kmax : ℕ) (hkcap : k≤Kmax) (hkpos : 1≤k)
    (E : ℝ) (r : ℕ) (Γ : Fin r→H.Primitive g n X)
    (hcard : selected.card≤r)
    (hEuler : ∀c∈selected,
      (((RF (actualCutWindowOrbit T Lcut X a) (actualCutWindowTuple T Lcut X a)
        (actualCutWindow_mem T Lcut X a)).piece c).model.negativeEuler:ℝ)≤E)
    (hcoords : ∀i,(∃e,actualCutWindowTuple T Lcut X a e=Γ i) ∨
      ∃c∈selected,(A.model g n X).curves.trace (A.primitiveEquiv g n X (Γ i))⊆
        ((RF (actualCutWindowOrbit T Lcut X a) (actualCutWindowTuple T Lcut X a)
          (actualCutWindow_mem T Lcut X a)).piece c).point '' intrinsicInterior
        ((RF (actualCutWindowOrbit T Lcut X a) (actualCutWindowTuple T Lcut X a)
          (actualCutWindow_mem T Lcut X a)).piece c).model) :
    MaskedTupleRecordingGeometry T Lcut X RF Kmax E r Γ
      ⟨⟨⟨k,by omega⟩,hkpos⟩,makeMaskedWindow T Lcut X a selected⟩ := by
  cases a <;>
    simpa only [MaskedTupleRecordingGeometry,maskedWindowSelected,maskedWindowMask,
      makeMaskedWindow,maskedWindowBase,maskedWindowRealization,
      Sum.elim_inl,Sum.elim_inr,
      Finset.image_image,Function.comp_def,Equiv.symm_apply_apply,Finset.image_id,Finset.image_id']
      using (And.intro hcard (And.intro hEuler hcoords))

end WP.Critical.ShortConfiguration
