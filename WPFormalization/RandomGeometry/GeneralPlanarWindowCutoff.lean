import WPFormalization.RandomGeometry.GeneralPlanarWindowCount

/-! A bounded-window count is independent of any complete catalog cutoff
containing its windows. This keeps mixed counts independent of their moment order. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External Set
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n r : ℕ}

lemma generalPlanarWindowCount_cutoff_eq (X : G.Moduli g n (fun _=>0))
    (k : Fin r→ℕ) (I : Fin r→Set ℝ) (L₁ L₂ : ℝ)
    (h₁ : ∀i,I i⊆Icc 0 L₁) (h₂ : ∀i,I i⊆Icc 0 L₂) :
    generalPlanarWindowCount H X k L₁ I=generalPlanarWindowCount H X k L₂ I := by
  classical
  let f : {γ : OrderedGeneralPlanarTuple (H:=H) X k L₁ //∀i,H.length (γ.val i)∈I i}→
      {γ : OrderedGeneralPlanarTuple (H:=H) X k L₂ //∀i,H.length (γ.val i)∈I i} := fun γ=>
    ⟨⟨γ.val.val,γ.val.property.1,fun i=>(H.mem_shortPlanar X (k i) L₂ _).mpr
      ⟨(h₂ i (γ.property i)).2,((H.mem_shortPlanar X (k i) L₁ _).mp (γ.val.property.2 i)).2⟩⟩,
      γ.property⟩
  let b : {γ : OrderedGeneralPlanarTuple (H:=H) X k L₂ //∀i,H.length (γ.val i)∈I i}→
      {γ : OrderedGeneralPlanarTuple (H:=H) X k L₁ //∀i,H.length (γ.val i)∈I i} := fun γ=>
    ⟨⟨γ.val.val,γ.val.property.1,fun i=>(H.mem_shortPlanar X (k i) L₁ _).mpr
      ⟨(h₁ i (γ.property i)).2,((H.mem_shortPlanar X (k i) L₂ _).mp (γ.val.property.2 i)).2⟩⟩,
      γ.property⟩
  exact Nat.card_congr ⟨f,b,(fun _=>rfl),(fun _=>rfl)⟩

end WP.RandomGeometry
