import WPFormalization.RandomGeometry.GeneralPlanarTypeTail

/-! The finite type-tail sum is exactly the actual event that a planar curve
with at least K+2 cusp labels occurs. Types larger than n cannot occur. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External MeasureTheory Set
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma generalPlanar_count_pos_iff (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ) :
    0<H.planarCount X k L ↔ ∃γ : H.Primitive g n X,H.length γ≤L ∧
      ∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=k := by
  rw [H.planarCount_eq_card,Finset.card_pos]
  exact Finset.nonempty_iff_ne_empty.trans (by
    rw [←Finset.nonempty_iff_ne_empty]
    exact exists_congr (fun γ => H.mem_shortPlanar X k L γ))

lemma generalPlanar_type_tail_pos_iff (X : G.Moduli g n (fun _ => 0)) (K : ℕ) (L : ℝ) :
    0<generalPlanarTypeTailCount H X K L ↔
      ∃γ : H.Primitive g n X,H.length γ≤L ∧
        ∃S : Finset (Fin n),H.planarSide γ=some S ∧ K+2≤S.card := by
  classical
  rw [generalPlanarTypeTailCount,Finset.sum_pos_iff]
  constructor
  · rintro ⟨j,hj,hcurve⟩
    obtain ⟨γ,hγ,S,hS,hcard⟩ := (generalPlanar_count_pos_iff H X _ L).mp hcurve
    exact ⟨γ,hγ,S,hS,by omega⟩
  · rintro ⟨γ,hγ,S,hS,hcard⟩
    have hmax : S.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    let j : ℕ := S.card-(K+2)
    have hj : j∈Finset.range (n-K-1) := Finset.mem_range.mpr (by dsimp [j];omega)
    refine ⟨j,hj,(generalPlanar_count_pos_iff H X _ L).mpr ⟨γ,hγ,S,hS,?_⟩⟩
    dsimp [j]
    omega

end WP.RandomGeometry
