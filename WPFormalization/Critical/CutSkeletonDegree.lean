import WPFormalization.Critical.CutGraphData
import WPFormalization.Critical.CutCuspLabels

/-! Fixed-skeleton degree and connectedness, with the exact original-cusp histogram in each canonical component boundary count. -/

noncomputable section
namespace WP.Critical.CutSkeleton
open WP.External Finset
variable {k Q:ℕ} (S:CutSkeleton k Q)

def emptyCuspData : MulticurveCutData 0 k := S.cutData (fun _=>0) Fin.elim0

def degree (c:Fin Q) : ℕ := CutGraphData.degree S.emptyCuspData c

def Connected : Prop := S.emptyCuspData.ConnectedWithin univ

lemma degree_pos (hk:1≤k) (hS:S.Connected) (c:Fin Q) : 1≤S.degree c :=
  CutGraphData.degree_pos S.emptyCuspData hk hS c

lemma sum_degree : (∑c:Fin Q,S.degree c)=2*k := CutGraphData.sum_degree S.emptyCuspData

lemma boundaryCount_cuspHistogram {n:ℕ} (a:Fin Q→ℕ) (σ:Fin n→Fin Q) (c:Fin Q) :
    (S.cutData a σ).boundaryCount c=cutCuspHistogram σ c+S.degree c := by
  change Fintype.card ({i:Fin n // σ i=c} ⊕ {e:Fin k×Fin 2 // S.edgeVertex e=c})=_
  rw [Fintype.card_sum,cutCuspHistogram_eq_card]
  rfl

end WP.Critical.CutSkeleton
