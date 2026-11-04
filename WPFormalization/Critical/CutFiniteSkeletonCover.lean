import WPFormalization.Critical.CutActualEstimate
noncomputable section
namespace WP.Critical
open WP.External Finset
open scoped Classical
instance {k Q : ℕ} : Finite (CutSkeleton k Q) :=
  Finite.of_injective (fun S : CutSkeleton k Q => S.edgeVertex)
    (by rintro ⟨a⟩ ⟨b⟩ h;cases h;rfl)
noncomputable instance {k Q : ℕ} : Fintype (CutSkeleton k Q) := Fintype.ofFinite _
namespace CutGraphData
variable {n k : ℕ} (D : MulticurveCutData n k)
lemma components_le_twice_edges (hk : 1≤k) (hconn : D.ConnectedWithin univ) :
    D.components≤2*k := by
  calc
    _ = ∑_c : Fin D.components,1 := by simp
    _ ≤ ∑c : Fin D.components,degree D c :=
      sum_le_sum (fun c _ => degree_pos D hk hconn c)
    _ = _ := sum_degree D
end CutGraphData
end WP.Critical
