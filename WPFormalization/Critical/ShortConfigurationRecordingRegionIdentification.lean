import WPFormalization.Critical.ShortConfigurationRecordingCutFibers
import WPFormalization.Critical.ShortConfigurationRecordingDiskAvoidance
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry

lemma preconnected_subset_open_of_frontier_avoid {X:Type u} [TopologicalSpace X]
    (U W:Set X) (hU:IsOpen U) (hW:IsPreconnected W)
    (havoid:Disjoint W (frontier U)) (hmeet:(W∩U).Nonempty) : W⊆U := by
  have hcover:W⊆U∪(closure U)ᶜ := by
    intro p hp
    by_cases hu:p∈U
    · exact Or.inl hu
    · right
      intro hc
      apply Set.disjoint_left.mp havoid hp
      exact ⟨hc,by simpa only [hU.interior_eq] using hu⟩
  have hor:=hW.subset_or_subset hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun p hp hn=>hn (subset_closure hp))) hcover
  rcases hor with h|h
  · exact h
  · obtain ⟨p,hpW,hpU⟩:=hmeet
    exact (h hpW (subset_closure hpU)).elim

lemma negativeEuler_le_of_area_le (B:BorderedGeometry.{u,v}) (L:ℝ)
    (harea:(B.surface.area univ).toReal≤4*L) : (B.negativeEuler:ℝ)≤2*L/Real.pi := by
  have hgb:(B.surface.area univ).toReal=2*Real.pi*(B.negativeEuler:ℝ) := by
    rw [B.gauss_bonnet,ENNReal.toReal_ofReal (by positivity)]
  apply (le_div_iff₀ Real.pi_pos).mpr
  rw [hgb] at harea
  nlinarith

lemma singleCurvePiece_negativeEuler_le (B:BorderedGeometry.{u,v})
    (γ:B.curves.Primitive) (S:SingleCurvePieceData B γ) :
    (S.piece.model.negativeEuler:ℝ)≤2*B.curves.length γ/Real.pi :=
  negativeEuler_le_of_area_le S.piece.model _ S.area_le

variable {P:WP.PsiTheory} {G:WP.External.WeilPeterssonGeometry.{u,v} P}
  {H:WP.External.HyperbolicCurveGeometry.{u,v,w} G}
  {A:AmbientRealization H} {T:WP.External.MulticurveTopology.{u,v,w,z} G H}
  {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
  {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}

lemma open_region_eq_actual_cut_piece
    (R:CutComponentRealization A T o X κ hκ)
    (U:Set (A.model g n X).surface.Point) (hUopen:IsOpen U)
    (hUpre:IsPreconnected U) (hUne:U.Nonempty) (hUcut:U⊆cutComplement A κ)
    (hfrontier:frontier U⊆⋃e,(A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))) :
    ∃!c,U=(R.piece c).point '' intrinsicInterior (R.piece c).model := by
  obtain ⟨c,hc,hunique⟩:=cut_realization_unique_piece R U hUne hUpre hUcut
  have heq:U=(R.piece c).point '' intrinsicInterior (R.piece c).model := by
    apply Set.Subset.antisymm hc
    apply preconnected_subset_open_of_frontier_avoid U _ hUopen (R.piece c).image_connected
    · apply Set.disjoint_left.mpr
      intro p hpW hpfront
      obtain ⟨e,he⟩:=Set.mem_iUnion.mp (hfrontier hpfront)
      have hp: p∈cutComplement A κ := by
        rw [R.image_eq] at hpW
        exact hpW.choose
      exact hp e he
    · obtain ⟨p,hp⟩:=hUne
      exact ⟨p,hc hp,hp⟩
  refine ⟨c,heq,?_⟩
  intro d hd
  exact hunique d hd.subset

end WP.Critical.ShortConfiguration
