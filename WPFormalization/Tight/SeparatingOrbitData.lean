import WPFormalization.Critical.CutRealizationTransport
import WPFormalization.External.TightMulticurveTopology
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual tight cut-orbit genus assignments. Connected cut incidence bounds
the component count, and the classical cut classifier proves injectivity of
the full genus assignment on a fixed ordered-edge skeleton. -/

noncomputable section
universe u v w z
namespace WP.TightSeparating
open WP.External WP.Critical Finset
open scoped BigOperators
namespace CutGraph
variable {n k : ℕ} (D : MulticurveCutData n k)
def incidenceGraph : SimpleGraph (Fin D.components) :=
  SimpleGraph.fromRel (fun a b => ∃ e : Fin k, D.edgeVertex (e,0)=a ∧ D.edgeVertex (e,1)=b)
local instance : Fintype (incidenceGraph D).edgeSet := Fintype.ofFinite _
lemma incidenceGraph_connected (h : D.ConnectedWithin univ) : (incidenceGraph D).Connected := by
  obtain ⟨c,hc⟩ := h.1
  have : Nonempty (Fin D.components) := ⟨c⟩
  constructor
  intro a b
  have hp := h.2 a (mem_univ a) b (mem_univ b)
  induction hp with
  | refl => exact .rfl
  | @tail b c hab hbc ih =>
    by_cases heq : b=c
    · simpa [heq] using ih
    · apply ih.trans
      apply SimpleGraph.Adj.reachable
      refine ⟨heq,?_⟩
      obtain ⟨_,_,e,he⟩ := hbc
      rcases he with he|he
      · exact Or.inl ⟨e,he⟩
      · exact Or.inr ⟨e,he.2,he.1⟩
lemma incidenceGraph_edges_le : (incidenceGraph D).edgeFinset.card ≤ k := by
  classical
  have hsub : (incidenceGraph D).edgeFinset ⊆
      univ.image (fun e : Fin k => s(D.edgeVertex (e,0), D.edgeVertex (e,1))) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hadj : (incidenceGraph D).Adj a b := SimpleGraph.mem_edgeFinset.mp he
      rcases hadj.2 with ⟨e,he0,he1⟩|⟨e,he0,he1⟩
      · exact mem_image.mpr ⟨e,mem_univ _,by rw [he0,he1]⟩
      · exact mem_image.mpr ⟨e,mem_univ _,by rw [he0,he1]; exact Sym2.eq_swap⟩
  exact (card_le_card hsub).trans ((card_image_le).trans (by simp))
lemma components_le (h : D.ConnectedWithin univ) : D.components ≤ k+1 := by
  have hc := (incidenceGraph_connected D h).card_vert_le_card_edgeSet_add_one
  have he := incidenceGraph_edges_le D
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hc
  omega
end CutGraph
end WP.TightSeparating
namespace WP.TightSeparating
open WP.External WP.Critical Finset
open scoped BigOperators
namespace Orbit
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
  {g k Q : ℕ} (S : CutSkeleton k Q)
abbrev Fixed := {o : A.Orbit g 0 k // Nonempty (S.Realization (A.cut o))}
def realization (o : Fixed A S (g:=g)) : S.Realization (A.cut o.val) := Classical.choice o.property
def genus (o : Fixed A S (g:=g)) : Fin Q → ℕ := (realization A S o).genus
lemma genus_injective : Function.Injective (genus A S (g:=g)) := by
  intro o p he
  change (realization A S o).genus = (realization A S p).genus at he
  have io := (realization A S o).isomorphism
  have ip := (realization A S p).isomorphism
  have hcusps : (realization A S o).cusps = (realization A S p).cusps := by
    funext i
    exact Fin.elim0 i
  have hc : S.cutData (realization A S o).genus (realization A S o).cusps =
      S.cutData (realization A S p).genus (realization A S p).cusps := by rw [he,hcusps]
  rw [hc] at io
  apply Subtype.ext
  exact A.cut_classifies o.val p.val ⟨io.trans ip.symm⟩
lemma boundary_eq (o : Fixed A S (g:=g)) (c : Fin (A.cut o.val).components) :
    (A.cut o.val).boundaryCount c = S.degree ((realization A S o).vertices c) := by
  rw [(realization A S o).boundaryCount_cuspHistogram]
  simp [cutCuspHistogram]
lemma genus_stable (o : Fixed A S (g:=g)) (c : Fin Q) :
    Stable (genus A S o c) (S.degree c) := by
  have hc := A.cut_stable o.val ((realization A S o).vertices.symm c)
  rw [boundary_eq A S o, (realization A S o).vertices.apply_symm_apply] at hc
  exact hc
lemma genus_euler (o : Fixed A S (g:=g)) :
    (∑ c, genus A S o c)+k = g+(Q-1) := by
  have he := A.cut_euler o.val
  have hs := (realization A S o).genus_sum
  have hQ := Fintype.card_congr (realization A S o).vertices
  simp only [Fintype.card_fin] at hQ
  have hne := (A.cut_connected o.val).1
  have hp : 0 < (A.cut o.val).components := by
    obtain ⟨c,hc⟩ := hne
    have := c.isLt
    omega
  change (∑ c, (realization A S o).genus c)+k = _
  rw [hs]
  omega
lemma genus_complexity (o : Fixed A S (g:=g)) :
    (∑ c, complexity (genus A S o c) (S.degree c)) = complexity g 0 := by
  have he := CutGraphData.sum_complexity (A.cut o.val) (A.cut_stable o.val) (A.cut_euler o.val)
  have hterm (c : Fin (A.cut o.val).components) :
      complexity ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) =
      complexity (genus A S o ((realization A S o).vertices c))
        (S.degree ((realization A S o).vertices c)) := by
    rw [boundary_eq A S o]
    simp only [genus,CutSkeleton.Realization.genus,
      (realization A S o).vertices.symm_apply_apply]
  simp_rw [hterm] at he
  exact (Equiv.sum_comp (realization A S o).vertices
    (fun c => complexity (genus A S o c) (S.degree c))).symm.trans he
lemma actual_product_eq (o : Fixed A S (g:=g)) (x : ℝ) :
    (∏ c, markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x) =
      ∏ c, markedF P (genus A S o c) (S.degree c) x := by
  have hterm (c : Fin (A.cut o.val).components) :
      markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x =
      markedF P (genus A S o ((realization A S o).vertices c))
        (S.degree ((realization A S o).vertices c)) x := by
    rw [boundary_eq A S o]
    simp only [genus,CutSkeleton.Realization.genus,
      (realization A S o).vertices.symm_apply_apply]
  simp_rw [hterm]
  exact Equiv.prod_comp (realization A S o).vertices
    (fun c => markedF P (genus A S o c) (S.degree c) x)
def genusFamily (s : Finset (Fixed A S (g:=g))) : Finset (Fin Q → ℕ) := by
  classical
  exact s.image (genus A S)
lemma genusFamily_spec (s : Finset (Fixed A S (g:=g))) :
    ∀ a ∈ genusFamily A S s, (∀ c, Stable (a c) (S.degree c)) ∧
      (∑ c, complexity (a c) (S.degree c)) = complexity g 0 ∧
      (∑ c, a c)+k = g+(Q-1) := by
  classical
  intro a ha
  obtain ⟨o,ho,rfl⟩ := mem_image.mp ha
  exact ⟨genus_stable A S o,genus_complexity A S o,genus_euler A S o⟩
lemma sum_actual_eq_genusFamily (s : Finset (Fixed A S (g:=g))) (x : ℝ) :
    (∑ o ∈ s, ∏ c, markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) x) =
      ∑ a ∈ genusFamily A S s, ∏ c, markedF P (a c) (S.degree c) x := by
  classical
  simp_rw [actual_product_eq A S]
  unfold genusFamily
  rw [sum_image (fun o _ p _ he => genus_injective A S he)]
end Orbit
end WP.TightSeparating
namespace WP.TightSeparating.Orbit
open WP.External WP.Critical Finset
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
  {g k Q : ℕ} (S : CutSkeleton k Q)
lemma fixed_connected (o : Fixed A S (g:=g)) : S.Connected := by
  have h := (realization A S o).isomorphism.connectedWithin univ (A.cut_connected o.val)
  change (S.cutData (realization A S o).genus (realization A S o).cusps).ConnectedWithin univ
  simpa [MulticurveCutData.Isomorphism.vertices] using h
lemma fixed_degree_pos (hk : 1 ≤ k) (o : Fixed A S (g:=g)) (c : Fin Q) :
    1 ≤ S.degree c := S.degree_pos hk (fixed_connected A S o) c
lemma fixed_components_le (o : Fixed A S (g:=g)) : Q ≤ k+1 := by
  have h := CutGraph.components_le (A.cut o.val) (A.cut_connected o.val)
  have he := Fintype.card_congr (realization A S o).vertices
  simp only [Fintype.card_fin] at he
  omega
lemma separating_zero_edges (g : ℕ) :
    (univ : Finset (A.Orbit g 0 0)).filter (fun o => 2 ≤ (A.cut o).components) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro o ho
  have hc := CutGraph.components_le (A.cut o) (A.cut_connected o)
  have hs := (mem_filter.mp ho).2
  omega
end WP.TightSeparating.Orbit
namespace WP.TightSeparating
open WP.External WP.Critical Finset
lemma empty_cut_boundary_sum {k : ℕ} (D : MulticurveCutData 0 k) :
    (∑ c, D.boundaryCount c) = 2*k := by simpa using D.sum_boundaryCount
lemma empty_cut_lengths_nonnegative {k : ℕ} (D : MulticurveCutData 0 k)
    (x : Fin k → ℝ) (hx : ∀ e, 0 ≤ x e) :
    ∀ c i, 0 ≤ D.tightProtectedLengths (fun i => Fin.elim0 i) x c i := by
  intro c i
  unfold MulticurveCutData.tightProtectedLengths
  split
  · rename_i j he
    exact Fin.elim0 j.val
  · exact hx _
lemma empty_cut_lengths_box {k : ℕ} (D : MulticurveCutData 0 k)
    (scale L : ℝ) (x : Fin k → ℝ)
    (hx : ∀ e, 0 ≤ scale*x e ∧ scale*x e ≤ L) :
    ∀ c i, 0 ≤ scale*D.tightProtectedLengths (fun i => Fin.elim0 i) x c i ∧
      scale*D.tightProtectedLengths (fun i => Fin.elim0 i) x c i ≤ L := by
  intro c i
  unfold MulticurveCutData.tightProtectedLengths
  split
  · rename_i j he
    exact Fin.elim0 j.val
  · exact hx _
namespace Orbit
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
lemma actual_cut_budgets {g k : ℕ} (hk : 1 ≤ k) (o : A.Orbit g 0 k) :
    (∀ c, 1 ≤ (A.cut o).boundaryCount c) ∧
    (∑ c, (A.cut o).boundaryCount c) = 2*k ∧
    (∑ c, complexity ((A.cut o).genus c) ((A.cut o).boundaryCount c)) = complexity g 0 ∧
    (∑ c, (A.cut o).genus c)+k = g+((A.cut o).components-1) := by
  refine ⟨CutGraphData.boundaryCount_pos (A.cut o) hk (A.cut_connected o),
    empty_cut_boundary_sum (A.cut o),
    CutGraphData.sum_complexity (A.cut o) (A.cut_stable o) (A.cut_euler o),?_⟩
  have he := A.cut_euler o
  obtain ⟨c,hc⟩ := (A.cut_connected o).1
  have := c.isLt
  omega
end Orbit
end WP.TightSeparating
