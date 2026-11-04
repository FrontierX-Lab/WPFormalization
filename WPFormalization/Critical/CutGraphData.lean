import WPFormalization.External.MirzakhaniIntegration
import WPFormalization.External.MulticurveCutIsomorphism
import WPFormalization.RandomGeometry.CutBoundaryProduct

/-! Actual cut skeletons and their multicurve orbits. Cut classification proves injection into genus and original cusp-label assignments. Connected cut incidence and Euler identities give the exact complexity budgets. -/

noncomputable section
universe u v w z
namespace WP.Critical
open WP.External

/-- A fixed graph with ordered edges and named vertices. Both incidences of
a loop are retained; no simplicity restriction is imposed. -/
structure CutSkeleton (k Q : ℕ) where
  edgeVertex : Fin k×Fin 2→Fin Q

namespace CutSkeleton
variable {k Q n:ℕ} (S : CutSkeleton k Q)

def cutData (a : Fin Q→ℕ) (σ : Fin n→Fin Q) : MulticurveCutData n k where
  components := Q
  genus := a
  cuspVertex := σ
  edgeVertex := S.edgeVertex

/-- Actual incidence agreement, allowing reversal of each unoriented cut. -/
structure Realization (D : MulticurveCutData n k) where
  vertices : Fin D.components≃Fin Q
  flip : Fin k→Bool
  edge_eq : ∀e j,vertices (D.edgeVertex (e,j))=
    S.edgeVertex (e,if flip e then j.rev else j)

variable {S}

def Realization.genus {D : MulticurveCutData n k} (R : S.Realization D) : Fin Q→ℕ :=
  fun c=>D.genus (R.vertices.symm c)

def Realization.cusps {D : MulticurveCutData n k} (R : S.Realization D) : Fin n→Fin Q :=
  fun i=>R.vertices (D.cuspVertex i)

def Realization.isomorphism {D : MulticurveCutData n k} (R : S.Realization D) :
    MulticurveCutData.Isomorphism D (S.cutData R.genus R.cusps) where
  vertexEquiv := R.vertices
  flip := R.flip
  genus_eq c := by
    change D.genus (R.vertices.symm (R.vertices c))=D.genus c
    exact congrArg D.genus (R.vertices.symm_apply_apply c)
  cusp_eq _ := rfl
  edge_eq := R.edge_eq

end CutSkeleton

namespace CutGraphOrbits
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
  {g n k Q:ℕ} (S:CutSkeleton k Q)

/-- These are actual multicurve orbits of the prescribed graph skeleton. -/
def Orbits := {o:T.Orbit g n k // Nonempty (S.Realization (T.cut o))}

noncomputable def realization (o:Orbits T S (g:=g) (n:=n)) : S.Realization (T.cut o.val) :=
  Classical.choice o.property

noncomputable def allocation (o:Orbits T S (g:=g) (n:=n)) :
    (Fin Q→ℕ)×(Fin n→Fin Q) :=
  ((realization T S o).genus,(realization T S o).cusps)

/-- Cut classification turns actual graph orbits into distinct genus and
original-cusp-label assignments. No count of all assignments is assumed. -/
lemma allocation_injective : Function.Injective (allocation T S (g:=g) (n:=n)) := by
  intro o p he
  have ha : (realization T S o).genus=(realization T S p).genus := congrArg Prod.fst he
  have hσ : (realization T S o).cusps=(realization T S p).cusps := congrArg Prod.snd he
  have io := (realization T S o).isomorphism
  have ip := (realization T S p).isomorphism
  have hc : S.cutData (realization T S o).genus (realization T S o).cusps=
      S.cutData (realization T S p).genus (realization T S p).cusps := by rw [ha,hσ]
  rw [hc] at io
  apply Subtype.ext
  exact T.cut_classifies o.val p.val ⟨io.trans ip.symm⟩

end CutGraphOrbits
end WP.Critical
namespace WP.Critical
open WP.External Finset

namespace CutSkeleton
variable {k Q n:ℕ} {S:CutSkeleton k Q} {D:MulticurveCutData n k}

lemma Realization.genus_sum (R:S.Realization D) :
    (∑c:Fin Q,R.genus c)=(∑c:Fin D.components,D.genus c) := by
  exact Equiv.sum_comp R.vertices.symm D.genus

lemma Realization.stable (R:S.Realization D)
    (hs:∀c,Stable (D.genus c) (D.boundaryCount c)) :
    ∀c,Stable (R.genus c) ((S.cutData R.genus R.cusps).boundaryCount c) := by
  intro c
  have hb := R.isomorphism.boundaryCount_eq (R.vertices.symm c)
  change D.boundaryCount (R.vertices.symm c)=
    (S.cutData R.genus R.cusps).boundaryCount (R.vertices (R.vertices.symm c)) at hb
  rw [R.vertices.apply_symm_apply] at hb
  change Stable (D.genus (R.vertices.symm c)) _
  rw [←hb]
  exact hs _

end CutSkeleton
namespace CutGraphOrbits
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
  {g n k Q:ℕ} (S:CutSkeleton k Q)

lemma allocation_euler (o:Orbits T S (g:=g) (n:=n)) :
    (∑c:Fin Q,(allocation T S o).1 c)+k+1=g+Q := by
  have hc := T.cut_euler o.val
  have hs := (realization T S o).genus_sum
  have hQ := Fintype.card_congr (realization T S o).vertices
  simp only [Fintype.card_fin] at hQ
  change (∑c:Fin Q,(realization T S o).genus c)+k+1=g+Q
  rw [hs]
  omega

lemma allocation_genus_le (o:Orbits T S (g:=g) (n:=n)) (c:Fin Q) :
    (allocation T S o).1 c≤g+Q := by
  have hs : (allocation T S o).1 c≤∑i:Fin Q,(allocation T S o).1 i :=
    single_le_sum (fun i _=>Nat.zero_le _) (mem_univ c)
  have he := allocation_euler T S o
  omega

end CutGraphOrbits
end WP.Critical
namespace WP.Critical
open WP.External Finset
namespace CutGraphData
variable {n r:ℕ} (D:MulticurveCutData n r)

def cuspCount (c:Fin D.components) : ℕ := Fintype.card {i:Fin n // D.cuspVertex i=c}
def degree (c:Fin D.components) : ℕ := Fintype.card {e:Fin r×Fin 2 // D.edgeVertex e=c}

lemma boundaryCount_eq (c:Fin D.components) :
    D.boundaryCount c=cuspCount D c+degree D c := by
  exact Fintype.card_sum

lemma sum_cuspCount : (∑c:Fin D.components,cuspCount D c)=n := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv D.cuspVertex)
  simpa [Fintype.card_sigma,cuspCount] using he

lemma sum_degree : (∑c:Fin D.components,degree D c)=2*r := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv D.edgeVertex)
  simpa [Fintype.card_sigma,degree,Nat.mul_comm] using he

lemma edgeVertex_surjective (hr:1≤r) (hconn:D.ConnectedWithin univ) :
    Function.Surjective D.edgeVertex := by
  intro c
  by_contra hnot
  have hiso : ∀e:Fin r×Fin 2,D.edgeVertex e≠c := by simpa only [not_exists] using hnot
  have hpath (b:Fin D.components)
      (hp:Relation.ReflTransGen (D.AdjacentWithin univ) c b) : b=c := by
    induction hp with
    | refl => rfl
    | @tail b d hcb hbd ih =>
      obtain ⟨_,_,e,he⟩ := hbd
      rcases he with he|he
      · exact (hiso (e,0) (he.1.trans ih)).elim
      · exact (hiso (e,1) (he.1.trans ih)).elim
  let e:Fin r×Fin 2 := (⟨0,by omega⟩,0)
  have hc := hpath (D.edgeVertex e) (hconn.2 c (mem_univ c) _ (mem_univ _))
  exact hiso e hc

lemma degree_pos (hr:1≤r) (hconn:D.ConnectedWithin univ) (c:Fin D.components) :
    1≤degree D c := by
  obtain ⟨e,he⟩ := edgeVertex_surjective D hr hconn c
  haveI : Nonempty {e:Fin r×Fin 2 // D.edgeVertex e=c} := ⟨⟨e,he⟩⟩
  exact Fintype.card_pos

lemma boundaryCount_pos (hr:1≤r) (hconn:D.ConnectedWithin univ) (c:Fin D.components) :
    1≤D.boundaryCount c := by
  rw [boundaryCount_eq]
  have hd := degree_pos D hr hconn c
  omega

end CutGraphData
end WP.Critical
namespace WP.Critical
namespace CutGraphData
open WP.External Finset
variable {g n r:ℕ} (D:MulticurveCutData n r)

lemma sum_complexity (hs:∀c,Stable (D.genus c) (D.boundaryCount c))
    (heuler:(∑c:Fin D.components,D.genus c)+r+1=g+D.components) :
    (∑c:Fin D.components,complexity (D.genus c) (D.boundaryCount c))=complexity g n := by
  have he (c:Fin D.components) :
      complexity (D.genus c) (D.boundaryCount c)+2=2*D.genus c+D.boundaryCount c := by
    have hc:=hs c
    unfold Stable complexity at *
    omega
  have hsum := congrArg (fun f:Fin D.components→ℕ=>∑c,f c) (funext he)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,
    ←mul_sum] at hsum
  rw [D.sum_boundaryCount] at hsum
  change (∑c:Fin D.components,complexity (D.genus c) (D.boundaryCount c))=2*g+n-2
  omega

/-- The base complexities before original cusp labels are allocated. The
one-boundary sphere has complexity -1, so this budget must be integral. -/
def baseComplexity (c:Fin D.components) : ℤ := 2*(D.genus c:ℤ)+(degree D c:ℤ)-2

lemma sum_baseComplexity
    (heuler:(∑c:Fin D.components,D.genus c)+r+1=g+D.components) :
    (∑c:Fin D.components,baseComplexity D c)=2*(g:ℤ)-2 := by
  have hdegree := sum_degree D
  have hc := congrArg (fun t:ℕ=>(t:ℤ)) heuler
  have hd := congrArg (fun t:ℕ=>(t:ℤ)) hdegree
  push_cast at hc hd
  simp only [baseComplexity,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,
    Fintype.card_fin,smul_eq_mul,←mul_sum]
  simp only [nsmul_eq_mul]
  push_cast
  linarith

lemma vertex_trichotomy (c:Fin D.components) (hd:1≤degree D c) :
    (D.genus c=0 ∧ degree D c=1) ∨
    (D.genus c=0 ∧ degree D c=2) ∨ 1≤baseComplexity D c := by
  unfold baseComplexity
  omega

lemma leaf_cusp_lower (c:Fin D.components)
    (hs:Stable (D.genus c) (D.boundaryCount c)) :
    (D.genus c=0 → degree D c=1 → 2≤cuspCount D c) ∧
    (D.genus c=0 → degree D c=2 → 1≤cuspCount D c) := by
  rw [boundaryCount_eq] at hs
  unfold Stable at hs
  omega

end CutGraphData
end WP.Critical
