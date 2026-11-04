import WPFormalization.External.MulticurveCutIsomorphism
import WPFormalization.External.BuddLionsTightIntegration
import WPFormalization.Tight.SeparatingPositiveProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace WP.TightConnected
open Set Filter Finset External MeasureTheory
open scoped Topology BigOperators ENNReal

/- An exact labelled connected cut.  Every edge is a loop at the sole
vertex and both of its oriented sides are retained. -/
def connectedCutData (g k : ℕ) : MulticurveCutData 0 k where
  components := 1
  genus := fun _ => g-k
  cuspVertex := Fin.elim0
  edgeVertex := fun _ => 0

lemma connectedCutData_connected (g k : ℕ) :
    (connectedCutData g k).ConnectedWithin univ := by
  unfold MulticurveCutData.ConnectedWithin
  dsimp only [connectedCutData]
  refine ⟨⟨0, mem_univ _⟩, ?_⟩
  intro a ha b hb
  change Fin 1 at a b
  have : a=b := Subsingleton.elim _ _
  subst b
  exact .refl

lemma connectedCutData_boundaryCount (g k : ℕ) (c : Fin 1) :
    (connectedCutData g k).boundaryCount c = 2*k := by
  classical
  have hc : c=0 := Subsingleton.elim _ _
  subst c
  change Fintype.card ({i : Fin 0 // Fin.elim0 i = (0:Fin 1)} ⊕
    {e : Fin k × Fin 2 // (0:Fin 1)=0})=2*k
  simp [Nat.mul_comm]

lemma connectedCutData_stable (g k : ℕ) (hg : 2≤g) (hk : k≤g) :
    ∀c,Stable ((connectedCutData g k).genus c)
      ((connectedCutData g k).boundaryCount c) := by
  intro c
  change Fin 1 at c
  rw [connectedCutData_boundaryCount]
  change 2*(g-k)+2*k>2
  omega

lemma connectedCutData_euler (g k : ℕ) (hk : k≤g) :
    (∑c,(connectedCutData g k).genus c)+k+1=g+(connectedCutData g k).components := by
  change (∑ _c : Fin 1,g-k)+k+1=g+1
  simp only [Fin.sum_univ_one]
  omega

lemma connected_cut_genus (g k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1)
    (heuler : (∑c,D.genus c)+k+1=g+D.components) (c : Fin D.components) :
    D.genus c=g-k := by
  rcases D with ⟨q,gen,cv,ev⟩
  dsimp at hc
  subst q
  simp only [Fin.sum_univ_one] at heuler
  have hcz : c=0 := Subsingleton.elim _ _
  subst c
  dsimp at heuler ⊢
  omega

lemma connected_cut_boundaryCount (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) : D.boundaryCount c=2*k := by
  classical
  rcases D with ⟨q,gen,cv,ev⟩
  dsimp at hc
  subst q
  have hev : ev=fun _=>c := funext fun _=>Subsingleton.elim _ _
  simp [MulticurveCutData.boundaryCount,MulticurveCutData.Boundary,hev,Nat.mul_comm]

def connected_cut_isomorphism (g k : ℕ) (D E : MulticurveCutData 0 k)
    (hD : D.components=1) (hE : E.components=1)
    (hde : (∑c,D.genus c)+k+1=g+D.components)
    (hee : (∑c,E.genus c)+k+1=g+E.components) : D.Isomorphism E where
  vertexEquiv := (finCongr hD).trans (finCongr hE).symm
  flip := fun _=>false
  genus_eq c := by
    rw [connected_cut_genus g k E hE hee,connected_cut_genus g k D hD hde]
  cusp_eq i := Fin.elim0 i
  edge_eq e j := by
    apply Fin.ext
    have ha := ((finCongr hD).trans (finCongr hE).symm (D.edgeVertex (e,j))).isLt
    have hb := (E.edgeVertex (e,if (false:Bool) then j.rev else j)).isLt
    omega

lemma connected_orbit_unique {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology G T H Q)
    {g k : ℕ} (o q : A.Orbit g 0 k)
    (ho : (A.cut o).components=1) (hq : (A.cut q).components=1) : o=q :=
  A.cut_classifies o q ⟨connected_cut_isomorphism g k (A.cut o) (A.cut q)
    ho hq (A.cut_euler o) (A.cut_euler q)⟩

def connected_cut_halfEdgeEquiv (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) : D.Boundary c ≃ (Fin k × Fin 2) where
  toFun b := match b with
    | Sum.inl j=>Fin.elim0 j.val
    | Sum.inr e=>e.val
  invFun e := Sum.inr ⟨e,by
    apply Fin.ext
    have h0 := (D.edgeVertex e).isLt
    have h1 := c.isLt
    omega⟩
  left_inv b := by
    cases b with
    | inl j=>exact Fin.elim0 j.val
    | inr e=>rfl
  right_inv e := rfl

def connected_cut_boundaryIndexEquiv (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) :
    Fin (D.boundaryCount c) ≃ (Fin k × Fin 2) :=
  (Fintype.equivFin (D.Boundary c)).symm.trans (connected_cut_halfEdgeEquiv k D hc c)

lemma connected_cut_boundary_length (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ)
    (j : Fin (D.boundaryCount c)) :
    D.tightProtectedLengths (fun i=>Fin.elim0 i) x c j =
      x (connected_cut_boundaryIndexEquiv k D hc c j).1 := by
  unfold MulticurveCutData.tightProtectedLengths
  change _ = x (connected_cut_halfEdgeEquiv k D hc c
    ((Fintype.equivFin (D.Boundary c)).symm j)).1
  cases hb : (Fintype.equivFin (D.Boundary c)).symm j with
  | inl b=>exact Fin.elim0 b.val
  | inr b=>
    simp only [connected_cut_halfEdgeEquiv]
    rfl

lemma connected_cut_boundary_product (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) (f : ℝ→ℝ) :
    (∏j,f (D.tightProtectedLengths (fun i=>Fin.elim0 i) x c j)) =
      ∏i,f (x i)^2 := by
  classical
  calc
    _ = ∏e : Fin k × Fin 2,f (x e.1) :=
      Fintype.prod_equiv (connected_cut_boundaryIndexEquiv k D hc c) _ _
        (fun j=>congrArg f (connected_cut_boundary_length k D hc c x j))
    _ = _ := by simp [Fintype.prod_prod_type,pow_two]

lemma connected_cut_productG {P : PsiTheory} (g k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1)
    (heuler : (∑c,D.genus c)+k+1=g+D.components) (x : Fin k→ℝ) :
    TightSeparating.cutProductG P D.genus D.boundaryCount
      (D.tightProtectedLengths (fun i=>Fin.elim0 i) x) =
    fun z=>TightMoments.momentTightG P (g-k)
      (D.boundaryCount ((finCongr hc).symm 0))
      (D.tightProtectedLengths (fun i=>Fin.elim0 i) x ((finCongr hc).symm 0)) z := by
  rcases D with ⟨q,gen,cv,ev⟩
  dsimp at hc
  subst q
  funext z
  unfold TightSeparating.cutProductG
  rw [Fin.prod_univ_one]
  congr 2
  exact connected_cut_genus g k _ rfl heuler 0

lemma connected_cut_kernel_single {P : PsiTheory} {G : WeilPeterssonGeometry P}
    (T : TightRegions G) (k n : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) :
    D.tightCutKernel T (fun i=>Fin.elim0 i) (fun _ : Fin n=>0) x =
      tightVolume T (D.genus c) (D.boundaryCount c) n
        (D.tightProtectedLengths (fun i=>Fin.elim0 i) x c) (fun _=>0) := by
  classical
  rcases D with ⟨q,gen,cv,ev⟩
  dsimp at hc
  subst q
  have hcz : c=0 := Subsingleton.elim _ _
  subst c
  unfold MulticurveCutData.tightCutKernel
  simp only [Fintype.sum_unique,Fin.prod_univ_one]
  have hcount : MulticurveCutData.assignedCount
      (D:={components:=1,genus:=gen,cuspVertex:=cv,edgeVertex:=ev})
      (default : Fin n→Fin 1) 0=n := by
    unfold MulticurveCutData.assignedCount
    exact (Fintype.card_congr (Equiv.subtypeUnivEquiv
      (fun j : Fin n=>Subsingleton.elim ((default : Fin n→Fin 1) j) 0))).trans
        (Fintype.card_fin n)
  let D0 : MulticurveCutData 0 k :=
    {components:=1,genus:=gen,cuspVertex:=cv,edgeVertex:=ev}
  change tightVolume T (gen 0) (D0.boundaryCount 0)
    (D0.assignedCount (default : Fin n→Fin 1) 0)
    (D0.tightProtectedLengths (fun i=>Fin.elim0 i) x 0)
    (fun _=>0) = tightVolume T (gen 0) (D0.boundaryCount 0) n
    (D0.tightProtectedLengths (fun i=>Fin.elim0 i) x 0) (fun _=>0)
  rw [hcount]

def connected_cut_boundaryVector (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) : Fin (2*k)→ℝ :=
  fun j=>D.tightProtectedLengths (fun i=>Fin.elim0 i) x c
    ((finCongr (connected_cut_boundaryCount k D hc c)).symm j)

lemma connected_cut_boundaryVector_product (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) (f : ℝ→ℝ) :
    (∏j,f (connected_cut_boundaryVector k D hc c x j))=∏i,f (x i)^2 := by
  calc
    _ = ∏j : Fin (D.boundaryCount c),f (D.tightProtectedLengths (fun i=>Fin.elim0 i) x c j) :=
      (finCongr (connected_cut_boundaryCount k D hc c)).symm.prod_comp
        (fun j=>f (D.tightProtectedLengths (fun i=>Fin.elim0 i) x c j))
    _ = _ := connected_cut_boundary_product k D hc c x f

lemma connected_cut_boundaryVector_mem (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) (B : ℝ)
    (hx : ∀i,x i∈Icc (0:ℝ) B) :
    ∀j,connected_cut_boundaryVector k D hc c x j∈Icc (0:ℝ) B := by
  intro j
  unfold connected_cut_boundaryVector
  rw [connected_cut_boundary_length k D hc c x]
  exact hx _

lemma connected_cut_boundaryVector_div (k : ℕ) (D : MulticurveCutData 0 k)
    (hc : D.components=1) (c : Fin D.components) (x : Fin k→ℝ) (a : ℝ) :
    connected_cut_boundaryVector k D hc c (fun i=>x i/a)=
      fun j=>connected_cut_boundaryVector k D hc c x j/a := by
  funext j
  unfold connected_cut_boundaryVector
  rw [connected_cut_boundary_length k D hc c (fun i=>x i/a),
    connected_cut_boundary_length k D hc c x]

lemma momentTightG_finCongr (P : PsiTheory) (g m n : ℕ) (h : m=n) (L : Fin m→ℝ) :
    TightMoments.momentTightG P g m L =
      TightMoments.momentTightG P g n (fun i=>L ((finCongr h).symm i)) := by
  subst n
  rfl


end WP.TightConnected
