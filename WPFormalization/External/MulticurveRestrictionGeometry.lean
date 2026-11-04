import WPFormalization.External.MirzakhaniIntegration

/-! Classical compatibility of actual multicurve cuts under forgetting or
reordering cutting curves. Source: Mirzakhani's 12 July 2005 version of
Simple geodesics and Weil--Petersson volumes of moduli spaces of bordered
Riemann surfaces, section 2 printed pages 11--12 (cutting out disjoint annular
neighborhoods, labelled cusps and the two boundary sides), and section 8
printed pages 36--38 (ordered multicurve mapping-class covers).

The finite-graph `Gluing.genus_euler` formula is the ordinary orientable-surface
Euler gluing identity, not a verbatim formula stated in that paper. All
removed edges are glued; a removed loop adds genus. Components are the
connected blocks under removed edges, and original cusp labels are retained.
This background interface permits zero retained edges and full reordering.
It contains no short-curve classification, nonseparating/pants criterion,
configuration recording, moment, or asymptotic estimate. No instance is
postulated here. Intrinsic-piece boundary sides are not identified with
injectively embedded ambient curve classes by this interface. -/
noncomputable section
universe aa bb cc dd
namespace WP.External
namespace MulticurveCutData
variable {n r q : ℕ}

def DeletedAdjacent (D : MulticurveCutData n r) (ι : Fin q ↪ Fin r)
    (a b : Fin D.components) : Prop :=
  ∃ e : Fin r, e ∉ Set.range ι ∧
    ((D.edgeVertex (e,0)=a ∧ D.edgeVertex (e,1)=b) ∨
      (D.edgeVertex (e,1)=a ∧ D.edgeVertex (e,0)=b))

/-- Exact gluing of all removed cut edges. This retains every original cusp,
permits loops, and accounts for the genus created by gluing loop sides. -/
structure Gluing (D : MulticurveCutData n r) (ι : Fin q ↪ Fin r)
    (E : MulticurveCutData n q) where
  vertexMap : Fin D.components → Fin E.components
  vertex_surjective : Function.Surjective vertexMap
  flip : Fin q → Bool
  cusp_eq : ∀ j, E.cuspVertex j=vertexMap (D.cuspVertex j)
  edge_eq : ∀ e j, E.edgeVertex (e,j)=
    vertexMap (D.edgeVertex (ι e,if flip e then j.rev else j))
  deleted_same_vertex : ∀ e : Fin r, e ∉ Set.range ι →
    vertexMap (D.edgeVertex (e,0))=vertexMap (D.edgeVertex (e,1))
  fiber_connected : ∀ a b, vertexMap a=vertexMap b →
    Relation.ReflTransGen (D.DeletedAdjacent ι) a b
  genus_euler : ∀ c : Fin E.components,
    E.genus c+(Finset.univ.filter (fun a => vertexMap a=c)).card=
      (∑ a ∈ Finset.univ.filter (fun a => vertexMap a=c),D.genus a)+
      (Finset.univ.filter (fun e : Fin r => e ∉ Set.range ι ∧
        vertexMap (D.edgeVertex (e,0))=c)).card+1
end MulticurveCutData

/-- Classical functoriality of actual surface cuts under forgetting some
ordered cutting curves. No graph classification, moment, estimate, or limit
is part of this interface. Reordering is its same-cardinality special case. -/
structure MulticurveRestrictionGeometry {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) (H : HyperbolicCurveGeometry.{aa,bb,cc} G)
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) where
  restrictOrbit : ∀ {g n r q : ℕ}, (Fin q ↪ Fin r) → T.Orbit g n r → T.Orbit g n q
  orbitMem_restrict : ∀ {g n r q : ℕ} (ι : Fin q ↪ Fin r) (o : T.Orbit g n r)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin r → H.Primitive g n X),
    T.orbitMem o X γ → T.orbitMem (restrictOrbit ι o) X (fun j => γ (ι j))
  cut_restrict : ∀ {g n r q : ℕ} (ι : Fin q ↪ Fin r) (o : T.Orbit g n r),
    Nonempty (MulticurveCutData.Gluing (T.cut o) ι (T.cut (restrictOrbit ι o)))
end WP.External
