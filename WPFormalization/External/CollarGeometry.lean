import WPFormalization.External.MirzakhaniIntegration

/-! Only the classical short-geodesic collar consequences are deferred.

Buser, Geometry and Spectra of Compact Riemann Surfaces, Theorem 4.4.6
(primitive length < 2 arsinh(1) implies simple), and Theorem 4.1.6
(distinct short simple geodesics do not intersect). These are the finite-area
collar facts used for cusped surfaces in Hide--Thomas, arXiv:2209.15568v3,
printed pp.1 and 8, respectively. The theorem numbers are intentionally distinct.

The fields refer to precisely the primitive geodesics of H and the disjointness
relation of T. No pants count, cut-classification conclusion, moment, or limit is
included. Their geometric realization remains explicit and unconstructed.
-/
noncomputable section
universe u v w z
namespace WP.External

@[blueprint "ext:collar"]
structure CollarGeometry {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H) : Prop where
  shortPrimitive_simple : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X), H.length γ < 2*Real.arsinh 1 → H.simple γ
  shortSimple_disjoint : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    (γ δ : H.Primitive g n X), γ ≠ δ → H.simple γ → H.simple δ →
    H.length γ < 2*Real.arsinh 1 → H.length δ < 2*Real.arsinh 1 → T.disjoint γ δ

end WP.External
