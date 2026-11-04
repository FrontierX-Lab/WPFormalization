import WPFormalization.Critical.PrimitiveCountPacking
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open WP.External.HyperbolicPacking
open scoped Classical ENNReal

def surfaceLift (S : QuotientSurface) (p : S.Point) : UpperHalfPlane :=
  Classical.choose (S.surjective_on_domain p)
lemma surfaceLift_mem (S : QuotientSurface) (p : S.Point) : surfaceLift S p ∈ S.domain :=
  (Classical.choose_spec (S.surjective_on_domain p)).1
lemma project_surfaceLift (S : QuotientSurface) (p : S.Point) : S.project (surfaceLift S p)=p :=
  (Classical.choose_spec (S.surjective_on_domain p)).2

def BasedRep {S : QuotientSurface} (C : PrimitiveGeometry S) (γ : C.Primitive)
    (η : S.Γ) : Prop := ∃ δ : S.Γ, η=δ*(C.representative γ).deck*δ⁻¹

lemma primitive_eq_of_basedRep {S : QuotientSurface} (C : PrimitiveGeometry S)
    {γ γ' : C.Primitive} {η : S.Γ} (h : BasedRep C γ η) (h' : BasedRep C γ' η) : γ=γ' := by
  obtain ⟨δ,hδ⟩ := h
  obtain ⟨δ',hδ'⟩ := h'
  rw [←C.class_representative γ,←C.class_representative γ']
  apply (C.class_eq_iff _ _).mpr
  refine ⟨δ'⁻¹*δ,Or.inl ?_⟩
  have he : δ*(C.representative γ).deck*δ⁻¹ = δ'*(C.representative γ').deck*δ'⁻¹ := hδ.symm.trans hδ'
  have hh := congrArg (fun x : S.Γ => δ'⁻¹*x*δ') he
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_rev,inv_inv,inv_mul_cancel,mul_one] using hh.symm

lemma axis_period_displacement {S : QuotientSurface} (a : PrimitiveAxis S.Γ S.domain) (t : ℝ) :
    dist (a.axis t) (a.deck.val (a.axis t))=a.period := by
  rw [a.translates, a.isometry.dist_eq,Real.dist_eq]
  rw [show t-(t+a.period) = -a.period by ring, abs_neg,abs_of_pos a.period_pos]

lemma dist_isometric_translate {X : Type*} [PseudoMetricSpace X] (e : X≃ᵢX) (z q : X) :
    dist z (e z) ≤ 2*dist z q + dist q (e q) := by
  calc
    dist z (e z) ≤ dist z q + dist q (e z) := dist_triangle _ _ _
    _ ≤ dist z q + (dist q (e q)+dist (e q) (e z)) := add_le_add le_rfl (dist_triangle _ _ _)
    _ = 2*dist z q+dist q (e q) := by rw [e.isometry.dist_eq,dist_comm q z];ring

lemma exists_basedRep_close {S : QuotientSurface} (C : PrimitiveGeometry S) (γ : C.Primitive)
    (p : S.Point) (r : ℝ) (hclose : ∃q∈C.trace γ,dist p q<r) :
    ∃η : S.Γ, BasedRep C γ η ∧ dist (surfaceLift S p) (η.val (surfaceLift S p)) < C.length γ+2*r := by
  obtain ⟨q,⟨a,⟨t,rfl⟩,rfl⟩,hpq⟩ := hclose
  have hi : sInf (range (fun δ:S.Γ => dist (surfaceLift S p) (δ.val ((C.representative γ).axis t)))) < r := by
    rw [←S.quotient_distance _ (surfaceLift_mem S p) _ ((C.representative γ).in_domain t),project_surfaceLift]
    exact hpq
  have hb : BddBelow (range (fun δ:S.Γ => dist (surfaceLift S p) (δ.val ((C.representative γ).axis t)))) :=
    ⟨0,fun _ ⟨δ,hδ⟩ => hδ ▸ dist_nonneg⟩
  obtain ⟨_,⟨δ,rfl⟩,hδ⟩ := (csInf_lt_iff hb (range_nonempty _)).mp hi
  let η : S.Γ := δ*(C.representative γ).deck*δ⁻¹
  refine ⟨η,⟨δ,rfl⟩,?_⟩
  have he : η.val (δ.val ((C.representative γ).axis t)) =
      δ.val ((C.representative γ).deck.val ((C.representative γ).axis t)) := by
    change (η*δ).val ((C.representative γ).axis t) = _
    dsimp [η]
    simp
  have hd : dist (δ.val ((C.representative γ).axis t)) (η.val (δ.val ((C.representative γ).axis t)))=C.length γ := by
    rw [he,δ.val.isometry.dist_eq,axis_period_displacement]
    rfl
  have hh := dist_isometric_translate η.val (surfaceLift S p) (δ.val ((C.representative γ).axis t))
  rw [hd] at hh
  linarith

end WP.Critical.PrimitivePacking
