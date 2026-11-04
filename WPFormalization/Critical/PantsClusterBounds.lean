import WPFormalization.Critical.PantsClusterCatalog
import WPFormalization.Critical.PrimitiveCount

/-! The existing actual primitive-count theorem G.2 bounds the cluster
multiplicities uniformly over every positive waist. No support cutoff or
cluster-moment estimate is an external input. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported

variable (F : Family.{u,v})

lemma negativeEuler_eq_one (s : Waist) : (F.model s).negativeEuler = 1 := by
  have he := (F.model s).euler_eq
  rw [F.genus,F.cusps,F.boundaries] at he
  omega

lemma measure_prefix_eq_intrinsic_card (s : Waist) (L : ℝ≥0) :
    measure F s (Iic L) = (((F.model s).curves.short (L : ℝ)).card : ℝ≥0∞) := by
  classical
  rw [measure_Iic]
  let e : {γ : F.Primitive // F.length s γ ≤ (L : ℝ)} ≃
      {γ : (F.model s).curves.Primitive // γ ∈ (F.model s).curves.short (L : ℝ)} :=
    { toFun := fun γ => ⟨F.marking s γ.val,((F.model s).curves.mem_short _ _).mpr γ.property⟩
      invFun := fun γ => ⟨(F.marking s).symm γ.val,by
        have hγ := ((F.model s).curves.mem_short _ _).mp γ.property
        simpa only [Family.length,Equiv.apply_symm_apply,
          WP.External.HyperbolicPacking.PrimitiveGeometry.length] using hγ⟩
      left_inv := fun γ => Subtype.ext ((F.marking s).symm_apply_apply γ.val)
      right_inv := fun γ => Subtype.ext ((F.marking s).apply_symm_apply γ.val) }
  congr 1
  exact (Nat.card_congr e).trans (by simp [Nat.card_eq_fintype_card])

lemma cluster_card_uniform_bound (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Waist, (((F.model s).curves.short L).card : ℝ) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := WP.Critical.PrimitivePacking.bounded_primitive_count 1 L
  refine ⟨C,hC,?_⟩
  intro s
  apply hbound (F.model s) (F.double s)
  · rw [negativeEuler_eq_one]
    norm_num
  · rw [negativeEuler_eq_one]
    norm_num

lemma cluster_prefix_uniform_bound (L : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Waist, (measure F s (Iic L)).toReal ≤ C := by
  obtain ⟨C,hC,hbound⟩ := cluster_card_uniform_bound F (L : ℝ)
  refine ⟨C,hC,?_⟩
  intro s
  rw [measure_prefix_eq_intrinsic_card]
  simpa only [ENNReal.toReal_natCast] using hbound s

end WP.Critical.PantsCluster
