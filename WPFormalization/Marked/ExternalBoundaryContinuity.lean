import WPFormalization.Analysis.BoundaryFactorBasic
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace WP
open Set

lemma boundaryFactor_product_joint_continuous (p : ℕ) (L0 : ℝ) :
    Continuous (fun q : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) =>
      ∏ i, boundaryFactor (q.1:ℝ) (q.2 i:ℝ)) := by
  apply continuous_finsetProd (f := fun (i : Fin p)
    (q : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0)) =>
      boundaryFactor (q.1:ℝ) (q.2 i:ℝ)) Finset.univ
  intro i _
  have hy : Continuous (fun q : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) => q.1) := continuous_fst
  have hl : Continuous (fun q : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) => (q.2 i:ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
  exact Continuous.comp' (g := fun z : (Icc (0:ℝ) y₀) × ℝ => boundaryFactor (z.1:ℝ) z.2)
    (f := fun q : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) => (q.1,(q.2 i:ℝ)))
    boundaryFactor_joint_continuous (hy.prodMk hl)

lemma one_le_boundaryFactor_product {p : ℕ} (Y : ℝ) (L : Fin p → ℝ) :
    1 ≤ ∏ i, boundaryFactor Y (L i) := by
  exact Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor Y (L i))

lemma boundaryFactor_product_uniform_compact_bound (p : ℕ) (L0 : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ Y ∈ Icc 0 y₀, ∀ L : Fin p → ℝ,
      (∀ i, L i ∈ Icc 0 L0) → ∏ i, boundaryFactor Y (L i) ≤ B := by
  obtain ⟨B,hBpos,hB⟩ := boundaryFactor_uniform_compact_bound L0
  refine ⟨(max 1 B)^p, one_le_pow₀ (le_max_left _ _), ?_⟩
  intro Y hY L hL
  calc
    _ ≤ ∏ _i : Fin p, max 1 B := Finset.prod_le_prod₀
      (fun i _ => (boundaryFactor_pos Y (L i)).le)
      (fun i _ => (hB Y hY (L i) (hL i)).trans (le_max_right _ _))
    _ = _ := by simp

/-- The original integral boundary factors have a common relative modulus in Y,
including both critical endpoints, uniformly throughout a fixed length box. -/
lemma boundaryFactor_product_uniform_relative_continuity (p : ℕ) (L0 : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y ∈ Icc 0 y₀, ∀ Z ∈ Icc 0 y₀,
      ∀ L : Fin p → ℝ, (∀ i, L i ∈ Icc 0 L0) → |Y-Z| < δ →
        |(∏ i, boundaryFactor Y (L i))/(∏ i, boundaryFactor Z (L i))-1| ≤ ε := by
  have hc := CompactSpace.uniformContinuous_of_continuous
    (boundaryFactor_product_joint_continuous p L0)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hc ε hε
  refine ⟨δ,hδ,?_⟩
  intro Y hY Z hZ L hL hYZ
  let a : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) :=
    (⟨Y,hY⟩,fun i => ⟨L i,hL i⟩)
  let b : (Icc (0:ℝ) y₀) × (Fin p → Icc (0:ℝ) L0) :=
    (⟨Z,hZ⟩,fun i => ⟨L i,hL i⟩)
  have hd : dist a b < δ := by
    simpa [a,b,Prod.dist_eq,Subtype.dist_eq,Real.dist_eq] using hYZ
  have he : |(∏ i, boundaryFactor Y (L i))-(∏ i, boundaryFactor Z (L i))| < ε := by
    simpa only [a,b,Real.dist_eq] using hclose hd
  have hden := one_le_boundaryFactor_product Z L
  rw [div_sub_one (ne_of_gt (zero_lt_one.trans_le hden)),abs_div,abs_of_pos (zero_lt_one.trans_le hden)]
  exact (div_le_self (abs_nonneg _) hden).trans he.le
end WP
