import WPFormalization.Marked.ExternalBoundaryContinuity
/-! Uniform relative continuity of the original boundary factors under a
relative change of their scaled lengths. This controls the tight Gaussian
tilt when the physical lengths themselves may tend to infinity. -/
noncomputable section
set_option maxHeartbeats 600000
namespace WP.TightConnected
open Set
lemma connected_scaled_factor_joint_continuous (p : ℕ) (B : ℝ) :
    Continuous (fun q : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) =>
      ∏ i, boundaryFactor 0 ((q.1:ℝ)*(q.2 i:ℝ))) := by
  let Yzero : Icc (0:ℝ) y₀ := ⟨0,le_rfl,y₀_pos.le⟩
  have hzero : Continuous (fun _q : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) => Yzero) := continuous_const
  apply continuous_finsetProd Finset.univ
  intro i _
  have hq : Continuous (fun q : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) => (q.1:ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hl : Continuous (fun q : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) => (q.2 i:ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
  exact Continuous.comp' (g := fun z : (Icc (0:ℝ) y₀) × ℝ => boundaryFactor (z.1:ℝ) z.2)
    (f := fun q : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) =>
      (Yzero,(q.1:ℝ)*(q.2 i:ℝ))) boundaryFactor_joint_continuous (hzero.prodMk (hq.mul hl))

lemma connected_scaled_factor_uniform_relative_continuity (p : ℕ) (B ε : ℝ)
    (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ q∈Icc (0:ℝ) 2, ∀ t : Fin p→ℝ,
      (∀i,t i∈Icc 0 B) → |q-1|<δ →
      |(∏i,boundaryFactor 0 (q*t i))/(∏i,boundaryFactor 0 (t i))-1|≤ε := by
  have hc := CompactSpace.uniformContinuous_of_continuous
    (connected_scaled_factor_joint_continuous p B)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hc ε hε
  refine ⟨δ,hδ,?_⟩
  intro q hq t ht hq1
  let a : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) := (⟨q,hq⟩,fun i=>⟨t i,ht i⟩)
  let b : Icc (0:ℝ) 2 × (Fin p → Icc (0:ℝ) B) := (⟨1,by norm_num⟩,fun i=>⟨t i,ht i⟩)
  have hd : dist a b<δ := by
    simpa [a,b,Prod.dist_eq,Subtype.dist_eq,Real.dist_eq] using hq1
  have he : |(∏i,boundaryFactor 0 (q*t i))-(∏i,boundaryFactor 0 (t i))|<ε := by
    simpa only [a,b,Real.dist_eq,one_mul] using hclose hd
  have hden := one_le_boundaryFactor_product 0 t
  rw [div_sub_one (ne_of_gt (zero_lt_one.trans_le hden)),abs_div,
    abs_of_pos (zero_lt_one.trans_le hden)]
  exact (div_le_self (abs_nonneg _) hden).trans he.le
end WP.TightConnected
