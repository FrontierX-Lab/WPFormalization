import WPFormalization.Critical.PantsClusterDefinitions

/-! Local consequences of classical marked hyperbolic metric variation.
The cluster itself is the actual full primitive spectrum from Definitions;
continuity and uniformly finite relevant catalogs are not inputs. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported

variable (F : Family.{u,v}) (D : DeformationClassics F)

private lemma logRatio_continuous (t : Waist) :
    Continuous (fun s : Waist => |Real.log (s.val / t.val)|) := by
  apply Continuous.abs
  exact (continuous_subtype_val.div_const t.val).log
    (fun s => div_ne_zero s.property.ne' t.property.ne')

private lemma logRatio_self (t : Waist) : |Real.log (t.val / t.val)| = 0 := by
  rw [div_self t.property.ne', Real.log_one, abs_zero]

private lemma logRatio_symm (s t : Waist) :
    |Real.log (s.val / t.val)| = |Real.log (t.val / s.val)| := by
  rw [Real.log_div s.property.ne' t.property.ne',
    Real.log_div t.property.ne' s.property.ne']
  exact abs_sub_comm _ _

include D

lemma marked_length_continuous (γ : F.Primitive) :
    Continuous (fun s : Waist => F.length s γ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨C,hC,hcompare⟩ := D.length_comparison (t.val+1) (by linarith [t.property])
  let K : Waist → ℝ := fun s => 1 + C * |Real.log (s.val / t.val)|
  have hK : Continuous K := continuous_const.add (continuous_const.mul (logRatio_continuous t))
  have hKt : K t = 1 := by simp only [K,logRatio_self,mul_zero,add_zero]
  have hKpos (s : Waist) : 0 < K s := by
    dsimp [K]
    nlinarith [abs_nonneg (Real.log (s.val/t.val))]
  have hB : ∀ᶠ s : Waist in 𝓝 t, s.val ≤ t.val+1 :=
    (continuous_subtype_val.continuousAt.eventually (eventually_le_nhds (by linarith)))
  have hlog : ∀ᶠ s : Waist in 𝓝 t, |Real.log (s.val/t.val)| ≤ 2 := by
    have ht : Tendsto (fun s : Waist => |Real.log (s.val/t.val)|) (𝓝 t) (𝓝 0) := by
      simpa only [logRatio_self] using (logRatio_continuous t).continuousAt.tendsto (x:=t)
    exact ht.eventually (eventually_le_nhds (by norm_num))
  have hlo : ∀ᶠ s : Waist in 𝓝 t, F.length t γ / K s ≤ F.length s γ := by
    filter_upwards [hB,hlog] with s hs hlog
    apply (div_le_iff₀ (hKpos s)).mpr
    simpa only [K,logRatio_symm s t,mul_comm] using
      hcompare t s (by linarith) hs (by rwa [←logRatio_symm s t]) γ
  have hhi : ∀ᶠ s : Waist in 𝓝 t, F.length s γ ≤ K s * F.length t γ := by
    filter_upwards [hB,hlog] with s hs hlog
    exact hcompare s t hs (by linarith) hlog γ
  have hl : Tendsto (fun s : Waist => F.length t γ / K s) (𝓝 t) (𝓝 (F.length t γ)) := by
    have hc : Continuous (fun s : Waist => F.length t γ / K s) :=
      continuous_const.div hK (fun s => (hKpos s).ne')
    simpa only [hKt,div_one] using hc.continuousAt.tendsto (x:=t)
  have hh : Tendsto (fun s : Waist => K s * F.length t γ) (𝓝 t) (𝓝 (F.length t γ)) := by
    simpa only [hKt,one_mul] using (hK.mul_const (F.length t γ)).continuousAt.tendsto (x:=t)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh hlo hhi

lemma local_length_comparison (t : Waist) :
    ∀ᶠ s : Waist in 𝓝 t, ∀ γ : F.Primitive, F.length t γ ≤ 2 * F.length s γ := by
  obtain ⟨C,hC,hcompare⟩ := D.length_comparison (t.val+1) (by linarith [t.property])
  have hB : ∀ᶠ s : Waist in 𝓝 t, s.val ≤ t.val+1 :=
    continuous_subtype_val.continuousAt.eventually (eventually_le_nhds (by linarith))
  have hlog : ∀ᶠ s : Waist in 𝓝 t,
      |Real.log (s.val/t.val)| ≤ min 2 (1/C) := by
    have ht : Tendsto (fun s : Waist => |Real.log (s.val/t.val)|) (𝓝 t) (𝓝 0) := by
      simpa only [logRatio_self] using (logRatio_continuous t).continuousAt.tendsto (x:=t)
    exact ht.eventually (eventually_le_nhds (lt_min (by norm_num) (one_div_pos.mpr hC)))
  filter_upwards [hB,hlog] with s hs hlog γ
  have hh := hcompare t s (by linarith) hs
    (by rw [←logRatio_symm s t]; exact hlog.trans (min_le_left _ _)) γ
  have hsmall : C * |Real.log (s.val/t.val)| ≤ 1 :=
    by
      have hh := (le_div_iff₀ hC).mp (hlog.trans (min_le_right _ _))
      nlinarith
  rw [←logRatio_symm s t] at hh
  have hpos := F.length_pos s γ
  nlinarith

lemma local_finite_catalog (t : Waist) (L : ℝ) :
    ∃ S : Finset F.Primitive, ∀ᶠ s : Waist in 𝓝 t,
      ∀ γ : F.Primitive, F.length s γ ≤ L → γ ∈ S := by
  refine ⟨F.short t (2*L), ?_⟩
  filter_upwards [local_length_comparison F D t] with s hs γ hγ
  apply (F.mem_short t _ γ).mpr
  exact (hs γ).trans (mul_le_mul_of_nonneg_left hγ (by norm_num))

lemma test_integral_locally_eq_finite_sum (t : Waist) (f : C_c(ℝ≥0,ℝ)) :
    ∃ S : Finset F.Primitive, ∀ᶠ s : Waist in 𝓝 t,
      (∫ x, f x ∂measure F s) = ∑ γ ∈ S, f (Real.toNNReal (F.length s γ)) := by
  classical
  obtain ⟨B,hB⟩ := (show IsCompact (tsupport f) from f.hasCompactSupport).bddAbove
  obtain ⟨S,hS⟩ := local_finite_catalog F D t (B : ℝ)
  refine ⟨S, ?_⟩
  filter_upwards [hS] with s hs
  rw [integral_eq_tsum]
  apply tsum_eq_sum
  intro γ hγ
  by_contra hne
  apply hγ
  apply hs γ
  exact Real.toNNReal_le_iff_le_coe.mp (hB (subset_tsupport f hne))

lemma test_integral_continuous (f : C_c(ℝ≥0,ℝ)) :
    Continuous (fun s : Waist => ∫ x, f x ∂measure F s) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨S,hS⟩ := test_integral_locally_eq_finite_sum F D t f
  have hc : Continuous (fun s : Waist => ∑ γ ∈ S, f (Real.toNNReal (F.length s γ))) := by
    apply continuous_finsetSum
    intro γ hγ
    exact f.continuous.comp (continuous_real_toNNReal.comp (marked_length_continuous F D γ))
  have he := Filter.EventuallyEq.eq_of_nhds hS
  change Tendsto (fun s : Waist => ∫ x, f x ∂measure F s) (𝓝 t)
    (𝓝 (∫ x, f x ∂measure F t))
  rw [he]
  exact hc.continuousAt.tendsto.congr' (Filter.EventuallyEq.symm hS)

lemma pointMeasure_continuous : Continuous (pointMeasure F) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  exact test_integral_continuous F D f

end WP.Critical.PantsCluster
