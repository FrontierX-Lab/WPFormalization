import WPFormalization.Volumes.DiagonalChainAlgebra

/-! The closed-volume logarithm is sublinear in genus, using only the
already proved fixed-cusp constant theorem. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma diagonal_closed_logarithm_tendsto (P : PsiTheory) :
    Tendsto (fun g : ℕ => Real.log (normalizedVolume P g 0)/(g : ℝ)) atTop (𝓝 0) := by
  let D : ℕ → ℝ := fun g => (2*g-3).factorial*(4*Real.pi^2)^(2*g-3)
  let q : ℕ → ℝ := fun g => volumeModel P g 0/(D g/Real.sqrt (Real.pi*g))
  obtain ⟨C,hC,G,hV⟩ := zograf_constant_proof P 0
  have hq : Tendsto q atTop (𝓝 1) := by
    apply real_tendsto_of_abs_error q (fun g : ℕ => C/(g : ℝ)) 1
    · simpa only [div_eq_mul_inv,mul_zero] using inverse_genus_tendsto_zero.const_mul C
    · apply eventually_atTop.mpr
      refine ⟨G,?_⟩
      intro g hg
      simpa only [q,D,Nat.add_zero] using hV g hg
  have hqlog := hq.log one_ne_zero
  have hqsmall : Tendsto (fun g : ℕ => Real.log (q g)/(g : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.log_one,zero_mul,div_eq_mul_inv] using hqlog.mul inverse_genus_tendsto_zero
  have hlogg : Tendsto (fun g : ℕ => Real.log (g : ℝ)/(g : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogs : Tendsto (fun g : ℕ => Real.log (Real.sqrt (Real.pi*g))/(g : ℝ))
      atTop (𝓝 0) := by
    have ht := ((inverse_genus_tendsto_zero.const_mul (Real.log Real.pi)).add hlogg).div_const 2
    simp only [mul_zero,zero_add,zero_div] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with g hg
    have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
    rw [Real.log_sqrt (by positivity : (0 : ℝ) ≤ Real.pi*g),Real.log_mul Real.pi_ne_zero hgr.ne']
    ring
  have ht := hqsmall.sub hlogs
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [diagonal_closed_volume_eventually_pos P,eventually_ge_atTop 1] with g hVpos hg
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hD : D g ≠ 0 := by dsimp [D];positivity
  have hS : Real.sqrt (Real.pi*g) ≠ 0 := by positivity
  have hqne : q g ≠ 0 := div_ne_zero hVpos.ne' (div_ne_zero hD hS)
  have he : normalizedVolume P g 0 = q g/Real.sqrt (Real.pi*g) := by
    simp only [normalizedVolume,Nat.add_zero,q,D]
    field_simp
  rw [he,Real.log_div hqne hS]
  ring

lemma diagonal_closed_logarithm_sublinear (P : PsiTheory) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G,
      |Real.log (normalizedVolume P g 0)| ≤ ε*(g : ℝ) := by
  intro ε hε
  have hb := (diagonal_closed_logarithm_tendsto P).eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
  obtain ⟨G,hG⟩ := eventually_atTop.mp (hb.and (eventually_ge_atTop 1))
  refine ⟨G,?_⟩
  intro g hg
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g from by have := (hG g hg).2;omega)
  have h := (hG g hg).1
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_div,abs_of_pos hgr] at h
  exact ((div_lt_iff₀ hgr).mp h).le

end WP
