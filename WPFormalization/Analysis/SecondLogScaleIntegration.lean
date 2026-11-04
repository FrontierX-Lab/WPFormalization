import WPFormalization.Volumes.PrefactorIntegration

/-! The actual logarithmic Z scale gives a quadratic genus error on the long interval cut off at distance h^(-3) from the critical parameter. -/

noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma second_order_log_scale_long_interval (p : ℕ) (f : ℕ→ℝ→ℝ) (C : ℝ) (hC : 0<C)
    (G : ℕ)
    (hvar : ∀ g ≥ G,∀ Y∈Ico (0:ℝ) y₀,∀ B∈Ico (0:ℝ) y₀,Y ≤ B →
      |f g Y-f g B| ≤ C/(complexity g p:ℝ)^2*(Real.log (Z Y)-Real.log (Z B))) :
    ∃ D : ℝ,0<D ∧ ∃ H : ℕ,∀ g ≥ H,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^3
      B∈Ico (0:ℝ) y₀ ∧ ∀ Y∈Ico (0:ℝ) y₀,Y ≤ B →
        |f g Y-f g B| ≤ D*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
  obtain ⟨M,δ,hM,hδ,hlog⟩ := Z_critical_log_bound
  have hδtendsto : Tendsto (fun g : ℕ => ((complexity g p:ℝ)⁻¹)^3) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_pow (by norm_num : 3≠0),Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (complexity_real_tendsto_atTop p)).pow 3
  obtain ⟨Gδ,hsmall⟩ := eventually_atTop.mp
    (hδtendsto.eventually (eventually_lt_nhds (lt_min hδ y₀_pos)))
  let q : ℝ := Real.log 2
  have hq : 0<q := Real.log_pos (by norm_num)
  let N : ℝ := |Real.log (Z 0)|+M+(15/2:ℝ)*Real.log ((p:ℝ)+2)
  have hN : 0<N := by
    have hl : 0 ≤ Real.log ((p:ℝ)+2) := Real.log_nonneg (by have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _;linarith)
    dsimp [N]
    positivity
  let D : ℝ := N/q+15/2
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨C*D,by positivity,max (max G Gδ) 2,?_⟩
  intro g hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgG : G ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hgδ : Gδ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hhNat : g ≤ complexity g p := by unfold complexity;omega
  have hhg : (g:ℝ) ≤ complexity g p := by exact_mod_cast hhNat
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hhp : (0:ℝ)<complexity g p := hgp.trans_le hhg
  let h : ℝ := complexity g p
  let B : ℝ := y₀-(h⁻¹)^3
  have hbδ : (h⁻¹)^3< min δ y₀ := hsmall g hgδ
  have hpow : 0<(h⁻¹)^3 := pow_pos (inv_pos.mpr hhp) 3
  have hB : B∈Ico (0:ℝ) y₀ := by
    dsimp [B]
    exact ⟨(sub_pos.mpr (hbδ.trans_le (min_le_right _ _))).le,sub_lt_self _ hpow⟩
  refine ⟨hB,?_⟩
  intro Y hY hYB
  have hlogB := hlog B hB (by dsimp [B];linarith [hbδ.trans_le (min_le_left _ _)])
  have hδlog : Real.log (y₀-B)=-3*Real.log h := by
    dsimp [B]
    rw [show y₀-(y₀-(h⁻¹)^3)=(h⁻¹)^3 by ring,Real.log_pow,Real.log_inv]
    ring
  rw [hδlog] at hlogB
  have hZgap : Real.log (Z Y)-Real.log (Z B) ≤ D*Real.log ((g:ℝ)+1) := by
    have hzY := logZ_le_zero_parameter Y hY
    have hlogh := complexity_log_bound g p hg2
    have hqL : q ≤ Real.log ((g:ℝ)+1) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ g+1 by omega))
    have hNL : N ≤ (N/q)*Real.log ((g:ℝ)+1) := by
      have he := mul_le_mul_of_nonneg_left hqL (div_pos hN hq).le
      rwa [div_mul_cancel₀ N hq.ne'] at he
    have hlower : -M ≤ Real.log (Z B)+(15/2:ℝ)*Real.log h := by
      have he := (abs_le.mp hlogB).1
      linarith
    have hfirst : Real.log (Z Y)-Real.log (Z B) ≤ N+(15/2:ℝ)*Real.log ((g:ℝ)+1) := by
      dsimp [N]
      change Real.log h ≤ _ at hlogh
      linarith [le_abs_self (Real.log (Z 0))]
    dsimp [D]
    nlinarith
  calc
    _ ≤ C/h^2*(Real.log (Z Y)-Real.log (Z B)) := hvar g hgG Y hY B hB hYB
    _ ≤ C/h^2*(D*Real.log ((g:ℝ)+1)) := mul_le_mul_of_nonneg_left hZgap (by positivity)
    _ ≤ _ := by
      have hlg : 0 ≤ Real.log ((g:ℝ)+1) := Real.log_nonneg (by have hg0 : (0:ℝ) ≤ g := Nat.cast_nonneg _;linarith)
      have hInv : h⁻¹ ≤ (g:ℝ)⁻¹ := inv_anti₀ hgp hhg
      have hInv2 := pow_le_pow_left₀ (inv_nonneg.mpr hhp.le) hInv 2
      have he := mul_le_mul_of_nonneg_left hInv2 (show 0 ≤ C*D*Real.log ((g:ℝ)+1) by positivity)
      convert he using 1 <;> ring
end WP.Analysis
