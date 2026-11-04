import WPFormalization.Statements.ChainDefinitions
import WPFormalization.Volumes.FixedCuspProof

/-! Exact normalization and subtraction along an Euler-characteristic chain.
The full-pair logarithmic estimate is an explicit internal proof input here,
and is not asserted or admitted by this module. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma chainProfile_zero : chainProfile 0 = 0 := by
  simp [chainProfile]

lemma diagonal_volume_pos_nonempty (P : PsiTheory) (g n : ℕ)
    (hn : 1 ≤ n) (hs : Stable g n) : 0 < volumeModel P g n := by
  have hd : (List.replicate n (0 : ℕ)).sum ≤ dimension g n := by simp
  have hN := normalized_pos_valid_nonempty P g (List.replicate n 0)
    (by simpa only [List.length_replicate] using hn)
    (by simpa only [List.length_replicate] using hs)
    (by simpa only [List.length_replicate] using hd) 0 ⟨le_rfl,y₀_pos.le⟩
  have hS : 0 < shifted P g (List.replicate n 0) 0 := by
    simp only [normalized,ne_of_lt y₀_pos,ite_false,a_zero,one_pow,one_mul] at hN
    exact (mul_pos_iff.mp hN).resolve_right (by
      intro h
      exact (not_lt_of_ge (pow_nonneg (r_pos 0 ⟨le_rfl,y₀_pos⟩).le _) h.1)) |>.2
  unfold volumeModel mixedBracket
  exact mul_pos (by positivity) hS

lemma diagonal_closed_volume_eventually_pos (P : PsiTheory) :
    ∀ᶠ g : ℕ in atTop, 0 < volumeModel P g 0 := by
  obtain ⟨C,hC,G,hV⟩ := zograf_constant_proof P 0
  have ht : Tendsto (fun g : ℕ => C/(g : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using inverse_genus_tendsto_zero.const_mul C
  filter_upwards [eventually_ge_atTop G,eventually_ge_atTop 2,
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with g hg hg2 hb
  have hscale : 0 < (2*g+0-3).factorial*(4*Real.pi^2)^(2*g+0-3)/
      Real.sqrt (Real.pi*g) := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
    positivity
  have h := (abs_lt.mp ((hV g hg).trans_lt hb)).1
  exact (div_pos_iff_of_pos_right hscale).mp (by linarith)

/-- Subtracting the closed value from a full-pair logarithmic estimate gives
the uniform chain quotient, including j=0 and the planar endpoint j=G. -/
lemma diagonal_chain_quotient_of_full_estimate (P : PsiTheory)
    (hfull : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g n : ℕ, Stable g n → N ≤ 2*g+n →
      |Real.log (normalizedVolume P g n) - ((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n)) :
    ∀ ε : ℝ, 0 < ε → ∃ G₀ : ℕ, ∀ G ≥ G₀, 2 ≤ G → ∀ j : ℕ, j ≤ G →
      |Real.log (volumeModel P (G-j) (2*j)/volumeModel P G 0)/G-
        chainProfile ((j : ℝ)/G)| ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := hfull (ε/4) (by positivity)
  obtain ⟨Gv,hGv⟩ := eventually_atTop.mp (diagonal_closed_volume_eventually_pos P)
  refine ⟨max N Gv,?_⟩
  intro G hG hG2 j hj
  have hGn : N ≤ G := le_trans (le_max_left _ _) hG
  have hGv' : Gv ≤ G := le_trans (le_max_right _ _) hG
  have hGp : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  have hsum : 2*(G-j)+2*j = 2*G := by omega
  have hsumR : 2*((G-j : ℕ) : ℝ)+(2*j : ℕ) = 2*(G : ℝ) := by exact_mod_cast hsum
  have hbase := hN G 0 (by unfold Stable;omega) (by omega)
  have hnode := hN (G-j) (2*j) (by unfold Stable;omega) (by omega)
  simp only [Nat.cast_zero,mul_zero,add_zero,zero_div,chainProfile_zero] at hbase
  have ht : ((2*j : ℕ) : ℝ)/(2*((G-j : ℕ) : ℝ)+(2*j : ℕ)) = (j : ℝ)/G := by
    rw [hsumR]
    push_cast
    field_simp
  rw [hsumR] at ht
  rw [hsumR,ht] at hnode
  have hfactor : 2*(G : ℝ)/2 = G := by ring
  rw [hfactor] at hnode
  have hD : ((2*G-3).factorial : ℝ)*(4*Real.pi^2)^(2*G-3) ≠ 0 := by positivity
  by_cases hj0 : j = 0
  · subst j
    simp [chainProfile_zero]
    exact hε.le
  have hnodeV := diagonal_volume_pos_nonempty P (G-j) (2*j) (by omega)
    (by unfold Stable;omega)
  have hbaseV := hGv G hGv'
  have hlogs : Real.log (volumeModel P (G-j) (2*j)/volumeModel P G 0) =
      Real.log (normalizedVolume P (G-j) (2*j))-Real.log (normalizedVolume P G 0) := by
    simp only [normalizedVolume,hsum,Nat.add_zero]
    rw [Real.log_div hnodeV.ne' hbaseV.ne', Real.log_div hnodeV.ne' hD,
      Real.log_div hbaseV.ne' hD]
    ring
  have hbound := (abs_sub_le (Real.log (normalizedVolume P (G-j) (2*j))-
      (G : ℝ)*chainProfile ((j : ℝ)/G)) 0
      (Real.log (normalizedVolume P G 0))).trans
    (add_le_add (by simpa only [sub_zero] using hnode) (by simpa using hbase))
  rw [hlogs]
  have heq : (Real.log (normalizedVolume P (G-j) (2*j))-
      Real.log (normalizedVolume P G 0))/(G : ℝ)-chainProfile ((j : ℝ)/G) =
      ((Real.log (normalizedVolume P (G-j) (2*j))-
      (G : ℝ)*chainProfile ((j : ℝ)/G))-Real.log (normalizedVolume P G 0))/G := by
    field_simp
    ring
  rw [heq,abs_div,abs_of_pos hGp]
  apply (div_le_iff₀ hGp).mpr
  convert hbound using 1 <;> ring

end WP
