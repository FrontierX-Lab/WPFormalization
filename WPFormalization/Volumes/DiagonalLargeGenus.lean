import WPFormalization.Analysis.ChainCuspSummation
import WPFormalization.Analysis.ChainProfilePrimitive
import WPFormalization.Volumes.DiagonalCuspIncrement
import WPFormalization.Volumes.DiagonalClosedLogarithm

/-! Summing the original cusp-ratio estimate proves the uniform large-genus
part of the full diagonal chain. No logarithmic chain estimate is assumed. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma diagonal_large_genus_of_cusp_ratios (P : PsiTheory)
    (hcusp : ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      |Real.log (normalizedVolume P g n)-((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n) := by
  obtain ⟨C,hC,G,hvol⟩ := hcusp
  obtain ⟨R,hR,hriemann⟩ := Analysis.chain_actual_cusp_riemann_sum
  intro ε hε
  obtain ⟨Gb,hb⟩ := diagonal_closed_logarithm_sublinear P (ε/3) (by positivity)
  have hdiv (A : ℝ) : Tendsto (fun g : ℕ => A/(g : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using inverse_genus_tendsto_zero.const_mul A
  have hevent := (eventually_ge_atTop G).and ((eventually_ge_atTop Gb).and
    ((eventually_ge_atTop 2).and ((diagonal_closed_volume_eventually_pos P).and
      (((hdiv C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))).and
        (((hdiv (2*C+2)).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/3))).and
          ((hdiv R).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/3))))))))
  obtain ⟨G₀,hG₀⟩ := eventually_atTop.mp hevent
  refine ⟨G₀,?_⟩
  intro g hg n
  obtain ⟨hgV,hgB,hg2,hclosed,hsmall,hrate,hRsmall⟩ := hG₀ g hg
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hsteps : ∀ j : ℕ,
      |Real.log (normalizedVolume P g (j+1))-Real.log (normalizedVolume P g j)-
        Analysis.chainCuspLogProfile ((j : ℝ)/g)| ≤ (2*C+2)/g := by
    intro j
    exact diagonal_cusp_log_increment_error P g j hg2 hclosed C hC.le hsmall.le
      (hvol g hgV j)
  have hsum := Analysis.chain_log_increment_sum
    (fun j : ℕ => Real.log (normalizedVolume P g j))
    (fun j : ℕ => Analysis.chainCuspLogProfile ((j : ℝ)/g)) ((2*C+2)/g)
    (by positivity) hsteps n
  have hb' := hb g hgB
  have hr' := hriemann g (by omega) n
  have hsum' : (n : ℝ)*((2*C+2)/g) ≤ (ε/3)*n := by
    nlinarith only [mul_le_mul_of_nonneg_left hrate.le (Nat.cast_nonneg (α := ℝ) n)]
  have hR' : R ≤ (ε/3)*(g : ℝ) := ((div_lt_iff₀ hgr).mp hRsmall).le
  calc
    _ = |(Real.log (normalizedVolume P g n)-Real.log (normalizedVolume P g 0)-
        (∑ j ∈ Finset.range n, Analysis.chainCuspLogProfile ((j : ℝ)/g)))+
          Real.log (normalizedVolume P g 0)+
          ((∑ j ∈ Finset.range n, Analysis.chainCuspLogProfile ((j : ℝ)/g))-
            ((2*(g : ℝ)+n)/2)*chainProfile ((n : ℝ)/(2*g+n)))| := by
      congr 1
      ring
    _ ≤ |Real.log (normalizedVolume P g n)-Real.log (normalizedVolume P g 0)-
          (∑ j ∈ Finset.range n, Analysis.chainCuspLogProfile ((j : ℝ)/g))|+
        |Real.log (normalizedVolume P g 0)|+
        |(∑ j ∈ Finset.range n, Analysis.chainCuspLogProfile ((j : ℝ)/g))-
          ((2*(g : ℝ)+n)/2)*chainProfile ((n : ℝ)/(2*g+n))| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (n : ℝ)*((2*C+2)/g)+(ε/3)*g+R :=
      add_le_add (add_le_add hsum hb') hr'
    _ ≤ ε*(2*g+n) := by
      nlinarith only [hsum',hR',mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) g),
        mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) n)]

end WP
