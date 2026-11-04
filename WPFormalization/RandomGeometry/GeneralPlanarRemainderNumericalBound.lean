import WPFormalization.RandomGeometry.GeneralPlanarNonstarNumerics
import WPFormalization.RandomGeometry.GeneralPlanarCutVolumeBound
import WPFormalization.RandomGeometry.PrimitivePlanarScale

/-! A fixed finite sum of genuine nonstar volume ratios. Its convergence does
not divide by a limiting cusp weight and remains valid at zero density. -/
noncomputable section
namespace WP.RandomGeometry
open Filter
open scoped Topology

def generalPlanarRemainderNumericalBound (P : PsiTheory) (g n r K : ℕ) (L : ℝ) : ℝ :=
  ((r+1)^(2*r+K):ℕ)*(Real.exp ((r:ℝ)*L)*(generalPlanarZeroVolumeCap P (K+2*r))^r)*
    ∑a∈Finset.range (K+1),∑d∈Finset.range r,
      if r+d≤a then (n:ℝ)^a*volumeModel P g (n-a+d)/volumeModel P g n*(L^2/2)^r else 0

lemma generalPlanarRemainderNumericalBound_tendsto_zero (P : PsiTheory) (r K : ℕ)
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) (t : ℝ) :
    Tendsto (fun g=>generalPlanarRemainderNumericalBound P g (n g) r K
      (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))) atTop (𝓝 0) := by
  have hninf : Tendsto n atTop atTop := by
    have hnreal : Tendsto (fun g=>(n g:ℝ)) atTop atTop := by
      apply tendsto_atTop_mono' atTop _ hn
      filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      have hgR : (1:ℝ)≤g := by exact_mod_cast hg
      have hs : 1≤Real.sqrt (g:ℝ) :=
        (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
      exact div_le_self (by positivity) hs
    exact tendsto_natCast_atTop_iff.mp hnreal
  have hqpos := (primitive_planar_scale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ)
  have hsum : Tendsto (fun g=>∑a∈Finset.range (K+1),∑d∈Finset.range r,
      if r+d≤a then (n g:ℝ)^a*volumeModel P g (n g-a+d)/volumeModel P g (n g)*
        ((t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))^2/2)^r else 0)
      atTop (𝓝 0) := by
    have heach : ∀a∈Finset.range (K+1),∀d∈Finset.range r,
        Tendsto (fun g=>if r+d≤a then (n g:ℝ)^a*volumeModel P g (n g-a+d)/volumeModel P g (n g)*
          ((t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))^2/2)^r else 0) atTop (𝓝 0) := by
      intro a ha d hd
      by_cases hgood : r+d≤a
      · simp only [if_pos hgood]
        have ht := general_planar_nonstar_base_tendsto_zero P r a d (Finset.mem_range.mp hd) hgood n hninf t
        apply ht.congr'
        filter_upwards [hqpos] with g hqg
        have hlen : (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))^2/2=
            t^2/(2*primitivePlanarEffectiveScale g (n g)) := by
          rw [div_pow,Real.sq_sqrt hqg.le]
          ring
        rw [hlen]
        rfl
      · simpa only [if_neg hgood] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
    have hs := tendsto_finsetSum (Finset.range (K+1))
      (fun a ha=>tendsto_finsetSum (Finset.range r) (fun d hd=>heach a ha d hd))
    simpa using hs
  have hL := primitive_planar_rescaled_length_tendsto_zero n hn t
  have hfactor := (((hL.const_mul (r:ℝ)).rexp).mul_const
    ((generalPlanarZeroVolumeCap P (K+2*r))^r)).const_mul (((r+1)^(2*r+K):ℕ):ℝ)
  simpa only [generalPlanarRemainderNumericalBound,mul_zero] using hfactor.mul hsum

end WP.RandomGeometry
