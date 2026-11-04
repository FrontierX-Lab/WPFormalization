import WPFormalization.RandomGeometry.PantsMomentAsymptoticsCutMoments
import WPFormalization.RandomGeometry.PantsProbability
import WPFormalization.RandomGeometry.PantsIntegrability
import WPFormalization.Spectral.VanishingGap

/-! The original Proposition 14.2 concentration argument. The two actual
cut-integral equalities are internal proof inputs, to be supplied by the local
ordered-orbit calculation. They are not fields of any geometric structure. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open Filter MeasureTheory WP.External
open scoped Topology

/-- The original fast-cusp regime implies the actual cusp count diverges. -/
lemma pants_fast_cusps_tendsto_atTop (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) :
    Tendsto n atTop atTop := by
  have hnreal : Tendsto (fun g => (n g:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hn
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
    have hs : 1 ≤ Real.sqrt (g:ℝ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    exact div_le_self (by positivity) hs
  exact tendsto_natCast_atTop_iff.mp hnreal

lemma pants_concentration_of_cut_integrals (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (n : ℕ → ℕ) (L : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hLp : ∀ᶠ g in atTop, 0 < L g) (hL : Tendsto L atTop (𝓝 0))
    (hscale : Tendsto (fun g => pantsScale g (n g)*(L g)^2) atTop atTop)
    (hfirst : ∀ᶠ g in atTop,
      (∫ X, (H.pantsCount X (L g) : ℝ) ∂wpProbability G g (n g)) =
        pantsFirstCutIntegral P g (n g) (L g))
    (hsecond : ∀ᶠ g in atTop,
      (∫ X, (H.pantsCount X (L g) : ℝ)*((H.pantsCount X (L g) : ℝ)-1)
        ∂wpProbability G g (n g)) = pantsSecondCutIntegral P g (n g) (L g)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ε ≤ |(H.pantsCount X (L g) : ℝ)/(pantsScale g (n g)*(L g)^2)-1|})
        atTop (𝓝 0) := by
  have hprob := WP.Spectral.wpProbability_eventually_probability P G n (hn.eventually_ge_atTop 1)
  have hshort : ∀ᶠ g in atTop, L g < 2*Real.arsinh 1 :=
    hL.eventually (gt_mem_nhds (mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))))
  have hX : ∀ᶠ g in atTop,
      MemLp (fun X => (H.pantsCount X (L g) : ℝ)) 2 (wpProbability G g (n g)) := by
    filter_upwards [hprob,hshort,eventually_ge_atTop (1:ℕ)] with g hpg hsg hg
    letI : IsProbabilityMeasure (wpProbability G g (n g)) := hpg
    exact short_pants_memLp T C hg (L g) hsg _ 2
  have hLne : ∀ᶠ g in atTop, L g ≠ 0 := hLp.mono fun _ h => h.ne'
  have hL0 : ∀ᶠ g in atTop, 0 ≤ L g := hLp.mono fun _ h => h.le
  have hm := pants_first_cut_asymptotic P n L hn hL0 hLne hL
  have hf := pants_second_cut_asymptotic P n L hn hL0 hLne hL
  have hmean : Tendsto (fun g =>
      (∫ X, (H.pantsCount X (L g) : ℝ) ∂wpProbability G g (n g))/
        (pantsScale g (n g)*(L g)^2)) atTop (𝓝 1) := by
    apply hm.congr'
    filter_upwards [hfirst] with g hg
    rw [hg]
  have hfactorial : Tendsto (fun g =>
      (∫ X, (H.pantsCount X (L g) : ℝ)*((H.pantsCount X (L g) : ℝ)-1)
        ∂wpProbability G g (n g))/(pantsScale g (n g)*(L g)^2)^2) atTop (𝓝 1) := by
    apply hf.congr'
    filter_upwards [hsecond] with g hg
    rw [hg]
  exact first_second_factorial_concentration_of_eventually (fun g => wpProbability G g (n g))
    hprob (fun g X => (H.pantsCount X (L g) : ℝ)) hX
    (fun g => pantsScale g (n g)*(L g)^2) hscale hmean hfactorial

end WP.RandomGeometry
