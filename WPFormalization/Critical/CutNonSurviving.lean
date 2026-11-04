import WPFormalization.Critical.CutUnorderedEstimate
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter
open scoped ENNReal Topology Classical

lemma nonSurviving_cut_exponent {w v : ℕ} (hw : 1 ≤ w) (hbad : w≠1 ∨ v≠0) :
    1-(w:ℝ)-(v:ℝ)/2 ≤ (-1/2:ℝ) := by
  have hv0 : (0:ℝ) ≤ v := Nat.cast_nonneg _
  by_cases hw1 : w=1
  · have hv : 1 ≤ v := by omega
    have hvR : (1:ℝ) ≤ v := by exact_mod_cast hv
    simp only [hw1,Nat.cast_one]
    linarith
  · have hw2 : 2 ≤ w := by omega
    have hwR : (2:ℝ) ≤ w := by exact_mod_cast hw2
    linarith

namespace CutGraphOrbits
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n k Q : ℕ} (S : CutSkeleton k Q)
lemma unorderedCutCount_empty (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    unorderedCutCount T (∅ : Finset (Orbits T S (g:=g) (n:=n))) L X=0 := by
  unfold unorderedCutCount
  apply ENNReal.tsum_eq_zero.mpr
  intro U
  obtain ⟨j,hj,hL⟩ := U.property
  exact (Finset.notMem_empty j.1.val j.1.property).elim
end CutGraphOrbits

lemma critical_unordered_nonSurviving_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hbad : w≠1 ∨ v≠0)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,hr⟩ := critical_unordered_cut_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn
    refine ⟨C,hC,?_⟩
    filter_upwards [hr,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (nonSurviving_cut_exponent hw hbad)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    simp only [partitionOrbits_zero_stable T S u v hg,unorderedCutCount_empty,lintegral_zero]
    exact bot_le

lemma critical_ordered_nonSurviving_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hbad : w≠1 ∨ v≠0)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n g) u v w L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,hr⟩ := critical_cut_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn
    refine ⟨C,hC,?_⟩
    filter_upwards [hr,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (nonSurviving_cut_exponent hw hbad)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    simp only [cutPartitionCount,partitionOrbits_zero_stable T S u v hg,Finset.sum_empty,lintegral_zero]
    exact bot_le

lemma critical_half_power_tendsto_zero :
    Tendsto (fun g : ℕ => (g:ℝ)^(-1/2:ℝ)) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have he : (fun g : ℕ => (g:ℝ)^(-1/2:ℝ)) = (fun g : ℕ => (Real.sqrt (g:ℝ))⁻¹) := by
    funext g
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by ring,Real.rpow_neg (Nat.cast_nonneg g),←Real.sqrt_eq_rpow]
  rw [he]
  exact h
lemma critical_unordered_marked_half_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  by_cases hw : 1 ≤ w
  · obtain ⟨C,hC,hr⟩ := critical_unordered_cut_marked_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn
    refine ⟨C,hC,?_⟩
    filter_upwards [hr,eventually_ge_atTop (1:ℕ)] with g hg hg1
    intro S hS
    refine (hg S hS).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hwR : (1:ℝ) ≤ w := by exact_mod_cast hw
    have hvR : (0:ℝ) ≤ v := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hg1) (by linarith)
  · have hw0 : w=0 := by omega
    subst w
    refine ⟨1,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop (k+2)] with g hg
    intro S hS
    have hempty := markedPartitionOrbits_zero_stable T S (n:=n g) u v hg
    simp only [hempty,unorderedCutCount_empty,lintegral_zero]
    exact bot_le

lemma critical_unordered_nonSurviving_tendsto_zero {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hbad : w≠1 ∨ v≠0)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (S : CutSkeleton k Q) (hS : S.Connected) :
    Tendsto (fun g : ℕ => ∫⁻ X,
      unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := critical_unordered_nonSurviving_estimate_regime G T MI k Q u v w hk hQ hbad L hL n c hc hn
  have ht : Tendsto (fun g : ℕ => ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le)) (hbound.mono (fun _ hg => hg S hS))

lemma critical_ordered_nonSurviving_tendsto_zero {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hbad : w≠1 ∨ v≠0)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (S : CutSkeleton k Q) (hS : S.Connected) :
    Tendsto (fun g : ℕ => ∫⁻ X,
      cutPartitionCount T S (g:=g) (n:=n g) u v w L X
        ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := critical_ordered_nonSurviving_estimate_regime G T MI k Q u v w hk hQ hbad L hL n c hc hn
  have ht : Tendsto (fun g : ℕ => ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le)) (hbound.mono (fun _ hg => hg S hS))

lemma critical_unordered_marked_tendsto_zero {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (L : ℝ) (hL : 0 ≤ L) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (S : CutSkeleton k Q) (hS : S.Connected) :
    Tendsto (fun g : ℕ => ∫⁻ X,
      unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := critical_unordered_marked_half_estimate_regime G T MI k Q u v w hk hQ L hL n c hc hn
  have ht : Tendsto (fun g : ℕ => ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul critical_half_power_tendsto_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall (fun _ => bot_le)) (hbound.mono (fun _ hg => hg S hS))

end WP.Critical
