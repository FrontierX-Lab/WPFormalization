import WPFormalization.Critical.CutMarkedFamilyBounds
/-! Finite catalogues preserve the quantitative half-power bound of the
actual G.1 ordered cut counts. Catalogue geometry remains a separate producer. -/
noncomputable section
namespace WP.Critical
open WP.External CutGraphOrbits MeasureTheory Filter Finset
open scoped Classical ENNReal

lemma finite_sum_uniform_ofReal_envelope {ι : Type*} (s : Finset ι)
    (ρ : ℕ → ℝ) (hρ : ∀ g, 0 ≤ ρ g) (F : ι → ℕ → ℝ≥0∞)
    (hF : ∀ i ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop, F i g ≤ ENNReal.ofReal (C * ρ g)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g in atTop,
      (∑ i ∈ s, F i g) ≤ ENNReal.ofReal (C * ρ g) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, Eventually.of_forall (fun _ => by simp)⟩
  | @insert i s hi ih =>
    obtain ⟨Ci, hCi, hbi⟩ := hF i (mem_insert_self i s)
    obtain ⟨Cs, hCs, hbs⟩ := ih (fun j hj => hF j (mem_insert_of_mem hj))
    refine ⟨Ci + Cs, add_pos hCi hCs, ?_⟩
    filter_upwards [hbi, hbs] with g hgi hgs
    rw [sum_insert hi]
    calc
      _ ≤ ENNReal.ofReal (Ci * ρ g) + ENNReal.ofReal (Cs * ρ g) := add_le_add hgi hgs
      _ = ENNReal.ofReal ((Ci + Cs) * ρ g) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCi.le (hρ g)) (mul_nonneg hCs.le (hρ g)), add_mul]

universe a b c d
lemma critical_finite_cut_catalog_half_estimate_regime {P : PsiTheory}
    {G : WeilPeterssonGeometry.{a,b} P} {H : HyperbolicCurveGeometry.{a,b,c} G}
    (T : MulticurveTopology.{a,b,c,d} G H) (MI : MirzakhaniIntegration G H T)
    {ι : Type*} [Fintype ι] (k Q u v w : ι → ℕ)
    (S : ∀ i, CutSkeleton (k i) (Q i)) (marked : ι → Bool)
    (hk : ∀ i, 1 ≤ k i) (hQ : ∀ i, 1 ≤ Q i) (hS : ∀ i, (S i).Connected)
    (hbad : ∀ i, marked i = false → w i ≠ 1 ∨ v i ≠ 0)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i) (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop,
      (∑ i, ∫⁻ X, (if marked i then
        cutMarkedPartitionCount T (S i) (g:=g) (n:=n g) (u i) (v i) (w i) (L i) X
        else cutPartitionCount T (S i) (u i) (v i) (w i) (L i) X)
          ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C * (g:ℝ)^(-1/2:ℝ)) := by
  apply finite_sum_uniform_ofReal_envelope univ (fun g => (g:ℝ)^(-1/2:ℝ))
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro i hi
  cases hm : marked i with
  | false =>
    obtain ⟨C, hC, hb⟩ := critical_ordered_nonSurviving_estimate_regime G T MI
      (k i) (Q i) (u i) (v i) (w i) (hk i) (hQ i) (hbad i hm) (L i) (hL i) n c hc hn
    refine ⟨C, hC, hb.mono (fun g hg => ?_)⟩
    simpa only [hm, Bool.false_eq_true, ite_false] using hg (S i) (hS i)
  | true =>
    obtain ⟨C, hC, hb⟩ := critical_ordered_marked_half_estimate_regime T MI
      (k i) (Q i) (u i) (v i) (w i) (hk i) (hQ i) (L i) (hL i) n c hc hn
    refine ⟨C, hC, hb.mono (fun g hg => ?_)⟩
    simpa only [hm, ite_true] using hg (S i) (hS i)
end WP.Critical
