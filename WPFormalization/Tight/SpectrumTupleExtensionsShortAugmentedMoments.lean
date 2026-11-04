import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments

noncomputable section
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H}

lemma shortAugmentedTuple_iff_scaled_goodSet {g n r : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (α : ℝ) (hα : 0<α) (lo hi : Fin r→ℝ) (ε : ℝ)
    (Δ : Fin (r+1)→Curve Q X) :
    ShortAugmentedTuple Q X (fun i=>lo i/α) (fun i=>hi i/α) (ε/α) Δ ↔
      GoodSetTuple Q X
        (fun i=>(fun l=>α*l) ⁻¹' (Fin.snoc (fun j : Fin r=>(Icc (lo j) (hi j) : Set ℝ)) (Icc (0:ℝ) ε) : Fin (r+1)→Set ℝ) i) Δ := by
  constructor
  · rintro ⟨hgood,hpref,hlast⟩
    refine ⟨hgood,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [Fin.snoc_last, Set.mem_preimage]
      exact ⟨mul_nonneg hα.le (Q.length_pos _).le,
        by simpa only [mul_comm] using (le_div_iff₀ hα).mp hlast⟩
    · simp only [Fin.snoc_castSucc, Set.mem_preimage]
      have heq : Fin.castAdd 1 j=j.castSucc := Fin.ext rfl
      exact ⟨by simpa only [mul_comm,heq] using (div_le_iff₀ hα).mp (hpref j).1,
        by simpa only [mul_comm,heq] using (le_div_iff₀ hα).mp (hpref j).2⟩
  · rintro ⟨hgood,hwin⟩
    refine ⟨hgood,?_,?_⟩
    · intro j
      have h := hwin j.castSucc
      simp only [Fin.snoc_castSucc, Set.mem_preimage] at h
      change α*Q.length (Δ j.castSucc)∈Icc (lo j) (hi j) at h
      have heq : Fin.castAdd 1 j=j.castSucc := Fin.ext rfl
      exact ⟨(div_le_iff₀ hα).mpr (by simpa only [mul_comm,heq] using h.1),
        (le_div_iff₀ hα).mpr (by simpa only [mul_comm,heq] using h.2)⟩
    · have h := hwin (Fin.last r)
      simp only [Fin.snoc_last, Set.mem_preimage] at h
      change α*Q.length (Δ (Fin.last r))∈Icc (0:ℝ) ε at h
      exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using h.2)

def scaledShortAugmentedCount (Q : TightGeodesicGeometry G T H)
    (g r n : ℕ) (lo hi : Fin r→ℝ) (ε : ℝ)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : ℕ :=
  Nat.card {Δ : Fin (r+1)→Curve Q X //
    ShortAugmentedTuple Q X
      (fun i=>lo i/tightScale ((n:ℝ)/g)) (fun i=>hi i/tightScale ((n:ℝ)/g))
      (ε/tightScale ((n:ℝ)/g)) Δ}

lemma scaled_short_augmented_count_eq_goodSet {g n r : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (lo hi : Fin r→ℝ) (ε : ℝ) :
    scaledShortAugmentedCount Q g r n lo hi ε X =
      scaledGoodSetCount Q g (r+1) n
        (Fin.snoc (fun j=>Icc (lo j) (hi j)) (Icc (0:ℝ) ε)) X := by
  exact Nat.card_congr ((Equiv.refl _).subtypeEquiv (fun Δ=>
    shortAugmentedTuple_iff_scaled_goodSet X _
      (TightConnected.tightScale_pos _ (by positivity)) lo hi ε Δ))

lemma scaled_short_augmented_count_expectation_tendsto (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (lo hi : Fin r→ℝ) (hlo : ∀i,0≤lo i)
    (B : ℝ) (hB : 0≤B) (hhi : ∀i,hi i≤B) (ε : ℝ) :
    Tendsto (fun j=>∫⁻X,(scaledShortAugmentedCount Q (gs j) r (ns j) lo hi ε X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 ((∏i,tightIntensity (Icc (lo i) (hi i)))*tightIntensity (Icc (0:ℝ) ε))) := by
  let I : Fin (r+1)→Set ℝ := Fin.snoc (fun j=>Icc (lo j) (hi j)) (Icc (0:ℝ) ε)
  have hI : ∀i,MeasurableSet (I i) := by
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [I,Fin.snoc_last] using (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) ε))
    · simpa only [I,Fin.snoc_castSucc] using (measurableSet_Icc : MeasurableSet (Icc (lo j) (hi j)))
  have hIB : ∀i,I i⊆Icc (0:ℝ) (max B ε) := by
    intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · intro t ht
      simp only [I,Fin.snoc_last] at ht
      exact ⟨ht.1,ht.2.trans (le_max_right _ _)⟩
    · intro t ht
      simp only [I,Fin.snoc_castSucc] at ht
      exact ⟨(hlo j).trans ht.1,ht.2.trans ((hhi j).trans (le_max_left _ _))⟩
  have ht := scaled_good_set_count_expectation_tendsto T BZ Q A MI (r+1) gs ns hgs I hI
    (max B ε) (hB.trans (le_max_left _ _)) hIB
  have hprod : (∏i,tightIntensity (I i))=
      (∏i,tightIntensity (Icc (lo i) (hi i)))*tightIntensity (Icc (0:ℝ) ε) := by
    rw [Fin.prod_univ_castSucc]
    simp only [I,Fin.snoc_castSucc,Fin.snoc_last]
  rw [hprod] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  apply lintegral_congr
  intro X
  exact congrArg (fun q : ℕ=>(q:ℝ≥0∞))
    (scaled_short_augmented_count_eq_goodSet X lo hi ε).symm

lemma scaled_short_augmented_const_expectation_tendsto (T : TightRegions G)
    (BZ : BuddZonneveldTransform G T) (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A)
    (r : ℕ) (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    (a B ε : ℝ) (ha : 0≤a) (hB : 0≤B) :
    Tendsto (fun j=>∫⁻X,
      (scaledShortAugmentedCount Q (gs j) r (ns j) (fun _=>a) (fun _=>B) ε X : ℝ≥0∞)
      ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop
      (𝓝 (tightIntensity (Icc (0:ℝ) ε)*tightIntensity (Icc a B)^r)) := by
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_comm] using
    scaled_short_augmented_count_expectation_tendsto T BZ Q A MI r gs ns hgs
      (fun _=>a) (fun _=>B) (fun _=>ha) B hB (fun _=>le_rfl) ε

end WP.Tight
