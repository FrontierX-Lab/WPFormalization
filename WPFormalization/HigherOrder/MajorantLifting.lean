import WPFormalization.HigherOrder.MajorantLocality

/-! Nonnegative real coefficients are lifted through NNReal semiring maps.
Finite substitution commutes with these genuine maps. Therefore the actual
real fixed point gives an ENNReal fixed point, and the proved lexicographic
comparison bounds every extended subsolution without a finiteness premise.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace WP.Majorant
open scoped NNReal ENNReal

lemma substitutionCoeff_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) R)
    (E : Fin m → PowerSeries R) (j : ℕ) :
    φ (substitutionCoeff Φ E j) = substitutionCoeff (MvPowerSeries.map φ Φ)
      (fun l => PowerSeries.map φ (E l)) j := by
  unfold substitutionCoeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  split_ifs
  · rw [map_mul,MvPowerSeries.coeff_map]
    congr 1
    rw [← PowerSeries.coeff_map]
    congr 1
    simp only [map_mul,map_pow,map_prod,PowerSeries.map_X]
  · exact map_zero φ

def nnPhi {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ α, 0 ≤ MvPowerSeries.coeff α Φ) : MvPowerSeries (Option (Fin m)) NNReal :=
  fun α => (⟨MvPowerSeries.coeff α Φ,hΦ α⟩ : NNReal)

def nnSeries (U : PowerSeries ℝ) (hU : ∀ j, 0 ≤ PowerSeries.coeff j U) : PowerSeries NNReal :=
  PowerSeries.mk (R := NNReal) (fun j => (⟨PowerSeries.coeff j U,hU j⟩ : NNReal))

lemma nnSeries_coeff (U : PowerSeries ℝ) (hU : ∀ j, 0 ≤ PowerSeries.coeff j U) (j : ℕ) :
    PowerSeries.coeff j (nnSeries U hU) = (⟨PowerSeries.coeff j U,hU j⟩ : NNReal) := by
  rw [nnSeries,PowerSeries.coeff_mk]

lemma nnPhi_real {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ α, 0 ≤ MvPowerSeries.coeff α Φ) :
    MvPowerSeries.map NNReal.toRealHom (nnPhi Φ hΦ) = Φ := by
  ext α
  rw [MvPowerSeries.coeff_map]
  rfl

lemma nnSeries_real (U : PowerSeries ℝ) (hU : ∀ j, 0 ≤ PowerSeries.coeff j U) :
    PowerSeries.map NNReal.toRealHom (nnSeries U hU) = U := by
  ext j
  rw [PowerSeries.coeff_map]
  simp only [nnSeries,PowerSeries.coeff_mk]
  rfl

lemma nnPhi_extended {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ α, 0 ≤ MvPowerSeries.coeff α Φ) :
    MvPowerSeries.map ENNReal.ofNNRealHom (nnPhi Φ hΦ) = positiveLift Φ := by
  ext α
  simp only [MvPowerSeries.coeff_map]
  change ENNReal.ofNNReal (⟨MvPowerSeries.coeff α Φ,hΦ α⟩ : NNReal) = ENNReal.ofReal (MvPowerSeries.coeff α Φ)
  exact ENNReal.ofReal_coe_nnreal.symm

lemma nnSeries_extended (U : PowerSeries ℝ) (hU : ∀ j, 0 ≤ PowerSeries.coeff j U) :
    PowerSeries.map ENNReal.ofNNRealHom (nnSeries U hU) =
      PowerSeries.mk (fun j => ENNReal.ofReal (PowerSeries.coeff j U)) := by
  ext j
  simp only [PowerSeries.coeff_map,PowerSeries.coeff_mk,nnSeries]
  change ENNReal.ofNNReal (⟨PowerSeries.coeff j U,hU j⟩ : NNReal) = ENNReal.ofReal (PowerSeries.coeff j U)
  exact ENNReal.ofReal_coe_nnreal.symm

lemma nnFixedPoint {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (U : Fin m → PowerSeries ℝ) (hU : ∀ i j, 0 ≤ PowerSeries.coeff j (U i))
    (hfixed : formalFixedPoint Φ U) :
    ∀ i j, PowerSeries.coeff j (nnSeries (U i) (hU i)) =
      substitutionCoeff (nnPhi (Φ i) (hΦ i)) (fun l => nnSeries (U l) (hU l)) j := by
  intro i j
  apply NNReal.coe_injective
  have he := substitutionCoeff_map NNReal.toRealHom (nnPhi (Φ i) (hΦ i))
    (fun l => nnSeries (U l) (hU l)) j
  simp only [nnPhi_real,nnSeries_real] at he
  rw [nnSeries_coeff]
  change PowerSeries.coeff j (U i) = NNReal.toRealHom
    (substitutionCoeff (nnPhi (Φ i) (hΦ i)) (fun l => nnSeries (U l) (hU l)) j)
  rw [he]
  exact hfixed i j

lemma extendedFixedPoint {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (U : Fin m → PowerSeries ℝ) (hU : ∀ i j, 0 ≤ PowerSeries.coeff j (U i))
    (hfixed : formalFixedPoint Φ U) :
    ∀ i j, ENNReal.ofReal (PowerSeries.coeff j (U i)) =
      substitutionCoeff (positiveLift (Φ i)) (fun l => PowerSeries.mk (fun k => ENNReal.ofReal (PowerSeries.coeff k (U l)))) j := by
  intro i j
  have he := congrArg ENNReal.ofNNRealHom (nnFixedPoint Φ hΦ U hU hfixed i j)
  rw [substitutionCoeff_map,nnPhi_extended] at he
  simp_rw [nnSeries_extended] at he
  have hleft := congrArg (PowerSeries.coeff j) (nnSeries_extended (U i) (hU i))
  rw [PowerSeries.coeff_map,PowerSeries.coeff_mk] at hleft
  rw [hleft] at he
  exact he

lemma extended_domination {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hΦ : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (U : Fin m → PowerSeries ℝ) (hU₀ : zeroConstant U) (hfixed : formalFixedPoint Φ U)
    (e : Fin m → ℕ → ℝ≥0∞) (he₀ : ∀ i, e i 0 = 0)
    (he : ∀ i j, 1 ≤ j → e i j ≤ substitutionCoeff (positiveLift (Φ i)) (fun l => PowerSeries.mk (e l)) j) :
    ∀ j i, e i j ≤ ENNReal.ofReal (PowerSeries.coeff j (U i)) := by
  have hnonneg : ∀ i j, 0 ≤ PowerSeries.coeff j (U i) := fun i j => fixedPoint_nonnegative Φ hΦ htri U hU₀ hfixed j i
  let V : Fin m → PowerSeries ℝ≥0∞ := fun i => PowerSeries.mk (fun j => ENNReal.ofReal (PowerSeries.coeff j (U i)))
  have hV₀ : ∀ i, PowerSeries.coeff 0 (V i) = 0 := by intro i; simp [V,hU₀ i]
  have hV : ∀ i j, PowerSeries.coeff j (V i) = substitutionCoeff (positiveLift (Φ i)) V j := by
    intro i j
    simpa [V] using extendedFixedPoint Φ hΦ U hnonneg hfixed i j
  have htri' : ∀ i l : Fin m, i.val ≤ l.val →
      MvPowerSeries.coeff (Finsupp.single (some l) 1) (positiveLift (Φ i)) = 0 := by
    intro i l hil
    change ENNReal.ofReal (MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i)) = 0
    rw [htri i l hil]
    simp
  have hresult := extended_subsolution_le_fixedPoint (fun i => positiveLift (Φ i)) htri' V hV₀ hV e he₀ he
  intro j i
  simpa [V] using hresult j i

end WP.Majorant
