import WPFormalization.HigherOrder.LargeWeightRemainder
/-! The proved actual canonical coefficient bounds remain valid on any
larger common order/degree scale. The constants precede all scales,
marking counts, tuples and indices. This is a consequence of C.4. -/
noncomputable section
namespace WP.HigherOrder
lemma canonical_coefficients_on_common_scale (P:PsiTheory) :
    ∃C B:ℝ,∃M₀:ℕ,0<C ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀p:ℕ,1 ≤ p→∀d:List ℕ,1 ≤ d.length→∀q:ℕ,∀T:ℝ,
    scalarOrderWeight (M:ℝ) q p ≤ T→profileOrderWeight (M:ℝ) q d ≤ T→
    ∀i:ℕ,i ≤ q→∀Y∈Set.Icc (0:ℝ) y₀,
      |PowerSeries.coeff i (formalCusp P Y p)| ≤ C*B^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalGenus P Y p)| ≤ C*B^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalProfile P Y d)| ≤ C*B^i*T^(2*i) :=by
  obtain ⟨C,B,M₀,hC,hB,hM₀,hprof,hscal⟩:=canonical_real_coefficient_bounds P
  refine ⟨C,B,M₀,hC,hB,hM₀,?_⟩
  intro M hM p hp d hd q T hTs hTp i hi Y hY
  have hm:=mul_le_mul (show (M₀:ℝ) ≤ M by exact_mod_cast hM)
    (show (i:ℝ) ≤ q by exact_mod_cast hi) (Nat.cast_nonneg i : (0:ℝ) ≤ i) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hweightS:scalarOrderWeight (M₀:ℝ) i p ≤ T:=by
    apply LE.le.trans _ hTs
    unfold scalarOrderWeight
    linarith
  have hweightP:profileOrderWeight (M₀:ℝ) i d ≤ T:=by
    apply LE.le.trans _ hTp
    unfold profileOrderWeight
    linarith
  have hSB:|cuspCoefficient P Y p i|+|genusCoefficient P Y p i| ≤ C*B^i*T^(2*i):=by
    exact (hscal i p hp Y hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold scalarOrderWeight;positivity) hweightS _) (by positivity))
  have hPB:|profileCoefficient P Y d i| ≤ C*B^i*T^(2*i):=by
    exact (hprof i d hd Y hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold profileOrderWeight;positivity) hweightP _) (by positivity))
  simp only[formalCusp,formalGenus,formalProfile,PowerSeries.coeff_mk]
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans hSB,
    (le_add_of_nonneg_left (abs_nonneg _)).trans hSB,hPB⟩
end WP.HigherOrder
