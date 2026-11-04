import WPFormalization.Probability.MarkedFirstPointDefinitions
noncomputable section
namespace WP.Probability
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma isFirstMarkedPoint_gt_iff_void (ξ:PointMeasure MarkedLengthSpace)
    (p:MarkedFirstState) (hp:IsFirstMarkedPoint ξ p) (t:ℝ≥0) :
    (t:ℝ≥0∞)<p.1 ↔ ξ.toMeasure (Iic t ×ˢ (univ:Set ℕ))=0 := by
  by_cases htop:p.1=∞
  · have hz:ξ.toMeasure=0 := by simpa only [IsFirstMarkedPoint,htop,ite_true] using hp
    simp [htop,hz]
  · have hs : ξ.toMeasure {(p.1.toNNReal,p.2)}≠0 ∧
        ξ.toMeasure (Iio p.1.toNNReal ×ˢ (univ:Set ℕ))=0 := by
      simpa only [IsFirstMarkedPoint,if_neg htop] using hp
    have he:(p.1.toNNReal:ℝ≥0∞)=p.1 := ENNReal.coe_toNNReal htop
    constructor
    · intro hlt
      have ht:t<p.1.toNNReal := by exact_mod_cast (hlt.trans_eq he.symm)
      apply measure_mono_null _ hs.2
      intro z hz
      exact ⟨lt_of_le_of_lt hz.1 ht,hz.2⟩
    · intro hzero
      by_contra hn
      have hle:p.1.toNNReal≤t := by exact_mod_cast (he.trans_le (le_of_not_gt hn))
      apply hs.1
      apply measure_mono_null _ hzero
      intro z hz
      rcases mem_singleton_iff.mp hz with rfl
      exact ⟨hle,mem_univ _⟩
end WP.Probability
