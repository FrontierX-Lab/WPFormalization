import WPFormalization.Volumes.BoundaryGeneratingIdentification
import WPFormalization.Volumes.BoundaryPositiveConvolution

noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

lemma translationWeight_eq_ofReal_real (t : ℝ) (b : ℕ) (Y : ℝ) :
    translationWeight t b (Y:ℂ) = Complex.ofReal (realTranslationWeight t b Y) := by
  rw [translationWeight,←Complex.ofReal_mul,translationKernel_ofReal,
    ←Complex.ofReal_pow,←Complex.ofReal_mul]
  congr 1
  simp [realTranslationWeight,translationWeight,←Complex.ofReal_pow,Complex.mul_re]

lemma boundaryR_ofReal (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    boundaryR P g p L (x:ℂ) = Complex.ofReal
      (a (inverseY x)^(complexity g p) *
        stringBoundaryAmplitude P g (fun i => lengthTime (L i)) 0 (inverseY x)) := by
  classical
  let Y : ℝ := inverseY x
  let T : (Fin p → ℕ) → ℝ := fun b => externalMarkedAmplitude P g 0 b Y *
    ∏ i, realTranslationWeight (lengthTime (L i)) (b i) Y
  have hterm (b : Fin p → ℕ) :
      externalAmplitude P g (List.ofFn b) (x:ℂ) *
        (∏ i, (oddFactorial (b i):ℂ)⁻¹ *
          translationWeight (lengthTime (L i)) (b i) (planarInverse P (x:ℂ))) =
      Complex.ofReal (a Y^(complexity g p) * T b) := by
    rw [externalAmplitude_ofReal P g _ (by simpa using hp) (by simpa using hs) x hx,
      planarInverse_ofReal P x hx]
    simp only [translationWeight_eq_ofReal_real,←Complex.ofReal_natCast,
      ←Complex.ofReal_inv,←Complex.ofReal_mul,←Complex.ofReal_prod,List.length_ofFn]
    apply congrArg Complex.ofReal
    simp only [T,externalMarkedAmplitude,List.replicate_zero,List.nil_append,
      externalOddWeight_zero_prefix]
    have hodd : externalOddWeight (List.ofFn b) = ∏ i,(oddFactorial (b i):ℝ) := by
      simpa only [List.replicate_zero,List.nil_append] using externalOddWeight_zero_prefix 0 p b
    rw [hodd]
    simp only [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
    dsimp only [Y]
    ring
  unfold boundaryR
  simp only [hterm]
  rw [←Complex.ofReal_sum,←Finset.mul_sum]
  apply congrArg Complex.ofReal
  apply congrArg (fun u => a Y^(complexity g p)*u)
  unfold stringBoundaryAmplitude externalStringAmplitude
  simp only [Nat.zero_add]
  change (∑ b ∈ degreeTuples g p,T b) = ∑ b ∈ externalDegreeBox p (dimension g p),T b
  apply Finset.sum_subset
  · intro b hb
    apply (mem_externalDegreeBox p _ b).mpr
    intro i
    have hb' := (mem_degreeTuples_iff g p b).mp hb
    exact (Finset.single_le_sum (fun i _ => Nat.zero_le (b i)) (Finset.mem_univ i)).trans hb'
  · intro b hb hnot
    have hd : dimension g p < ∑ i,b i := lt_of_not_ge (mt (mem_degreeTuples_iff g p b).mpr hnot)
    have hz : shifted P g (List.ofFn b) Y=0 := by
      simp only [shifted,List.length_ofFn,List.sum_ofFn]
      simp [not_le.mpr hd]
    simp only [T,externalMarkedAmplitude,List.replicate_zero,List.nil_append,hz,zero_div,zero_mul]

lemma boundaryG_ofReal (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    boundaryG P g p L (x:ℂ) = Complex.ofReal
      (stringBoundaryAmplitude P g (fun i => lengthTime (L i)) 0 (inverseY x)) := by
  rw [boundaryG,boundaryR_ofReal P g p hp hs L x hx,universalV,planarThird_ofReal P x hx,
    ←Complex.ofReal_pow,←Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have ha := (a_pos _ (inverseY_branch x hx).1).ne'
  rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ ha),one_mul]

end WP.BoundaryConvolution
