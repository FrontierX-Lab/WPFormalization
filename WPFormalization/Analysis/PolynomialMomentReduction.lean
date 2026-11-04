import WPFormalization.Analysis.TransportGammaComplexification
/-! A sequence agreeing with a polynomial after finitely many exceptions has
an exact weighted sum in finitely many genuine kernel moments and low-index
corrections. The same finite expression lifts actual parameter sums to
holomorphic extensions; their convergence or analyticity is never assumed.
Real absolute convergence is included. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

lemma polynomial_weighted_hasSum (w M : ℕ → ℝ)
    (hm : ∀ k : ℕ,HasSum (fun l : ℕ => (l:ℝ)^k*w l) (M k))
    (P : Polynomial ℝ) (D : ℕ) (hD : P.natDegree≤D) :
    HasSum (fun l : ℕ => w l*P.eval (l:ℝ))
      (∑ k∈Finset.range (D+1),P.coeff k*M k) := by
  have hs : HasSum (fun l : ℕ => ∑ k∈Finset.range (D+1),P.coeff k*((l:ℝ)^k*w l))
      (∑ k∈Finset.range (D+1),P.coeff k*M k) := by
    apply hasSum_sum
    intro k hk
    exact (hm k).mul_left _
  convert! hs using 1
  funext l
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma polynomial_tail_weighted_hasSum (w M : ℕ → ℝ)
    (hm : ∀ k : ℕ,HasSum (fun l : ℕ => (l:ℝ)^k*w l) (M k))
    (P : Polynomial ℝ) (D N : ℕ) (hD : P.natDegree≤D) (f : ℕ → ℝ)
    (hf : ∀ l : ℕ,N≤l → f l=P.eval (l:ℝ)) :
    HasSum (fun l : ℕ => w l*f l)
      ((∑ k∈Finset.range (D+1),P.coeff k*M k)+
        ∑ l∈Finset.range N,w l*(f l-P.eval (l:ℝ))) := by
  have hc : HasSum (fun l : ℕ => w l*(f l-P.eval (l:ℝ)))
      (∑ l∈Finset.range N,w l*(f l-P.eval (l:ℝ))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro l hl
    have hlN : N≤l := by simpa only [Finset.mem_range,not_lt] using hl
    rw [hf l hlN,sub_self,mul_zero]
  have hs := (polynomial_weighted_hasSum w M hm P D hD).add hc
  convert! hs using 1
  funext l
  ring

lemma kernel_moment_hasSum_absolute (j : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l : ℕ => (l:ℝ)^j*weight Y l) (WP.HigherOrder.kernelMoment j Y) := by
  obtain ⟨C,hC⟩ := weight_absolute_moments_uniform j
  have hs : Summable (fun l : ℕ => ‖(l:ℝ)^j*weight Y l‖) := by
    apply Summable.of_nonneg_of_le (fun l => norm_nonneg _) _ (hC Y hY).1
    intro l
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (show (0:ℝ)≤(l:ℝ) from Nat.cast_nonneg l)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (show (0:ℝ)≤(l:ℝ) from Nat.cast_nonneg l) (by linarith) j) (abs_nonneg _)
  exact (summable_norm_iff.mp hs).hasSum

lemma kernel_polynomial_tail_hasSum (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀)
    (P : Polynomial ℝ) (D N : ℕ) (hD : P.natDegree≤D) (f : ℕ → ℝ)
    (hf : ∀ l : ℕ,N≤l → f l=P.eval (l:ℝ)) :
    HasSum (fun l : ℕ => weight Y l*f l)
      ((∑ k∈Finset.range (D+1),P.coeff k*WP.HigherOrder.kernelMoment k Y)+
        ∑ l∈Finset.range N,weight Y l*(f l-P.eval (l:ℝ))) := by
  exact polynomial_tail_weighted_hasSum (weight Y) (fun k => WP.HigherOrder.kernelMoment k Y)
    (fun k => kernel_moment_hasSum_absolute k Y hY) P D N hD f hf

lemma dilaton_polynomial_tail_hasSum (Y : ℝ)
    (P : Polynomial ℝ) (D N : ℕ) (hD : P.natDegree≤D) (f : ℕ → ℝ)
    (hf : ∀ l : ℕ,N≤l → f l=P.eval (l:ℝ)) :
    HasSum (fun l : ℕ => canonicalDilatonCoefficient Y l*f l)
      ((∑ k∈Finset.range (D+1),P.coeff k*WP.HigherOrder.bMoment k Y)+
        ∑ l∈Finset.range N,canonicalDilatonCoefficient Y l*(f l-P.eval (l:ℝ))) := by
  exact polynomial_tail_weighted_hasSum (canonicalDilatonCoefficient Y) (fun k => WP.HigherOrder.bMoment k Y)
    (fun k => WP.HigherOrder.bMoment_hasSum k Y) P D N hD f hf
end WP.Analysis
namespace WP.Analysis

lemma HasPhysicalHolomorphicExtension.congr_on_physical {Ω : Set ℂ} {f g : ℝ → ℝ}
    (hf : HasPhysicalHolomorphicExtension Ω f) (he : ∀ Y∈Icc (0:ℝ) y₀,f Y=g Y) :
    HasPhysicalHolomorphicExtension Ω g := by
  obtain ⟨F,hF,hFr⟩ := hf
  refine ⟨F,hF,?_⟩
  intro Y hY
  exact (hFr Y hY).trans (congrArg Complex.ofReal (he Y hY))

lemma HasPolynomialPhysicalExtension.eval_of_natDegree_le {Ω : Set ℂ} {P : ℝ → Polynomial ℝ}
    (hP : HasPolynomialPhysicalExtension Ω P) (D : ℕ)
    (hD : ∀ Y∈Icc (0:ℝ) y₀,(P Y).natDegree≤D) (x : ℝ) :
    HasPhysicalHolomorphicExtension Ω (fun Y => (P Y).eval x) := by
  have hf : HasPhysicalHolomorphicExtension Ω
      (fun Y => ∑ k∈Finset.range (D+1),(P Y).coeff k*x^k) :=
    HasPhysicalHolomorphicExtension.sum _ _ (fun k => (hP k).mul (HasPhysicalHolomorphicExtension.const Ω (x^k)))
  exact hf.congr_on_physical (fun Y hY => (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hD Y hY)) x).symm)

lemma polynomial_tail_weighted_holomorphic (Ω : Set ℂ) (w : ℝ → ℕ → ℝ) (M : ℕ → ℝ → ℝ)
    (hm : ∀ Y∈Icc (0:ℝ) y₀,∀ k : ℕ,HasSum (fun l : ℕ => (l:ℝ)^k*w Y l) (M k Y))
    (hM : ∀ k : ℕ,HasPhysicalHolomorphicExtension Ω (M k))
    (hw : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => w Y l))
    (P : ℝ → Polynomial ℝ) (hP : HasPolynomialPhysicalExtension Ω P) (D N : ℕ)
    (hD : ∀ Y∈Icc (0:ℝ) y₀,(P Y).natDegree≤D) (f : ℝ → ℕ → ℝ)
    (hf : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => f Y l))
    (htail : ∀ Y∈Icc (0:ℝ) y₀,∀ l : ℕ,N≤l → f Y l=(P Y).eval (l:ℝ)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => ∑'l : ℕ,w Y l*f Y l) := by
  have he : HasPhysicalHolomorphicExtension Ω (fun Y =>
      (∑ k∈Finset.range (D+1),(P Y).coeff k*M k Y)+
        ∑ l∈Finset.range N,w Y l*(f Y l-(P Y).eval (l:ℝ))) := by
    apply HasPhysicalHolomorphicExtension.add
    · exact HasPhysicalHolomorphicExtension.sum _ _ (fun k => (hP k).mul (hM k))
    · exact HasPhysicalHolomorphicExtension.sum _ _ (fun l =>
        (hw l).mul ((hf l).sub (hP.eval_of_natDegree_le D hD (l:ℝ))))
  apply he.congr_on_physical
  intro Y hY
  exact (polynomial_tail_weighted_hasSum (w Y) (fun k => M k Y) (hm Y hY) (P Y) D N (hD Y hY)
    (f Y) (htail Y hY)).tsum_eq.symm

lemma kernel_polynomial_tail_holomorphic (Ω : Set ℂ)
    (hM : ∀ k : ℕ,HasPhysicalHolomorphicExtension Ω (WP.HigherOrder.kernelMoment k))
    (hw : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => weight Y l))
    (P : ℝ → Polynomial ℝ) (hP : HasPolynomialPhysicalExtension Ω P) (D N : ℕ)
    (hD : ∀ Y∈Icc (0:ℝ) y₀,(P Y).natDegree≤D) (f : ℝ → ℕ → ℝ)
    (hf : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => f Y l))
    (htail : ∀ Y∈Icc (0:ℝ) y₀,∀ l : ℕ,N≤l → f Y l=(P Y).eval (l:ℝ)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => ∑'l : ℕ,weight Y l*f Y l) := by
  exact polynomial_tail_weighted_holomorphic Ω weight WP.HigherOrder.kernelMoment
    (fun Y hY k => kernel_moment_hasSum_absolute k Y hY) hM hw P hP D N hD f hf htail

lemma dilaton_polynomial_tail_holomorphic (Ω : Set ℂ)
    (hM : ∀ k : ℕ,HasPhysicalHolomorphicExtension Ω (WP.HigherOrder.bMoment k))
    (hb : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => canonicalDilatonCoefficient Y l))
    (P : ℝ → Polynomial ℝ) (hP : HasPolynomialPhysicalExtension Ω P) (D N : ℕ)
    (hD : ∀ Y∈Icc (0:ℝ) y₀,(P Y).natDegree≤D) (f : ℝ → ℕ → ℝ)
    (hf : ∀ l : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => f Y l))
    (htail : ∀ Y∈Icc (0:ℝ) y₀,∀ l : ℕ,N≤l → f Y l=(P Y).eval (l:ℝ)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => ∑'l : ℕ,canonicalDilatonCoefficient Y l*f Y l) := by
  exact polynomial_tail_weighted_holomorphic Ω canonicalDilatonCoefficient WP.HigherOrder.bMoment
    (fun Y hY k => WP.HigherOrder.bMoment_hasSum k Y) hM hb P hP D N hD f hf htail
end WP.Analysis
namespace WP.Analysis
lemma polynomial_tail_weighted_abs_summable (w M : ℕ → ℝ)
    (hm : ∀ k : ℕ,HasSum (fun l : ℕ => (l:ℝ)^k*w l) (M k))
    (P : Polynomial ℝ) (D N : ℕ) (hD : P.natDegree≤D) (f : ℕ → ℝ)
    (hf : ∀ l : ℕ,N≤l → f l=P.eval (l:ℝ)) :
    Summable (fun l : ℕ => |w l*f l|) := by
  simpa only [Real.norm_eq_abs] using
    (polynomial_tail_weighted_hasSum w M hm P D N hD f hf).summable.norm
end WP.Analysis
