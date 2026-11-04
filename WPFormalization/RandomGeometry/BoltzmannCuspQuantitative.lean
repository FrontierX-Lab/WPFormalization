import WPFormalization.Statements.MarkedRatios
import WPFormalization.Tight.ConnectedPoissonPhi
import WPFormalization.Tight.ConnectedVariance

noncomputable section
namespace WP.BoltzmannCusp
open Set

lemma cusp_ratio_perturbation (G H ψ A B R C₀ C₁ C₂ : ℝ)
    (hG : 1≤ G) (hH : 0≤ H) (hHG : H≤2*G) (hψ : 0≤ ψ)
    (hC₀ : 0<C₀) (hC₁ : 0<C₁) (hC₂ : 0<C₂) (hsmall : 2*C₁≤ G)
    (hA : |A-1|≤C₀/G) (hB : |B-1|≤C₁/G) (hR : |R-H*ψ|≤C₂*ψ) :
    |R*A/B-H*ψ|≤(C₂+2*(C₀+C₁)*(2+C₂))*ψ := by
  have hGp : 0<G := by linarith
  have hhalf : C₁/G≤1/2 := (div_le_iff₀ hGp).mpr (by linarith)
  have hBp : 0<B := by have := (abs_sub_le_iff.mp hB).2;linarith
  have hBhalf : 1/2≤B := by have := (abs_sub_le_iff.mp hB).2;linarith
  have hAB : |A-B|≤(C₀+C₁)/G := by
    calc
      |A-B|=|(A-1)-(B-1)| := by congr 1;ring
      _≤|A-1|+|B-1| := abs_sub _ _
      _≤C₀/G+C₁/G := add_le_add hA hB
      _=(C₀+C₁)/G := by ring
  have hQ : |A/B-1|≤2*(C₀+C₁)/G := by
    rw [show A/B-1=(A-B)/B by field_simp
    <;>ring,abs_div,abs_of_pos hBp]
    apply (div_le_iff₀ hBp).mpr
    have hnon : 0≤2*(C₀+C₁)/G := by positivity
    calc
      |A-B|≤(C₀+C₁)/G := hAB
      _=(2*(C₀+C₁)/G)*(1/2) := by ring
      _≤(2*(C₀+C₁)/G)*B := mul_le_mul_of_nonneg_left hBhalf hnon
  have hRabs : |R|≤((2+C₂)*G)*ψ := by
    have ht : |R|≤ H*ψ+C₂*ψ := by
      calc
        |R|=|(R-H*ψ)+H*ψ| := by congr 1;ring
        _≤|R-H*ψ|+|H*ψ| := abs_add_le _ _
        _≤C₂*ψ+H*ψ := by rw [abs_of_nonneg (mul_nonneg hH hψ)];gcongr
        _=H*ψ+C₂*ψ := by ring
    have hstep : C₂≤C₂*G := by nlinarith
    have hh : H+C₂≤(2+C₂)*G := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh hψ]
  calc
    |R*A/B-H*ψ|=|R*(A/B-1)+(R-H*ψ)| := by congr 1;ring
    _≤|R| * |A/B-1|+|R-H*ψ| := by simpa only [abs_mul] using abs_add_le (R*(A/B-1)) (R-H*ψ)
    _≤(((2+C₂)*G)*ψ)*(2*(C₀+C₁)/G)+C₂*ψ := by gcongr
    _=(C₂+2*(C₀+C₁)*(2+C₂))*ψ := by field_simp
    <;>ring

lemma psi_nonneg (x : ℝ) (hx : x∈Ico 0 xCritical) : 0≤Psi x := by
  by_cases hz : x=0
  · simp [hz,Analysis.Psi_zero_value]
  · exact (TightConnected.connected_variance_formula x ⟨lt_of_le_of_ne hx.1 (Ne.symm hz),hx.2⟩).1.le

lemma unmarked_cusp_ratio_error (P : PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ Y∈Ico (0:ℝ) y₀,
      |XR Y*markedF P g 1 (XR Y)/markedF P g 0 (XR Y)-
        (complexity g 0:ℝ)*Psi (XR Y)|≤C*Psi (XR Y) := by
  obtain ⟨C₀,hC₀,N₀,h₀⟩ := (marked_ratios P).2 0
  obtain ⟨C₁,hC₁,N₁,h₁⟩ := (marked_ratios P).2 1
  obtain ⟨C₂,hC₂,N₂,h₂⟩ := (marked_ratios P).1 2 (by omega)
  obtain ⟨N₃,hN₃⟩ := TightConnected.connected_unmarked_positive_eventually P
  obtain ⟨N₄,hN₄⟩ := exists_nat_gt (2*C₁)
  refine ⟨C₂+2*(C₀+C₁)*(2+C₂),by positivity,N₀+N₁+N₂+N₃+N₄+4,?_⟩
  intro g hg Y hY
  have hg4 : 4≤g := by omega
  have hx : XR Y∈Ico (0:ℝ) xCritical := ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
  have hF₀ : markedF P g 0 (XR Y)≠0 := (hN₃ g (by omega) _ hx).ne'
  have hF₁ : markedF P g 1 (XR Y)≠0 :=
    (markedF_positive_cusp_weight P g 1 (by omega) (by unfold Stable;omega) _ hx).ne'
  have hF₂ : markedF P (g-1) 2 (XR Y)≠0 :=
    (markedF_positive_cusp_weight P (g-1) 2 (by omega) (by unfold Stable;omega) _ hx).ne'
  have hr : r Y≠0 := (r_pos Y hY).ne'
  have hc : complexity (g-1) 2=complexity g 0 := by unfold complexity;omega
  have hR := h₂ (g-1) (by omega) Y hY
  rw [hc] at hR
  have hmain := cusp_ratio_perturbation (g:ℝ) (complexity g 0:ℝ) (Psi (XR Y))
    (markedF P (g-1) 2 (XR Y)/(4*r Y*markedF P g 0 (XR Y)))
    (markedF P (g-1) 3 (XR Y)/(4*r Y*markedF P g 1 (XR Y)))
    (XR Y*markedF P (g-1) 3 (XR Y)/markedF P (g-1) 2 (XR Y))
    C₀ C₁ C₂ (by exact_mod_cast (show 1≤g by omega)) (Nat.cast_nonneg _)
    (by exact_mod_cast (show complexity g 0≤2*g by unfold complexity;omega))
    (psi_nonneg _ hx) hC₀ hC₁ hC₂
    (le_of_lt (hN₄.trans_le (by exact_mod_cast (show N₄≤g by omega))))
    (by simpa only [Nat.zero_add] using h₀ g (by omega) Y hY)
    (by norm_num only [Nat.reduceAdd] at *;exact h₁ g (by omega) Y hY) hR
  have hF₃ : markedF P (g-1) 3 (XR Y)≠0 :=
    (markedF_positive_cusp_weight P (g-1) 3 (by omega) (by unfold Stable;omega) _ hx).ne'
  convert hmain using 1
  congr 1
  field_simp [hF₀,hF₁,hF₂,hF₃,hr]
end WP.BoltzmannCusp

namespace WP.BoltzmannCusp
lemma variance_scalar_bound (G H ψ m q C₀ C₁:ℝ)
    (hG:1≤ G) (hH:0≤ H) (hHG:H≤2*G) (hψ:0≤ ψ) (hm:0≤ m)
    (hC₀:0<C₀) (hC₁:0<C₁)
    (hmean:|m-H*ψ|≤C₀*ψ) (hnext:|q-(H+1)*ψ|≤C₁*ψ) :
    m*(q+1-m)≤(2+C₀)*(2+C₀+C₁)*G*(ψ+ψ^2) := by
  have hmup : m≤(2+C₀)*G*ψ := by
    have hh:= (abs_sub_le_iff.mp hmean).1
    have hCG : C₀≤C₀*G := by nlinarith
    have hsum : H+C₀≤(2+C₀)*G := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsum hψ]
  have hqup : q+1-m≤1+(1+C₀+C₁)*ψ := by
    have hlo := (abs_sub_le_iff.mp hmean).2
    have hhi := (abs_sub_le_iff.mp hnext).1
    nlinarith
  calc
    m*(q+1-m)≤ m*(1+(1+C₀+C₁)*ψ) := mul_le_mul_of_nonneg_left hqup hm
    _≤((2+C₀)*G*ψ)*(1+(1+C₀+C₁)*ψ) := by gcongr
    _≤(2+C₀)*(2+C₀+C₁)*G*(ψ+ψ^2) := by
      have hc : 0≤(2+C₀)*G := by positivity
      have ht : ψ*(1+(1+C₀+C₁)*ψ)≤(2+C₀+C₁)*(ψ+ψ^2) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht hc]
end WP.BoltzmannCusp
