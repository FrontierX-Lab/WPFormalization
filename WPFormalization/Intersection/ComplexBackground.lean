import WPFormalization.Analysis.ComplexKernelGeometricBounds
import WPFormalization.Analysis.FiniteKernelDataComplex
import WPFormalization.Intersection.PositiveRecursion
import WPFormalization.Intersection.CriticalHomogeneity
/-! Explicit complex finite-background amplitudes extend the actual normalized
PsiTheory quantities, including critical, top, unstable and excessive-degree
states. The finite positive recursion and the full finite dilaton identity
continue by the complex identity principle. Their real restrictions are
proved from the canonical finite background formula; no complex recursion
or amplitude is supplied as an input field. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

def complexBackgroundTime (R : ℂ → ℂ) (i : ℕ) (z : ℂ) : ℂ :=
  -(oddFactorial (i+1):ℂ)*regularizedKernelCoeff K R (i+1) z

def complexBackgroundAmplitude (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℂ) : ℂ :=
  (doubleWeight d:ℂ)*∑ l∈backgroundVectors N B m,
    (P.psi g (d++(backgroundDegrees l).map Int.ofNat):ℂ)*
      ∏ i : Fin N,t i^(l i)/(l i).factorial

def complexNormalized (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℕ) (z : ℂ) : ℂ :=
  if Stable g d.length ∧ d.sum≤dimension g d.length then
    complexBackgroundAmplitude P g (d.map Int.ofNat) (deficit g d) (deficit g d)
      (fun i : Fin (deficit g d+1) => complexBackgroundTime R i.val z)
  else 0

def complexPiSigned (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℤ) (z : ℂ) : ℂ :=
  if ∀ k∈d,0≤k then complexNormalized P R g (d.map Int.toNat) z else 0

def complexNormalizedChildren (P : PsiTheory) (R : ℂ → ℂ) (g p : ℕ) (d : List ℤ) (z : ℂ) : ℂ :=
  (∑ j∈Finset.range d.length,(2*(d[j]!:ℂ)+1)*complexPiSigned P R g (((p:ℤ)+d[j]!-1)::d.eraseIdx j) z)+
  (if g=0 then 0 else (1/2:ℂ)*∑ u∈Finset.range (p-1),complexPiSigned P R (g-1) ((u:ℤ)::((p:ℤ)-2-u)::d) z)+
  (1/2:ℂ)*∑ u∈Finset.range (p-1),∑ g₁∈Finset.range (g+1),∑ I∈(Finset.range d.length).powerset,
    complexPiSigned P R g₁ ((u:ℤ)::selected d I) z*
      complexPiSigned P R (g-g₁) (((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)) z

lemma complexBackgroundAmplitude_analyticOnNhd (Ω : Set ℂ) (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : ℂ → Fin N → ℂ)
    (ht : ∀ i,AnalyticOnNhd ℂ (fun z => t z i) Ω) :
    AnalyticOnNhd ℂ (fun z => complexBackgroundAmplitude P g d B m (t z)) Ω := by
  intro z hz
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro l hl
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact ((ht i z hz).pow (l i)).div_const

lemma complexNormalized_analyticOnNhd (Ω : Set ℂ) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω) (g : ℕ) (d : List ℕ) :
    AnalyticOnNhd ℂ (complexNormalized P R g d) Ω := by
  by_cases hs : Stable g d.length ∧ d.sum≤dimension g d.length
  · have he : complexNormalized P R g d=(fun z =>
        complexBackgroundAmplitude P g (d.map Int.ofNat) (deficit g d) (deficit g d)
          (fun i : Fin (deficit g d+1) => complexBackgroundTime R i.val z)) := by
      funext z
      simp only [complexNormalized,ite_eq_left hs]
    rw [he]
    exact complexBackgroundAmplitude_analyticOnNhd Ω P g (d.map Int.ofNat) _ _ _
      (fun i z hz => analyticAt_const.mul (hK (i.val+1) z hz))
  · have he : complexNormalized P R g d=(fun _ : ℂ => 0) := by
      funext z
      simp only [complexNormalized,ite_eq_right hs]
    rw [he]
    exact analyticOnNhd_const

lemma complexBackgroundAmplitude_ofReal (P : PsiTheory) (g : ℕ) (d : List ℤ)
    {N : ℕ} (B m : ℕ) (t : Fin N → ℝ) :
    complexBackgroundAmplitude P g d B m (fun i => (t i:ℂ))=(finiteBackgroundAmplitude P g d B m t:ℂ) := by
  unfold complexBackgroundAmplitude finiteBackgroundAmplitude
  push_cast
  rfl

lemma complexBackgroundTime_restrict_closed (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (i : ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexBackgroundTime R i (Y:ℂ)=(normalizedBackgroundTime Y i:ℂ) := by
  unfold complexBackgroundTime
  rw [hK (i+1) Y hY]
  have hr : WP.coeff (barK Y) (i+1)=((realCoeff (barK Y) (i+1):ℝ):ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using barK_realCoefficients Y (i+1)
  rw [hr]
  simp only [normalizedBackgroundTime,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_natCast]

lemma complexNormalized_restrict_closed (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (g : ℕ) (d : List ℕ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexNormalized P R g d (Y:ℂ)=(normalized P g d Y:ℂ) := by
  by_cases hs : Stable g d.length
  · by_cases hd : d.sum≤dimension g d.length
    · rw [complexNormalized,ite_eq_left ⟨hs,hd⟩]
      have ht : (fun i : Fin (deficit g d+1) => complexBackgroundTime R i.val (Y:ℂ))=
          (fun i => ((normalizedBackgroundTime Y i.val:ℝ):ℂ)) :=
        funext (fun i => complexBackgroundTime_restrict_closed R hK i.val Y hY)
      rw [ht,complexBackgroundAmplitude_ofReal]
      congr 1
      exact finiteBackgroundAmplitude_normalized_canonical P g d Y hY hs hd
        (deficit g d+1) (deficit g d) (by omega) (by omega) le_rfl
    · rw [complexNormalized,ite_eq_right (by tauto),normalized_excess P g d Y (by omega)]
      norm_num
  · rw [complexNormalized,ite_eq_right (by tauto),normalized_unstable P g d Y hs]
    norm_num

lemma complexNormalized_unstable (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℕ)
    (hs : ¬Stable g d.length) (z : ℂ) : complexNormalized P R g d z=0 := by
  simp only [complexNormalized,ite_eq_right (show ¬(Stable g d.length ∧ d.sum≤dimension g d.length) by tauto)]

lemma complexNormalized_excess (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℕ)
    (hd : dimension g d.length<d.sum) (z : ℂ) : complexNormalized P R g d z=0 := by
  simp only [complexNormalized,ite_eq_right (show ¬(Stable g d.length ∧ d.sum≤dimension g d.length) by omega)]

lemma complexPiSigned_analyticOnNhd (Ω : Set ℂ) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω) (g : ℕ) (d : List ℤ) :
    AnalyticOnNhd ℂ (complexPiSigned P R g d) Ω := by
  by_cases hd : ∀ k∈d,0≤k
  · have he : complexPiSigned P R g d=complexNormalized P R g (d.map Int.toNat) := by
      funext z
      simp only [complexPiSigned,ite_eq_left hd]
    rw [he]
    exact complexNormalized_analyticOnNhd Ω P R hK g _
  · have he : complexPiSigned P R g d=(fun _ : ℂ => 0) := by
      funext z
      simp only [complexPiSigned,ite_eq_right hd]
    rw [he]
    exact analyticOnNhd_const

lemma complexPiSigned_restrict_closed (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (g : ℕ) (d : List ℤ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexPiSigned P R g d (Y:ℂ)=(piSigned P g d Y:ℂ) := by
  unfold complexPiSigned piSigned
  split_ifs
  · exact complexNormalized_restrict_closed P R hK g _ Y hY
  · simp
end WP.Analysis
namespace WP.Analysis
lemma complexNormalizedChildren_analyticOnNhd (Ω : Set ℂ) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω) (g p : ℕ) (d : List ℤ) :
    AnalyticOnNhd ℂ (complexNormalizedChildren P R g p d) Ω := by
  intro z hz
  unfold complexNormalizedChildren
  apply AnalyticAt.add
  · apply AnalyticAt.add
    · apply Finset.analyticAt_fun_sum
      intro j hj
      exact analyticAt_const.mul (complexPiSigned_analyticOnNhd Ω P R hK g _ z hz)
    · by_cases hg : g=0
      · simp only [ite_eq_left hg]
        exact analyticAt_const
      · simp only [ite_eq_right hg]
        apply AnalyticAt.mul analyticAt_const
        apply Finset.analyticAt_fun_sum
        intro u hu
        exact complexPiSigned_analyticOnNhd Ω P R hK (g-1) _ z hz
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_sum
    intro u hu
    apply Finset.analyticAt_fun_sum
    intro g₁ hg₁
    apply Finset.analyticAt_fun_sum
    intro I hI
    exact (complexPiSigned_analyticOnNhd Ω P R hK g₁ _ z hz).mul
      (complexPiSigned_analyticOnNhd Ω P R hK (g-g₁) _ z hz)

lemma complexNormalizedChildren_restrict_closed (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (g p : ℕ) (d : List ℤ) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    complexNormalizedChildren P R g p d (Y:ℂ)=(normalizedChildren P g p d Y:ℂ) := by
  have hr : normalizedChildren P g p d Y=
      (∑ j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*piSigned P g (((p:ℤ)+d[j]!-1)::d.eraseIdx j) Y)+
      (if g=0 then 0 else (1/2:ℝ)*∑ u∈Finset.range (p-1),piSigned P (g-1) ((u:ℤ)::((p:ℤ)-2-u)::d) Y)+
      (1/2:ℝ)*∑ u∈Finset.range (p-1),∑ g₁∈Finset.range (g+1),∑ I∈(Finset.range d.length).powerset,
        piSigned P g₁ ((u:ℤ)::selected d I) Y*
          piSigned P (g-g₁) (((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)) Y := rfl
  rw [hr]
  unfold complexNormalizedChildren
  push_cast
  simp_rw [complexPiSigned_restrict_closed P R hK _ _ Y hY]
  split_ifs <;> push_cast <;> rfl

lemma holomorphic_identity_of_closed_physical (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (he : ∀ Y∈Icc (0:ℝ) y₀,f (Y:ℂ)=g (Y:ℂ)) : EqOn f g Ω := by
  have hc : y₀/2∈Ioo (0:ℝ) y₀ := ⟨half_pos y₀_pos,half_lt_self y₀_pos⟩
  apply complex_identity_of_real_germ f g Ω (y₀/2) hf hg hconn (hcover _ ⟨hc.1.le,hc.2.le⟩)
  filter_upwards [isOpen_Ioo.mem_nhds hc] with Y hY
  exact he Y ⟨hY.1.le,hY.2.le⟩

lemma complexNormalized_positive_convolution (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (g pivot : ℕ) (d : List ℕ) (hh : 2≤complexity g (d.length+1))
    (hd : (pivot::d).sum≤dimension g (d.length+1)) :
    ∀ z∈Ω,complexNormalized P R g (pivot::d) z=
      ∑ l∈Finset.range (deficit g (pivot::d)+1),complexThetaCoeff R l z*
        complexNormalizedChildren P R g (pivot+l) (d.map Int.ofNat) z := by
  have hθ := complexThetaCoeff_analyticOnNhd Ω R hK
  apply holomorphic_identity_of_closed_physical Ω hconn hcover _ _ (complexNormalized_analyticOnNhd Ω P R hK g _) _ _
  · intro z hz
    apply Finset.analyticAt_fun_sum
    intro l hl
    exact (hθ l z hz).mul (complexNormalizedChildren_analyticOnNhd Ω P R hK g (pivot+l) _ z hz)
  · intro Y hY
    rw [complexNormalized_restrict_closed P R hKr g _ Y hY,
      normalized_positive_convolution P g pivot d Y hh hd hY]
    push_cast
    apply Finset.sum_congr rfl
    intro l hl
    rw [complexThetaCoeff_restrict_closed R hKr l Y hY,
      complexNormalizedChildren_restrict_closed P R hKr g (pivot+l) _ Y hY]

lemma complexNormalized_top (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (g : ℕ) (d : List ℕ) (hd : d.sum=dimension g d.length) :
    ∀ z∈Ω,complexNormalized P R g d z=(normalized P g d y₀:ℂ) := by
  apply holomorphic_identity_of_closed_physical Ω hconn hcover _ _ (complexNormalized_analyticOnNhd Ω P R hK g d) analyticOnNhd_const
  intro Y hY
  rw [complexNormalized_restrict_closed P R hKr g d Y hY,
    normalized_top P g d Y hY hd,normalized_top P g d y₀ ⟨y₀_pos.le,le_rfl⟩ hd]

lemma complexNormalized_one_zero (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n) :
    ∀ z∈Ω,complexNormalized P R 1 [0] z=complexThetaCoeff R 1 z/8 := by
  have hθ := complexThetaCoeff_analyticOnNhd Ω R hK 1
  apply holomorphic_identity_of_closed_physical Ω hconn hcover _ _ (complexNormalized_analyticOnNhd Ω P R hK 1 [0])
    (fun z hz => (hθ z hz).div_const)
  intro Y hY
  rw [complexNormalized_restrict_closed P R hKr 1 [0] Y hY,
    (initial_amplitudes P Y hY).2.2,complexThetaCoeff_restrict_closed R hKr 1 Y hY,Complex.ofReal_div]
  norm_num
end WP.Analysis
namespace WP.Analysis
lemma complexPiSigned_unstable (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℤ)
    (hs : ¬Stable g d.length) (z : ℂ) : complexPiSigned P R g d z=0 := by
  unfold complexPiSigned
  split_ifs
  · exact complexNormalized_unstable P R g (d.map Int.toNat) (by simpa only [List.length_map] using hs) z
  · rfl

lemma complexNormalized_dilaton (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (hH : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω)
    (hHr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n)
    (g p : ℕ) (hs : Stable g p) :
    ∀ z∈Ω,(complexity g p:ℂ)*complexNormalized P R g (List.replicate p 0) z=
      ∑ d∈Finset.range (dimension g (p+1)+1),complexDilatonCoefficient R d z*
        complexNormalized P R g (d::List.replicate p 0) z := by
  apply holomorphic_identity_of_closed_physical Ω hconn hcover _ _
    (fun z hz => analyticAt_const.mul (complexNormalized_analyticOnNhd Ω P R hK g _ z hz)) _ _
  · intro z hz
    apply Finset.analyticAt_fun_sum
    intro d hd
    exact (complexDilatonCoefficient_analyticOnNhd Ω R hH d z hz).mul
      (complexNormalized_analyticOnNhd Ω P R hK g _ z hz)
  · intro Y hY
    dsimp only [Pi.mul_apply]
    rw [complexNormalized_restrict_closed P R hKr g _ Y hY]
    have he := congrArg Complex.ofReal (canonical_shifted_dilaton_closed P g p hs Y hY)
    push_cast at he
    rw [he]
    apply Finset.sum_congr rfl
    intro d hd
    rw [complexDilatonCoefficient_restrict_closed R hHr d Y hY,
      complexNormalized_restrict_closed P R hKr g _ Y hY]
end WP.Analysis
