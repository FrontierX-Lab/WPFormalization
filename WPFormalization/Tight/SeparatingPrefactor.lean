import WPFormalization.Volumes.LeadingMarkedComparison
import WPFormalization.Marked.NormalizedModel
import WPFormalization.Analysis.KernelMomentComplexification

/-! Original F.3 prefactor bounds at every stable genus for fixed positive
protected count. The actual proved large-genus prefactor is joined to genuine
positive continuous normalized amplitudes on the finitely many small genera.
No finite-genus comparison or desired sandwich is assumed as a field. -/

noncomputable section
namespace WP.TightSeparating
open Set Filter
open scoped Topology

lemma Theta_continuous_closed : Continuous (fun Y : Icc (0 : ℝ) y₀ => Theta (Y : ℝ)) := by
  obtain ⟨Ω,hΩ,hconv,hcover,R,Q,Ah,hR,hQ,hA,hmatch,hrest⟩ :=
    Analysis.common_holomorphic_kernel_moments
  have hm : Continuous (fun Y : Icc (0 : ℝ) y₀ => ((Y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  have hcomp : Continuous (fun Y : Icc (0 : ℝ) y₀ => Q ((Y : ℝ) : ℂ)) :=
    hQ.continuousOn.comp_continuous hm (fun Y => hcover Y Y.property)
  have hcont : Continuous (fun Y : Icc (0 : ℝ) y₀ => (Q ((Y : ℝ) : ℂ)).re) :=
    Complex.continuous_re.comp hcomp
  apply hcont.congr
  intro Y
  rw [(hmatch Y Y.property).1]
  rfl

lemma normalizedMarkedModel_continuous_closed (g p : ℕ) :
    Continuous (fun Y : Icc (0 : ℝ) y₀ => normalizedMarkedModel g p (Y : ℝ)) := by
  have hA : Continuous (fun Y : Icc (0 : ℝ) y₀ => A (Y : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp Analysis.A_continuousOn_closed_parameter
  unfold normalizedMarkedModel
  exact (continuous_const.mul ((hA.inv₀ (fun Y =>
    (Analysis.marked_A_pos Y Y.property).ne')).pow _)).mul
      (((hA.mul Theta_continuous_closed).div_const _).sqrt)

lemma positive_continuous_parameter_bounds
    (f : Icc (0 : ℝ) y₀ → ℝ) (hf : Continuous f) (hp : ∀ Y, 0 < f Y) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Y, c ≤ f Y ∧ f Y ≤ C := by
  have hn : (univ : Set (Icc (0 : ℝ) y₀)).Nonempty :=
    ⟨⟨0,le_rfl,y₀_pos.le⟩,mem_univ _⟩
  obtain ⟨Y₁,hY₁,hmin⟩ := isCompact_univ.exists_isMinOn hn hf.continuousOn
  obtain ⟨Y₂,hY₂,hmax⟩ := isCompact_univ.exists_isMaxOn hn hf.continuousOn
  exact ⟨f Y₁,f Y₂,hp Y₁,hp Y₂,fun Y => ⟨hmin (mem_univ Y),hmax (mem_univ Y)⟩⟩

lemma fixed_genus_prefactor_bounds (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Y ∈ Icc (0 : ℝ) y₀,
      c ≤ Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y ∧
      Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y ≤ C := by
  let f : Icc (0 : ℝ) y₀ → ℝ := fun Y =>
    Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y
  have hcont : Continuous f := by
    exact (continuous_const.mul (normalized_continuous P g _)).div
      (normalizedMarkedModel_continuous_closed g p)
      (fun Y => (normalizedMarkedModel_pos g p hs Y Y.property).ne')
  have hpos : ∀ Y, 0 < f Y := by
    intro Y
    exact div_pos (mul_pos Real.pi_pos
      (normalized_pos_valid_nonempty P g _ (by simpa using hp) (by simpa using hs)
        (by simp) Y Y.property)) (normalizedMarkedModel_pos g p hs Y Y.property)
  obtain ⟨c,C,hc,hC,hbound⟩ := positive_continuous_parameter_bounds f hcont hpos
  exact ⟨c,C,hc,hC,fun Y hY => hbound ⟨Y,hY⟩⟩

lemma marked_model_relative_all_stable (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ g : ℕ, Stable g p → ∀ Y ∈ Ico (0 : ℝ) y₀,
      c ≤ Real.pi * markedF P g p (XR Y) / markedModel g p Y ∧
      Real.pi * markedF P g p (XR Y) / markedModel g p Y ≤ C := by
  obtain ⟨B,H,hB,hH,hBH,hlead⟩ := marked_leading_relative_error P p hp
  obtain ⟨N,hN⟩ := exists_nat_ge H
  let G := N+2
  have hfinite (i : Fin G) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, Stable i.val p →
        c ≤ Real.pi * normalized P i.val (List.replicate p 0) Y / normalizedMarkedModel i.val p Y ∧
        Real.pi * normalized P i.val (List.replicate p 0) Y / normalizedMarkedModel i.val p Y ≤ C := by
    by_cases hs : Stable i.val p
    · obtain ⟨c,C,hc,hC,hbound⟩ := fixed_genus_prefactor_bounds P i.val p hp hs
      exact ⟨c,C,hc,hC,fun Y hY _ => hbound Y hY⟩
    · exact ⟨1,1,by norm_num,by norm_num,fun Y hY hh => (hs hh).elim⟩
  choose c C hc hC hfinite using hfinite
  let D : ℝ := 2 + ∑ i : Fin G, (c i)⁻¹
  let E : ℝ := 2 + ∑ i : Fin G, C i
  have hD2 : 2 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hc i)).le))
  have hE2 : 2 ≤ E := by
    dsimp [E]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hC i).le))
  have hD : 0 < D := by linarith
  have hE : 0 < E := by linarith
  refine ⟨D⁻¹,E,inv_pos.mpr hD,hE,?_⟩
  intro g hs Y hY
  have he : Real.pi * markedF P g p (XR Y) / markedModel g p Y =
      Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y := by
    simpa only [←mul_div_assoc] using congrArg (fun x : ℝ => Real.pi*x)
      (markedF_div_model_eq_normalized P g p hs Y hY)
  by_cases hg : G ≤ g
  · have hgh : g ≤ complexity g p := by unfold complexity; dsimp [G] at hg;omega
    have hlarge : H ≤ (complexity g p : ℝ) := hN.trans
      (by exact_mod_cast (show N ≤ complexity g p by dsimp [G] at hg;omega))
    have hx : XR Y ∈ Ico (0 : ℝ) xCritical :=
      ⟨XR_nonneg_interior Y hY,XR_strictMonoOn hY.2.le (by simp) hY.2⟩
    have hh : 0 < (complexity g p : ℝ) := hH.trans_le hlarge
    have hsmall : B/(complexity g p : ℝ) ≤ 1/2 :=
      (div_le_iff₀ hh).mpr (by linarith)
    have hb := hlead g hlarge (XR Y) hx
    unfold markedLeadingError at hb
    rw [Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl] at hb
    have hhalf := abs_le.mp (hb.trans hsmall)
    have hDin : D⁻¹ ≤ 1/2 := by
      have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hD2
      norm_num at hi
      exact hi
    constructor <;> linarith
  · let i : Fin G := ⟨g,by omega⟩
    have hb := hfinite i Y ⟨hY.1,hY.2.le⟩ hs
    change c i ≤ Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y ∧
      Real.pi * normalized P g (List.replicate p 0) Y / normalizedMarkedModel g p Y ≤ C i at hb
    have hci : (c i)⁻¹ ≤ D := by
      have hh := Finset.single_le_sum (fun j _ => (inv_pos.mpr (hc j)).le) (Finset.mem_univ i)
      dsimp [D]
      linarith
    have hci' : D⁻¹ ≤ c i := by
      have hh := inv_anti₀ (inv_pos.mpr (hc i)) hci
      simpa only [inv_inv] using hh
    have hCi : C i ≤ E := by
      have hh := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
      dsimp [E]
      linarith
    rw [he]
    exact ⟨hci'.trans hb.1,hb.2.trans hCi⟩

lemma marked_model_sandwich_all_stable (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ g : ℕ, Stable g p → ∀ Y ∈ Ico (0 : ℝ) y₀,
      c * markedModel g p Y ≤ markedF P g p (XR Y) ∧
      markedF P g p (XR Y) ≤ C * markedModel g p Y := by
  obtain ⟨c,C,hc,hC,hbound⟩ := marked_model_relative_all_stable P p hp
  refine ⟨c/Real.pi,C/Real.pi,div_pos hc Real.pi_pos,div_pos hC Real.pi_pos,?_⟩
  intro g hs Y hY
  have hm := markedModel_pos_parameter g p hs Y hY
  have hb := hbound g hs Y hY
  have hlo := (le_div_iff₀ hm).mp hb.1
  have hhi := (div_le_iff₀ hm).mp hb.2
  constructor
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)
  · rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ Real.pi_pos).mpr (by nlinarith)

end WP.TightSeparating
