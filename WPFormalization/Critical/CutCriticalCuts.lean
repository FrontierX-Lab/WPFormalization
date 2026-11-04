import WPFormalization.Critical.CutPartitionOrbitSummation
import WPFormalization.Critical.CutPartitionGamma
import WPFormalization.Critical.CutMarkedPartitionGamma

noncomputable section
set_option maxHeartbeats 0
universe uu vv ww zz
namespace WP.Critical
open WP.External Finset MeasureTheory
open scoped Classical ENNReal
namespace CutGraphOrbits

/-- The actual chosen graph marking has precisely the prescribed unstable
vertices; the other vertices have positive base complexity before cusp allocation. -/
def PartitionAdmissible {g n k Q u v w : ℕ} (S : CutSkeleton k Q)
    (R : CutVertexPartition Q u v w) (a : BoundedAllocation g n Q) : Prop :=
  (∀ i, (a.1 (R.oneVertex i)).val = 0) ∧
  (∀ i, (a.1 (R.twoVertex i)).val = 0) ∧
  (∀ i, Stable (a.1 (R.stableVertex i)).val (S.degree (R.stableVertex i)))

/-- All admissible genera and individually named original cusps, without any
user-supplied asymptotic premise. Constants are uniform in graph markings. -/
lemma canonical_partition_gamma_rate (k Q u v w : ℕ) (hk : 1 ≤ k) (hw : 1 ≤ w)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      (n : ℝ) ≤ A * Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ R : CutVertexPartition Q u v w,
      (∀ i, S.degree (R.oneVertex i) = 1) →
      (∀ i, S.degree (R.twoVertex i) = 2) →
      (∑ a ∈ (canonicalAllocations S g n).filter (PartitionAdmissible S R),
          allocationGamma S a) / Real.Gamma (complexity g n) ≤
        C * (g : ℝ) ^ (1 - (w : ℝ) - (v : ℝ) / 2) := by

  obtain ⟨C, hC, G₁, hrate⟩ := cutCuspAllocationSum_genus_rate u v w hw A hA
  refine ⟨C,hC,max G₁ (w+2),?_⟩
  intro g hg n hn S hS R h01 h02
  let s := (canonicalAllocations S g n).filter (PartitionAdmissible S R)
  have ha01 : ∀ a ∈ s, ∀ i, (a.1 (R.oneVertex i)).val=0 :=
    fun a ha => (mem_filter.mp ha).2.1
  have ha02 : ∀ a ∈ s, ∀ i, (a.1 (R.twoVertex i)).val=0 :=
    fun a ha => (mem_filter.mp ha).2.2.1
  have hstable : ∀ a ∈ s, ∀ i, Stable (a.1 (R.stableVertex i)).val
      (S.degree (R.stableVertex i)) := fun a ha => (mem_filter.mp ha).2.2.2
  have hs := canonical_stableGenera_spec S R (PartitionAdmissible S R) ha01 ha02 hstable
  have hmajor := (sum_allocationGamma_le_all_cusps S R s ha01 ha02).trans
    (R.gamma_sum_coefficient_majorant g k n (by omega) S.degree (S.degree_pos hk hS)
      S.sum_degree h01 h02 (s.image (stableGenera R)) hs)
  have hΓ : 0 < Real.Gamma (complexity g n) := by

    apply Real.Gamma_pos_of_pos
    exact_mod_cast (by unfold complexity; omega : 0 < complexity g n)
  exact (div_le_div_of_nonneg_right hmajor hΓ.le).trans
    (by convert hrate g (by omega) n hn using 1 <;> unfold complexity <;> ring)

lemma canonical_marked_partition_gamma_rate (k Q u v w : ℕ) (hk : 1 ≤ k) (hw : 1 ≤ w)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      (n : ℝ) ≤ A * Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ R : CutVertexPartition Q u v w,
      (∀ i, S.degree (R.oneVertex i) = 1) →
      (∀ i, S.degree (R.twoVertex i) = 2) → ∀ i₀ : Fin u,
      (∑ a ∈ (canonicalAllocations S g n).filter (fun a =>
          PartitionAdmissible S R a ∧ 3 ≤ cutCuspHistogram a.2 (R.oneVertex i₀)),
          allocationGamma S a) / Real.Gamma (complexity g n) ≤
        C * (g : ℝ) ^ (1 - (w : ℝ) - ((v : ℝ)+1) / 2) := by

  by_cases hu : 1 ≤ u
  · obtain ⟨C,hC,G₁,hrate⟩ := cutMarkedCuspAllocationSum_genus_rate u v w hu hw A hA
    refine ⟨C,hC,max G₁ (w+2),?_⟩
    intro g hg n hn S hS R h01 h02 i₀
    let B : BoundedAllocation g n Q → Prop := fun a =>
      PartitionAdmissible S R a ∧ 3 ≤ cutCuspHistogram a.2 (R.oneVertex i₀)
    let s := (canonicalAllocations S g n).filter B
    have ha01 : ∀ a ∈ s, ∀ i, (a.1 (R.oneVertex i)).val=0 :=
      fun a ha => (mem_filter.mp ha).2.1.1
    have ha02 : ∀ a ∈ s, ∀ i, (a.1 (R.twoVertex i)).val=0 :=
      fun a ha => (mem_filter.mp ha).2.1.2.1
    have hstable : ∀ a ∈ s, ∀ i, Stable (a.1 (R.stableVertex i)).val
        (S.degree (R.stableVertex i)) := fun a ha => (mem_filter.mp ha).2.1.2.2
    have hs : ∀ b ∈ s.image (stableGenera R), (∀ i, Stable (b i) (S.degree (R.stableVertex i))) ∧
        (∑ c, R.genusVector b c)+k+1=g+Q := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
      refine ⟨hstable a ha,?_⟩
      rw [stableGenera_recover R a (ha01 a ha) (ha02 a ha)]
      exact ((mem_canonicalAllocations S a).mp (mem_filter.mp ha).1).1
    have hsum := sum_allocationGamma_le_stableGenera S R s ha01 ha02
      (fun _ σ => 3 ≤ cutCuspHistogram σ (R.oneVertex i₀))
      (fun a ha => (mem_filter.mp ha).2.2)
    have hsum' : (∑ a ∈ s, allocationGamma S a) ≤
        ∑ b ∈ s.image (stableGenera R), ∑ σ ∈ (univ : Finset (Fin n → Fin Q)).filter
          (fun σ => 3 ≤ cutCuspHistogram σ (R.oneVertex i₀)),
          ∏ c, Real.Gamma (complexity (R.genusVector b c)
            (S.degree c+cutCuspHistogram σ c)) := by

      simp only [sum_filter]
      convert hsum using 1
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro σ hσ
      split_ifs <;> rfl
    have hmajor := hsum'.trans
      (R.marked_gamma_sum_coefficient_majorant g k n (by omega) S.degree (S.degree_pos hk hS)
        S.sum_degree h01 h02 i₀ (s.image (stableGenera R)) hs)
    have hΓ : 0 < Real.Gamma (complexity g n) := by

      apply Real.Gamma_pos_of_pos
      exact_mod_cast (by unfold complexity; omega : 0 < complexity g n)
    exact (div_le_div_of_nonneg_right hmajor hΓ.le).trans
      (by convert hrate g (by omega) n hn using 1 <;> unfold complexity <;> ring)
  · refine ⟨1,by norm_num,0,?_⟩
    intro g hg n hn S hS R h01 h02 i₀
    have := i₀.isLt
    omega

/-- Actual expectation over every finite orbit selection in a prescribed
vertex partition. The constant is uniform over skeletons and vertex markings. -/
lemma critical_cut_partition_expectation {P : PsiTheory}
    (G : WeilPeterssonGeometry.{uu,vv} P) {H : HyperbolicCurveGeometry.{uu,vv,ww} G}
    (T : MulticurveTopology.{uu,vv,ww,zz} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hw : 1 ≤ w)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ R : CutVertexPartition Q u v w,
      (∀ i, S.degree (R.oneVertex i) = 1) →
      (∀ i, S.degree (R.twoVertex i) = 2) →
      ∀ s : Finset (Orbits T S (g:=g) (n:=n)),
      (∀ o ∈ s, PartitionAdmissible S R (boundedAllocation T S o)) →
      (∑ o ∈ s, ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2)) := by

  obtain ⟨C₁,hC₁,G₁,he⟩ := sum_orbit_expectation_gamma_envelope G T MI k Q hk hQ A L hA hL
  obtain ⟨C₂,hC₂,G₂,hr⟩ := canonical_partition_gamma_rate k Q u v w hk hw A hA
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,max G₁ G₂,?_⟩
  intro g hg n hn hcritical S hS R h01 h02 s hs
  refine (he g (by omega) n hn hcritical S s (PartitionAdmissible S R) hs).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left (hr g (by omega) n hcritical S hS R h01 h02) hC₁.le
  convert this using 1 <;> ring

lemma critical_cut_marked_partition_expectation {P : PsiTheory}
    (G : WeilPeterssonGeometry.{uu,vv} P) {H : HyperbolicCurveGeometry.{uu,vv,ww} G}
    (T : MulticurveTopology.{uu,vv,ww,zz} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hw : 1 ≤ w)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      ∀ R : CutVertexPartition Q u v w,
      (∀ i, S.degree (R.oneVertex i) = 1) →
      (∀ i, S.degree (R.twoVertex i) = 2) → ∀ i₀ : Fin u,
      ∀ s : Finset (Orbits T S (g:=g) (n:=n)),
      (∀ o ∈ s, PartitionAdmissible S R (boundedAllocation T S o) ∧
        3 ≤ cutCuspHistogram (boundedAllocation T S o).2 (R.oneVertex i₀)) →
      (∑ o ∈ s, ∫⁻ X, T.orbitSum o.val (cutLengthTest k L) X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2)) := by

  obtain ⟨C₁,hC₁,G₁,he⟩ := sum_orbit_expectation_gamma_envelope G T MI k Q hk hQ A L hA hL
  obtain ⟨C₂,hC₂,G₂,hr⟩ := canonical_marked_partition_gamma_rate k Q u v w hk hw A hA
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,max G₁ G₂,?_⟩
  intro g hg n hn hcritical S hS R h01 h02 i₀ s hs
  refine (he g (by omega) n hn hcritical S s
    (fun a => PartitionAdmissible S R a ∧ 3 ≤ cutCuspHistogram a.2 (R.oneVertex i₀)) hs).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left (hr g (by omega) n hcritical S hS R h01 h02 i₀) hC₁.le
  convert this using 1 <;> ring

end CutGraphOrbits
end WP.Critical
