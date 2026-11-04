import WPFormalization.Critical.CutVertexPartition

/-! A specified one-boundary sphere receiving at least three original cusp labels. Its exact local series, partition product, and complete Gamma-allocation sum give the extra inverse square-root genus factor from Lemma G.1. -/
noncomputable section
namespace WP.Critical
open Finset

lemma cutPhi01Three_coeff_gamma_indicator (q:ℕ) :
    (q.factorial:ℝ)*PowerSeries.coeff q cutPhi01Three=
      if 3 ≤ q then Real.Gamma (complexity 0 (1+q)) else 0 := by
  by_cases hq:3 ≤ q
  · rw [if_pos hq]
    have he : PowerSeries.coeff q cutPhi01Three=PowerSeries.coeff q (cutLocalCuspSeries 0 1) := by
      simp [cutPhi01Three,cutLocalCuspSeries,cutPhi01,PowerSeries.coeff_mk,hq,show 2 ≤ q by omega]
    rw [he]
    exact cutLocalCuspSeries_coeff_gamma 0 1 q (by omega)
  · simp [cutPhi01Three,PowerSeries.coeff_mk,hq]

/-- A single distinguished one-boundary sphere is required to receive at
least three of the original cusp labels. -/
def cutMarkedLocalSeries {Q:ℕ} (a p:Fin Q→ℕ) (c₀ c:Fin Q) : PowerSeries ℝ :=
  if c=c₀ then cutPhi01Three else cutLocalCuspSeries (a c) (p c)

lemma cutCuspLabels_marked_gamma_series (n Q:ℕ) (a p:Fin Q→ℕ) (c₀:Fin Q)
    (hp:∀i,1 ≤ p i) (ha₀:a c₀=0) (hp₀:p c₀=1) :
    (∑σ∈(univ:Finset (Fin n→Fin Q)).filter (fun σ=>3 ≤ cutCuspHistogram σ c₀),
      ∏c:Fin Q,Real.Gamma (complexity (a c) (p c+cutCuspHistogram σ c))) =
        (n.factorial:ℝ)*PowerSeries.coeff n (∏c:Fin Q,cutMarkedLocalSeries a p c₀ c) := by
  classical
  rw [←cutCuspLabels_series_coeff]
  rw [sum_filter]
  apply sum_congr rfl
  intro σ hσ
  by_cases hq:3 ≤ cutCuspHistogram σ c₀
  · rw [if_pos hq]
    apply prod_congr rfl
    intro c hc
    unfold cutMarkedLocalSeries
    by_cases hcc:c=c₀
    · subst c
      rw [if_pos rfl,cutPhi01Three_coeff_gamma_indicator,if_pos hq,ha₀,hp₀]
    · rw [if_neg hcc]
      exact (cutLocalCuspSeries_coeff_gamma _ _ _ (hp c)).symm
  · rw [if_neg hq]
    symm
    apply prod_eq_zero (mem_univ c₀)
    simp only [cutMarkedLocalSeries,ite_true]
    rw [cutPhi01Three_coeff_gamma_indicator,if_neg hq]

end WP.Critical
namespace WP.Critical
namespace CutVertexPartition
open Finset
variable {Q u v w:ℕ} (R:CutVertexPartition Q u v w)

lemma marked_localSeries_product (p:Fin Q→ℕ) (b:Fin w→ℕ) (i₀:Fin u)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2)
    (hb:∀i,Stable (b i) (p (R.stableVertex i))) :
    (∏c:Fin Q,cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) c)=
      cutMarkedCuspAllocationSeries u v*
        (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i)))) := by
  classical
  have hone (i:Fin u) : R.oneVertex i=R.oneVertex i₀ ↔ i=i₀ := by
    unfold oneVertex
    rw [R.vertices.symm.injective.eq_iff,Sum.inl.injEq]
  have h1 (i:Fin u) : cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.oneVertex i)=
      if i=i₀ then cutPhi01Three else cutPhi01 := by
    unfold cutMarkedLocalSeries
    simp only [hone]
    have ha:R.genusVector b (R.oneVertex i)=0 := by simp [genusVector,oneVertex]
    rw [ha,h01 i]
    simp [cutLocalCuspSeries]
  have h2 (i:Fin v) : cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.twoVertex i)=cutPhi02 := by
    have hne:R.twoVertex i≠R.oneVertex i₀ := by
      intro he
      have hc:=congrArg R.vertices he
      simp [twoVertex,oneVertex] at hc
    rw [cutMarkedLocalSeries,if_neg hne]
    have ha:R.genusVector b (R.twoVertex i)=0 := by simp [genusVector,twoVertex]
    rw [ha,h02 i]
    norm_num [cutLocalCuspSeries]
  have h3 (i:Fin w) : cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.stableVertex i)=
      cutStableCuspSeries (complexity (b i) (p (R.stableVertex i))) := by
    have hne:R.stableVertex i≠R.oneVertex i₀ := by
      intro he
      have hc:=congrArg R.vertices he
      simp [stableVertex,oneVertex] at hc
    rw [cutMarkedLocalSeries,if_neg hne]
    have ha:R.genusVector b (R.stableVertex i)=b i := by simp [genusVector,stableVertex]
    rw [ha]
    exact cutLocalCuspSeries_eq_stable _ _ (hb i)
  have he : (∏c:Fin Q,cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) c)=
      ∏j:Fin u⊕(Fin v⊕Fin w),
        cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.vertices.symm j) :=
    (Equiv.prod_comp R.vertices.symm _).symm
  rw [he,Fintype.prod_sum_type,Fintype.prod_sum_type]
  change (∏i:Fin u,cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.oneVertex i))*
    ((∏i:Fin v,cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.twoVertex i))*
      (∏i:Fin w,cutMarkedLocalSeries (R.genusVector b) p (R.oneVertex i₀) (R.stableVertex i)))=_
  simp_rw [h1,h2,h3]
  have hconst : (∏i:Fin u,if i=i₀ then cutPhi01Three else cutPhi01)=
      cutPhi01Three*cutPhi01^(u-1) := by
    rw [←mul_prod_erase univ (fun i:Fin u=>if i=i₀ then cutPhi01Three else cutPhi01) (mem_univ i₀)]
    simp only [ite_true]
    congr 1
    calc
      _ = ∏_i∈univ.erase i₀,cutPhi01 := by
        apply prod_congr rfl
        intro i hi
        rw [if_neg (mem_erase.mp hi).1]
      _ = _ := by simp
  rw [hconst]
  simp only [prod_const,card_univ,Fintype.card_fin]
  unfold cutMarkedCuspAllocationSeries
  ring

end CutVertexPartition
end WP.Critical
namespace WP.Critical
namespace CutVertexPartition
open Finset
variable {Q u v w:ℕ} (R:CutVertexPartition Q u v w)

lemma marked_gamma_sum_coefficient_majorant (g k n:ℕ) (hg:w+2≤g)
    (p:Fin Q→ℕ) (hp:∀i,1≤p i) (hpsum:(∑c:Fin Q,p c)=2*k)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2) (i₀:Fin u)
    (s:Finset (Fin w→ℕ))
    (hs:∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
      (∑c:Fin Q,R.genusVector b c)+k+1=g+Q) :
    (∑b∈s,∑σ∈(univ:Finset (Fin n→Fin Q)).filter
        (fun σ=>3≤cutCuspHistogram σ (R.oneVertex i₀)),
      ∏c:Fin Q,Real.Gamma (complexity (R.genusVector b c) (p c+cutCuspHistogram σ c))) ≤
        (n.factorial:ℝ)*PowerSeries.coeff n (cutMarkedCuspAllocationSeries u v*
          cutStableAllocationSeries w (2*g-2+u-w)) := by
  have hstable : ∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
      (∑i:Fin w,complexity (b i) (p (R.stableVertex i)))=(2*g-2+u-w)+w := by
    intro b hb
    exact ⟨(hs b hb).1,R.stableComplexity_budget g k hg p b h01 h02 (hs b hb).1 hpsum (hs b hb).2⟩
  calc
    _ = ∑b∈s,(n.factorial:ℝ)*PowerSeries.coeff n
        (cutMarkedCuspAllocationSeries u v*
          (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i))))) := by
      apply sum_congr rfl
      intro b hb
      have ha₀ : R.genusVector b (R.oneVertex i₀)=0 := by simp [genusVector,oneVertex]
      rw [cutCuspLabels_marked_gamma_series n Q (R.genusVector b) p (R.oneVertex i₀)
        hp ha₀ (h01 i₀),R.marked_localSeries_product p b i₀ h01 h02 (hs b hb).1]
    _ = (n.factorial:ℝ)*(∑b∈s,PowerSeries.coeff n
        (cutMarkedCuspAllocationSeries u v*
          (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i)))))) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cutStableGenus_coefficient_majorant n (fun i=>p (R.stableVertex i)) s hstable
        (cutMarkedCuspAllocationSeries u v) (cutMarkedCuspAllocation_coeff_nonneg u v)) (Nat.cast_nonneg _)

lemma marked_gamma_sum_genus_rate (k:ℕ) (p:Fin Q→ℕ) (hp:∀i,1≤p i)
    (hpsum:(∑c:Fin Q,p c)=2*k)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2) (i₀:Fin u)
    (hw:1≤w) (A:ℝ) (hA:0<A) :
    ∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ)≤A*Real.sqrt g →
      ∀s:Finset (Fin w→ℕ),
      (∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
        (∑c:Fin Q,R.genusVector b c)+k+1=g+Q) →
      ((∑b∈s,∑σ∈(univ:Finset (Fin n→Fin Q)).filter
          (fun σ=>3≤cutCuspHistogram σ (R.oneVertex i₀)),
        ∏c:Fin Q,Real.Gamma (complexity (R.genusVector b c) (p c+cutCuspHistogram σ c)))/
          Real.Gamma ((2*g+n-2:ℕ):ℝ)) ≤ C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2) := by
  have hu:1≤u := by have:=i₀.isLt;omega
  obtain ⟨C,hC,G,hbound⟩:=cutMarkedCuspAllocationSum_genus_rate u v w hu hw A hA
  refine ⟨C,hC,max G (w+2),?_⟩
  intro g hg n hn s hs
  have hpΓ : 0<Real.Gamma (((2*g+n-2:ℕ):ℝ)) := by
    apply Real.Gamma_pos_of_pos
    exact_mod_cast (by omega:0<2*g+n-2)
  have he:=R.marked_gamma_sum_coefficient_majorant g k n (by omega) p hp hpsum h01 h02 i₀ s hs
  have hb:=div_le_div_of_nonneg_right he hpΓ.le
  have hm:=hbound g (by omega) n hn
  exact hb.trans (by convert hm using 1 <;>ring)

end CutVertexPartition
end WP.Critical
