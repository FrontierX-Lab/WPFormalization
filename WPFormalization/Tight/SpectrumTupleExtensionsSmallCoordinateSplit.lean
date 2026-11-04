import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments
/- Appendix F.4 local actual-spectrum proof. The original normalized WP
measure and the complete primitive tight catalogue are retained; all limits
are proved from the previously formalized geometric moment producers. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set SpectrumTupleExtensions
open scoped ENNReal NNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) {g n : ℕ}
  (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))

def smallCoordinateWindows (r : ℕ) (a B : ℝ) (i : Fin r) : Fin r→Set ℝ :=
  fun j=>if j=i then Icc (0:ℝ) a else Icc (0:ℝ) B

lemma good_set_count_le_positive_box_add_small_coordinates {r : ℕ}
    (W : Fin r→Set ℝ) (a B : ℝ) (haB : a≤B) (hW : ∀i,W i⊆Icc (0:ℝ) B) :
    Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ} ≤
      Nat.card {Γ : Fin r→Curve Q X // WindowTuple Q X (fun _=>a) (fun _=>B) Γ} +
      ∑i : Fin r,Nat.card {Γ : Fin r→Curve Q X //
        GoodSetTuple Q X (smallCoordinateWindows r a B i) Γ} := by
  let R : Option (Fin r)→(Fin (r+0)→Curve Q X)→Prop := fun i=>
    match i with
    | none=>WindowTuple Q X (fun _=>a) (fun _=>B)
    | some i=>GoodSetTuple Q X (smallCoordinateWindows r a B i)
  have hfinite : ∀i : Option (Fin r),Finite {Γ //R i Γ} := by
    intro i
    cases i with
    | none=>exact finite_window_tuples Q X (fun _=>a) (fun _=>B) B (fun _=>le_rfl)
    | some i=>
      apply good_set_tuple_finite Q X (smallCoordinateWindows r a B i) B
      intro j l hl
      by_cases hji : j=i
      · have hh : l∈Icc (0:ℝ) a := by simpa only [smallCoordinateWindows,hji,ite_true] using hl
        exact hh.2.trans haB
      · have hh : l∈Icc (0:ℝ) B := by simpa only [smallCoordinateWindows,hji,ite_false] using hl
        exact hh.2
  letI := hfinite
  have hc := card_le_sum_of_prefix_extensions r (fun _ : Option (Fin r)=>0)
    (GoodSetTuple Q X W) R (by
      intro Γ hΓ
      by_cases hall : ∀i,a≤Q.length (Γ i)
      · refine ⟨none,Γ,⟨hΓ.1,fun i=>⟨hall i,(hW i (hΓ.2 i)).2⟩⟩,?_⟩
        intro j
        rfl
      · obtain ⟨i,hi⟩:=not_forall.mp hall
        refine ⟨some i,Γ,⟨hΓ.1,?_⟩,?_⟩
        · intro j
          by_cases hji : j=i
          · subst j
            simpa only [smallCoordinateWindows,ite_true] using
              (show Q.length (Γ i)∈Icc (0:ℝ) a from ⟨(hW i (hΓ.2 i)).1,(lt_of_not_ge hi).le⟩)
          · simpa only [smallCoordinateWindows,hji,ite_false] using hW j (hΓ.2 j)
        · intro j
          rfl)
  simp only [Fintype.sum_option,R] at hc
  convert hc using 1 <;> rfl

lemma bad_good_set_count_le_positive_bad_add_small_coordinates {r : ℕ}
    (W : Fin r→Set ℝ) (a B : ℝ) (haB : a≤B) (hW : ∀i,W i⊆Icc (0:ℝ) B) (b : ℝ) :
    (if BadConfiguration Q X b then Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ} else 0) ≤
      (if BadConfiguration Q X b then
        Nat.card {Γ : Fin r→Curve Q X // WindowTuple Q X (fun _=>a) (fun _=>B) Γ} else 0) +
      ∑i : Fin r,Nat.card {Γ : Fin r→Curve Q X //
        GoodSetTuple Q X (smallCoordinateWindows r a B i) Γ} := by
  split_ifs
  · exact good_set_count_le_positive_box_add_small_coordinates Q X W a B haB hW
  · exact Nat.zero_le _

lemma small_coordinate_intensity_product {r : ℕ} (a B : ℝ) (i : Fin r) :
    (∏j : Fin r,tightIntensity (smallCoordinateWindows r a B i j)) =
      tightIntensity (Icc (0:ℝ) a)*tightIntensity (Icc (0:ℝ) B)^(r-1) := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [smallCoordinateWindows,ite_true]
  congr 1
  have he : (Finset.univ \ {i} : Finset (Fin r)).card=r-1 := by
    rw [Finset.sdiff_singleton_eq_erase,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin]
  rw [←he,←Finset.prod_const]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j≠i := by simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_singleton,true_and] using hj
  simp only [hji,ite_false]

end WP.Tight
