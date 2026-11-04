import WPFormalization.RandomGeometry.GeneralPlanarMixedFactorialCount
import WPFormalization.RandomGeometry.PantsRationalWindows

/-! Exact bounded-window counts of each actual planar cusp type. This layer
contains no geometric integration or probabilistic limit. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set Filter
open scoped Topology ENNReal NNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma generalPlanarLengthPointMeasure_Ioc_eq_windowCount (X : G.Moduli g n (fun _=>0))
    (s : ℝ) (hs : 0<s) (k : ℕ) (L : ℝ) (a b : ℝ≥0) (hcut : (b:ℝ)/s≤L) :
    (planarLengthPointMeasure H X s hs k).toMeasure (Ioc a b)=
      (generalPlanarWindowCount H X (fun _ : Fin 1=>k) L
        (fun _=>Ioc ((a:ℝ)/s) ((b:ℝ)/s)):ℝ≥0∞) := by
  let p := fun γ : H.Primitive g n X=>∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=k
  letI := curveNNLengthMeasure_finite_window H X s hs p (Ioc a b) ⟨b,fun _ hx=>hx.2⟩
  change curveNNLengthMeasure H X s p (Ioc a b)=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ measurableSet_Ioc]
  rw [←generalPlanarWindowCatalog_card H X k L (Ioc ((a:ℝ)/s) ((b:ℝ)/s))]
  have hc : Nat.card {γ //γ∈generalPlanarWindowCatalog H X k L (Ioc ((a:ℝ)/s) ((b:ℝ)/s))}=
      (generalPlanarWindowCatalog H X k L (Ioc ((a:ℝ)/s) ((b:ℝ)/s))).card := by
    simp [Nat.card_eq_fintype_card]
  rw [←hc]
  have hcat (γ : H.Primitive g n X) :
      γ∈generalPlanarWindowCatalog H X k L (Ioc ((a:ℝ)/s) ((b:ℝ)/s)) ↔
      γ∈H.shortPlanar X k L ∧ H.length γ∈Ioc ((a:ℝ)/s) ((b:ℝ)/s) := by
    simp [generalPlanarWindowCatalog]
  congr 1
  apply Nat.card_congr
  exact {
    toFun:=fun γ=>⟨γ.val.val,(hcat _).mpr ⟨(H.mem_shortPlanar X k L _).mpr
      ⟨((scaled_length_mem_Ioc s hs a b _).mp γ.property).2.trans hcut,γ.val.property⟩,
        (scaled_length_mem_Ioc s hs a b _).mp γ.property⟩⟩
    invFun:=fun γ=>⟨⟨γ.val,(H.mem_shortPlanar X k L γ.val).mp ((hcat _).mp γ.property).1 |>.2⟩,
      (scaled_length_mem_Ioc s hs a b _).mpr ((hcat _).mp γ.property).2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma generalPlanarLengthPointMeasure_Ioc_count_eq_windowCount (X : G.Moduli g n (fun _=>0))
    (s : ℝ) (hs : 0<s) (k : ℕ) (L : ℝ) (a b : ℝ≥0) (hcut : (b:ℝ)/s≤L) :
    (planarLengthPointMeasure H X s hs k).count ℝ≥0 (lengthIocWindow a b)=
      generalPlanarWindowCount H X (fun _ : Fin 1=>k) L (fun _=>Ioc ((a:ℝ)/s) ((b:ℝ)/s)) := by
  apply Nat.cast_injective (R:=ℝ≥0∞)
  exact ((planarLengthPointMeasure H X s hs k).count_spec ℝ≥0 _).symm.trans
    (generalPlanarLengthPointMeasure_Ioc_eq_windowCount H X s hs k L a b hcut)

lemma generalPlanarLengthPointMeasure_prefix_count_measurable (s : ℝ) (hs : 0<s) (k : ℕ) (b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (planarLengthPointMeasure H X s hs k).count ℝ≥0 (nnrealPrefixWindow b)) := by
  simp_rw [planarLengthPointMeasure_prefix_count]
  exact H.measurable_planarCount g n k _

lemma generalPlanarLengthPointMeasure_Ioc_count_measurable (s : ℝ) (hs : 0<s) (k : ℕ) (a b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (planarLengthPointMeasure H X s hs k).count ℝ≥0 (lengthIocWindow a b)) := by
  change Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (planarLengthPointMeasure H X s hs k).count ℝ≥0 (nnrealIocWindow a b))
  simp_rw [PointMeasure.count_nnrealIoc]
  exact (generalPlanarLengthPointMeasure_prefix_count_measurable H s hs k b).sub
    (generalPlanarLengthPointMeasure_prefix_count_measurable H s hs k a)

lemma generalPlanarLengthPointMeasure_rational_count_measurable (s : ℝ) (hs : 0<s) (k : ℕ) (a b : ℚ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (planarLengthPointMeasure H X s hs k).count ℝ≥0 (nnrealRationalWindow a b)) := by
  have hz (X : G.Moduli g n (fun _=>0)) : (planarLengthPointMeasure H X s hs k).toMeasure {0}=0 :=
    curveNNLengthMeasure_singleton_zero H X s hs _
  simp_rw [pointMeasure_count_rational_window_eq_canonical_Ioc _ (hz _) a b]
  exact generalPlanarLengthPointMeasure_Ioc_count_measurable H s hs k _ _

end WP.RandomGeometry
