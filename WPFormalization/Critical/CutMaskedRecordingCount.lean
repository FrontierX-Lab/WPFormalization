import WPFormalization.Critical.CutMarkedFamilyIndex
import WPFormalization.Critical.ShortConfigurationRecordingFinite
import Mathlib.Data.Fintype.Powerset

/-! Pure finite-fiber counting for literal cut-window records with vertex masks.
The actual recording map and its ordinary finite-fiber bound are supplied by
independent geometric producers. No finiteness of the record codomain is assumed.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd ee ff
namespace WP.Critical
open WP.External Finset MeasureTheory
open scoped Classical ENNReal

/-- A finite actual set mapped into any record type, with a uniform ordinary
fiber bound, is bounded by the ENNReal cardinal sum of all literal records. -/
lemma finite_count_le_recording_tsum {α : Type ee} {ρ : Type ff}
    (s : Finset α) (record : s → ρ) (N : ℕ)
    (hfiber : ∀ R, Nat.card {a : s // record a = R} ≤ N) :
    (s.card : ℝ≥0∞) ≤ (N : ℝ≥0∞) * ∑' _ : ρ, (1 : ℝ≥0∞) := by
  let records : Finset ρ := univ.image record
  have hs : s.card ≤ records.card * N := by
    have hh := ShortConfiguration.count_le_recording_card_mul
      (univ : Finset s) records record
      (fun a _ => mem_image_of_mem record (mem_univ a)) N
      (fun R _ => by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfiber R)
    simpa only [card_univ, Fintype.card_coe] using hh
  calc
    (s.card : ℝ≥0∞) ≤ (records.card : ℝ≥0∞) * N := by exact_mod_cast hs
    _ = (N : ℝ≥0∞) * ∑ R ∈ records, (1 : ℝ≥0∞) := by
      rw [←Finset.cast_card]
      exact mul_comm _ _
    _ ≤ (N : ℝ≥0∞) * ∑' _ : ρ, (1 : ℝ≥0∞) :=
      mul_le_mul_right (ENNReal.sum_le_tsum records) _

/-- A mask on `q` vertices contributes exactly `2^q` choices, even when the
outer index type is infinite. -/
lemma masked_index_tsum_one_le {W : Type ee} (q : W → ℕ) (Q : ℕ)
    (hq : ∀ w, q w ≤ Q) :
    (∑' _ : Σ w : W, Finset (Fin (q w)), (1 : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)^Q * ∑' _ : W, (1 : ℝ≥0∞) := by
  rw [ENNReal.tsum_sigma']
  calc
    _ = ∑' w : W, (2 : ℝ≥0∞)^(q w) := by
      apply tsum_congr
      intro w
      rw [tsum_fintype]
      simp [Fintype.card_finset]
    _ ≤ ∑' _ : W, (2 : ℝ≥0∞)^Q :=
      ENNReal.tsum_le_tsum (fun w => pow_le_pow_right₀ (by norm_num) (hq w))
    _ = _ := by simpa only [mul_one] using
      (ENNReal.tsum_mul_left (a := (2 : ℝ≥0∞)^Q) (f := fun _ : W => 1))

/-- Positive cut sizes up to the fixed maximum, retaining their original size. -/
abbrev PositiveCutSize (Kmax : ℕ) := {k : Fin (Kmax+1) // 1 ≤ k.val}

lemma positiveCutSize_sum_eq (Kmax : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ k : PositiveCutSize Kmax, f k.val.val) =
      ∑ k ∈ Finset.Icc 1 Kmax, f k := by
  apply Finset.sum_bij (fun k _ => k.val.val)
  · intro k _
    have hk := k.val.isLt
    have hp := k.property
    simp only [mem_Icc]
    omega
  · intro a _ b _ hab
    apply Subtype.ext
    exact Fin.ext hab
  · intro b hb
    simp only [mem_Icc] at hb
    refine ⟨⟨⟨b, by omega⟩, hb.1⟩, mem_univ _, rfl⟩
  · intro _ _
    rfl

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) {g n : ℕ}

/-- A literal fixed-size bad/marked window together with an arbitrary mask. -/
abbrev CutMaskedWindowIndex (k : ℕ) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :=
    (Σ w : BadCutWindowIndex T (t := k) L X, Finset (Fin w.1.1.val.val)) ⊕
    (Σ w : MarkedCutWindowIndex T (t := k) L X, Finset (Fin w.1.1.val.val))

/-- Literal bad/marked cut records, retaining the full ordered window index.
All masks are allowed; their geometric interpretation belongs to the front end. -/
abbrev CutMaskedRecordingIndex (Kmax : ℕ) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :=
  Σ k : PositiveCutSize Kmax, CutMaskedWindowIndex T k.val.val L X

lemma bad_cut_masked_window_tsum_one_le (Kmax k : ℕ) (hk : k ≤ Kmax) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : Σ w : BadCutWindowIndex T (t := k) L X,
      Finset (Fin w.1.1.val.val), (1 : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)^(2*Kmax) * badCutFamilyCount T k L X := by
  have hb := masked_index_tsum_one_le
    (fun w : BadCutWindowIndex T (t := k) L X => w.1.1.val.val)
    (2*Kmax) (fun w => by have hq := w.1.1.val.isLt; omega)
  exact hb.trans_eq (congrArg (fun x : ℝ≥0∞ => (2 : ℝ≥0∞)^(2*Kmax) * x)
    (badCutWindowIndex_tsum_one_eq T L X))

lemma marked_cut_masked_window_tsum_one_le (Kmax k : ℕ) (hk : k ≤ Kmax) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : Σ w : MarkedCutWindowIndex T (t := k) L X,
      Finset (Fin w.1.1.val.val), (1 : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)^(2*Kmax) * markedCutFamilyCount T k L X := by
  have hm := masked_index_tsum_one_le
    (fun w : MarkedCutWindowIndex T (t := k) L X => w.1.1.val.val)
    (2*Kmax) (fun w => by have hq := w.1.1.val.isLt; omega)
  exact hm.trans_eq (congrArg (fun x : ℝ≥0∞ => (2 : ℝ≥0∞)^(2*Kmax) * x)
    (markedCutWindowIndex_tsum_one_eq T L X))

lemma cut_masked_window_tsum_one_le (Kmax k : ℕ) (hk : k ≤ Kmax) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : CutMaskedWindowIndex T k L X, (1 : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)^(2*Kmax) *
        (badCutFamilyCount T k L X + markedCutFamilyCount T k L X) := by
  have hs := ENNReal.summable.tsum_sum (f := fun _ : CutMaskedWindowIndex T k L X =>
    (1 : ℝ≥0∞)) ENNReal.summable
  calc
    _ = _ := hs
    _ ≤ _ := add_le_add (bad_cut_masked_window_tsum_one_le T Kmax k hk L X)
      (marked_cut_masked_window_tsum_one_le T Kmax k hk L X)
    _ = _ := (mul_add _ _ _).symm

lemma cut_masked_recording_tsum_one_le (Kmax : ℕ) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : CutMaskedRecordingIndex T Kmax L X, (1 : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞)^(2*Kmax) * ∑ k ∈ Finset.Icc 1 Kmax,
        (badCutFamilyCount T k L X + markedCutFamilyCount T k L X) := by
  rw [ENNReal.tsum_sigma', tsum_fintype]
  have hsum := Finset.sum_le_sum (s := (univ : Finset (PositiveCutSize Kmax)))
    (f := fun k => ∑' _ : CutMaskedWindowIndex T k.val.val L X, (1 : ℝ≥0∞))
    (g := fun k => (2 : ℝ≥0∞)^(2*Kmax) *
      (badCutFamilyCount T k.val.val L X + markedCutFamilyCount T k.val.val L X))
    (fun k _ => cut_masked_window_tsum_one_le T Kmax k.val.val
      (by have hk := k.val.isLt; omega) L X)
  calc
    _ ≤ _ := hsum
    _ = _ := by
      rw [←mul_sum]
      exact congrArg (fun x : ℝ≥0∞ => (2 : ℝ≥0∞)^(2*Kmax) * x)
        (positiveCutSize_sum_eq Kmax (fun k =>
          badCutFamilyCount T k L X + markedCutFamilyCount T k L X))

/-- The purely finite counting consequence of a geometric record map and an
ordinary uniform bound on each literal-record fiber. No asymptotic estimate,
record existence, or fiber bound is postulated by this module. -/
lemma cut_masked_recording_count_le {α : Type ee} (Kmax : ℕ) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (s : Finset α)
    (record : s → CutMaskedRecordingIndex T Kmax L X) (N : ℕ)
    (hfiber : ∀ R, Nat.card {a : s // record a = R} ≤ N) :
    (s.card : ℝ≥0∞) ≤ ((N * 2^(2*Kmax) : ℕ) : ℝ≥0∞) *
      ∑ k ∈ Finset.Icc 1 Kmax,
        (badCutFamilyCount T k L X + markedCutFamilyCount T k L X) := by
  calc
    _ ≤ (N : ℝ≥0∞) * ∑' _ : CutMaskedRecordingIndex T Kmax L X,
        (1 : ℝ≥0∞) := finite_count_le_recording_tsum s record N hfiber
    _ ≤ (N : ℝ≥0∞) * ((2 : ℝ≥0∞)^(2*Kmax) *
        ∑ k ∈ Finset.Icc 1 Kmax,
          (badCutFamilyCount T k L X + markedCutFamilyCount T k L X)) :=
      mul_le_mul_right (cut_masked_recording_tsum_one_le T Kmax L X) _
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

end WP.Critical
