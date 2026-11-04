import WPFormalization.HigherOrder.BoundaryAffineStatus
/-! The paper boundary cutoffs are monotone and dominate the actual merger, handle and separating low-index cutoffs. Refining a finite boundary pattern preserves a current joint polynomial certificate and its degree. No all-order certificate is supplied here. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData

def boundaryCutoff : ℕ → ℕ
  | 0 => 0
  | K + 1 => 2 * boundaryCutoff K + 2 * (K + 1) + 4

lemma boundaryCutoff_mono : Monotone boundaryCutoff := by
  apply monotone_nat_of_le_succ
  intro k
  rw [boundaryCutoff]
  omega

lemma boundaryCutoff_merger (k : ℕ) : boundaryCutoff k + 1 ≤ boundaryCutoff (k + 1) := by
  rw [boundaryCutoff]
  omega

lemma boundaryCutoff_handle (k : ℕ) : 2 * boundaryCutoff k + 2 ≤ boundaryCutoff (k + 1) := by
  rw [boundaryCutoff]
  omega

lemma boundaryCutoff_separating (k : ℕ) :
    boundaryCutoff k + (3 * (k + 1)) / 2 + 2 ≤ boundaryCutoff (k + 1) := by
  rw [boundaryCutoff]
  omega
end WP.HigherOrder.KernelFiniteData

namespace WP.HigherOrder.JointBoundary
variable {R : Type*} [CommRing R]

def coarsenPattern {p : ℕ} (b B : ℕ) (σ : Fin p → Option (Fin (B + 1))) :
    Fin p → Option (Fin (b + 1)) := classify p b (representative p B σ)

lemma coarsenPattern_classify {p : ℕ} (b B : ℕ) (hb : b ≤ B) (d : Fin p → ℕ) :
    coarsenPattern b B (classify p B d) = classify p b d :=
  classify_representative b B hb d

def coarsenStratumPolynomial {p : ℕ} (b B : ℕ)
    (F : (Fin p → Option (Fin (b + 1))) → MvPolynomial (Fin p) R)
    (σ : Fin p → Option (Fin (B + 1))) : MvPolynomial (Fin p) R := F (coarsenPattern b B σ)

lemma coarsenStratumPolynomial_degree {p : ℕ} (b B D : ℕ)
    (F : (Fin p → Option (Fin (b + 1))) → MvPolynomial (Fin p) R)
    (hdegree : ∀ τ, (F τ).totalDegree ≤ D) (σ : Fin p → Option (Fin (B + 1))) :
    (coarsenStratumPolynomial b B F σ).totalDegree ≤ D := hdegree _

lemma coarsenStratumPolynomial_eval {p : ℕ} (b B : ℕ) (hb : b ≤ B)
    (F : (Fin p → Option (Fin (b + 1))) → MvPolynomial (Fin p) R)
    (φ : R →+* ℝ) (d : Fin p → ℕ) :
    MvPolynomial.eval₂ φ (fun i => (d i : ℝ))
        (coarsenStratumPolynomial b B F (classify p B d)) =
      MvPolynomial.eval₂ φ (fun i => (d i : ℝ)) (F (classify p b d)) := by
  rw [coarsenStratumPolynomial, coarsenPattern_classify b B hb d]
end WP.HigherOrder.JointBoundary
