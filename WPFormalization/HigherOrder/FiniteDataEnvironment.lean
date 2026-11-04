import WPFormalization.HigherOrder.BoundaryCoarsening
import WPFormalization.HigherOrder.FiniteThetaInverse
import WPFormalization.HigherOrder.FirstScalarCoefficients
import WPFormalization.Analysis.PolynomialMomentReduction
import WPFormalization.HigherOrder.BMoments
/-! The actual finite kernel-data ring at final order J uses the literal index set Index J bJ. Its evaluation supplies actual area, inverse area, bounded moments and low coefficients, with every theta prefix at K≤J. The genuine moment HasSum theorems instantiate the primitive data; no recursive profile or scalar conclusion is included in the environment. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
inductive Index (J N:ℕ) where
  | area
  | inverseArea
  | weightMoment (k:Fin (2*J+1))
  | dilatonMoment (k:Fin (2*J+1))
  | weightCoefficient (l:Fin (N+1))
  | dilatonCoefficient (l:Fin (N+1))
  | thetaCoefficient (l:Fin ((3*J)/2+2))
  deriving DecidableEq, Fintype

/-- Only genuine functions from the current canonical definitions. -/
def value (J N:ℕ)(Y:ℝ):Index J N→ℝ
  | .area=>A Y
  | .inverseArea=>(A Y)⁻¹
  | .weightMoment k=>kernelMoment k.val Y
  | .dilatonMoment k=>bMoment k.val Y
  | .weightCoefficient l=>weight Y l.val
  | .dilatonCoefficient l=>bCoeff Y l.val
  | .thetaCoefficient l=>theta Y l.val


abbrev DataPolynomial (J : ℕ) := MvPolynomial (Index J (boundaryCutoff J)) ℝ

def dataEval (J : ℕ) (Y : ℝ) : DataPolynomial J →ₐ[ℝ] ℝ :=
  MvPolynomial.aeval (value J (boundaryCutoff J) Y)

@[simp] lemma dataEval_X (J : ℕ) (Y : ℝ) (i : Index J (boundaryCutoff J)) :
    dataEval J Y (MvPolynomial.X i) = value J (boundaryCutoff J) Y i := by
  simp [dataEval]

@[simp] lemma dataEval_C (J : ℕ) (Y x : ℝ) :
    dataEval J Y (MvPolynomial.C x) = x := by simp [dataEval]

lemma dataEval_toRingHom (J : ℕ) (Y : ℝ) :
    (dataEval J Y).toRingHom = MvPolynomial.eval (value J (boundaryCutoff J) Y) := rfl

def dataArea (J : ℕ) : DataPolynomial J := MvPolynomial.X .area
def dataInverseArea (J : ℕ) : DataPolynomial J := MvPolynomial.X .inverseArea

def dataWeightMoment (J k : ℕ) : DataPolynomial J :=
  if hk : k ≤ 2 * J then MvPolynomial.X (.weightMoment ⟨k, by omega⟩) else 0

def dataDilatonMoment (J k : ℕ) : DataPolynomial J :=
  if hk : k ≤ 2 * J then MvPolynomial.X (.dilatonMoment ⟨k, by omega⟩) else 0

def dataWeightCoefficient (J l : ℕ) : DataPolynomial J :=
  if hl : l ≤ boundaryCutoff J then MvPolynomial.X (.weightCoefficient ⟨l, by omega⟩) else 0

def dataDilatonCoefficient (J l : ℕ) : DataPolynomial J :=
  if hl : l ≤ boundaryCutoff J then MvPolynomial.X (.dilatonCoefficient ⟨l, by omega⟩) else 0

lemma dataArea_eval (J : ℕ) (Y : ℝ) : dataEval J Y (dataArea J) = WP.A Y := by
  simp [dataArea, value]
lemma dataInverseArea_eval (J : ℕ) (Y : ℝ) : dataEval J Y (dataInverseArea J) = (WP.A Y)⁻¹ := by
  simp [dataInverseArea, value]
lemma dataWeightMoment_eval (J k : ℕ) (hk : k ≤ 2 * J) (Y : ℝ) :
    dataEval J Y (dataWeightMoment J k) = kernelMoment k Y := by
  simp only [dataWeightMoment, dite_eq_left hk, dataEval_X, value]
lemma dataDilatonMoment_eval (J k : ℕ) (hk : k ≤ 2 * J) (Y : ℝ) :
    dataEval J Y (dataDilatonMoment J k) = bMoment k Y := by
  simp only [dataDilatonMoment, dite_eq_left hk, dataEval_X, value]
lemma dataWeightCoefficient_eval (J l : ℕ) (hl : l ≤ boundaryCutoff J) (Y : ℝ) :
    dataEval J Y (dataWeightCoefficient J l) = weight Y l := by
  simp only [dataWeightCoefficient, dite_eq_left hl, dataEval_X, value]
lemma dataDilatonCoefficient_eval (J l : ℕ) (hl : l ≤ boundaryCutoff J) (Y : ℝ) :
    dataEval J Y (dataDilatonCoefficient J l) = canonicalDilatonCoefficient Y l := by
  simp only [dataDilatonCoefficient, dite_eq_left hl, dataEval_X, value, bCoeff_eq_canonicalDilatonCoefficient]

lemma dataWeightMoment_hasSum (J k : ℕ) (hk : k ≤ 2 * J) (Y : ℝ) (hY : Y ∈ Set.Icc (0 : ℝ) y₀) :
    HasSum (fun l : ℕ => (l : ℝ) ^ k * weight Y l) (dataEval J Y (dataWeightMoment J k)) := by
  rw [dataWeightMoment_eval J k hk Y]
  exact WP.Analysis.kernel_moment_hasSum_absolute k Y hY
lemma dataDilatonMoment_hasSum (J k : ℕ) (hk : k ≤ 2 * J) (Y : ℝ) :
    HasSum (fun l : ℕ => (l : ℝ) ^ k * canonicalDilatonCoefficient Y l)
      (dataEval J Y (dataDilatonMoment J k)) := by
  rw [dataDilatonMoment_eval J k hk Y]
  exact bMoment_hasSum k Y

def thetaDataMap (J K : ℕ) (hK : K ≤ J) : ThetaPolynomial ((3 * K) / 2 + 1) →+* DataPolynomial J :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin ((3 * K) / 2 + 2) =>
      MvPolynomial.X (.thetaCoefficient ⟨i.val, by have := i.isLt; omega⟩))

lemma thetaDataMap_eval (J K : ℕ) (hK : K ≤ J) (Y : ℝ) :
    (dataEval J Y).toRingHom.comp (thetaDataMap J K hK) =
      MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [thetaDataMap, dataEval, value]
  · intro i
    simp [thetaDataMap, dataEval, value]
end WP.HigherOrder.KernelFiniteData
