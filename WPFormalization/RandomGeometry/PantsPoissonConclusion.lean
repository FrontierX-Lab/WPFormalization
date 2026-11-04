import WPFormalization.RandomGeometry.PantsClosedCountsPoisson
import WPFormalization.RandomGeometry.PrimitiveSystolicMarkProbability
import WPFormalization.RandomGeometry.PrimitiveSystolicPlanarityProbability
import WPFormalization.RandomGeometry.PrimitiveMinimumLaw
import WPFormalization.RandomGeometry.GeneralPlanarLengthPoissonProcess

/-! The full concrete conclusion of Theorem14.1, separated from its proof.
Each process is built from the same actual unoriented primitive geodesics.
The systole is represented by the infimum of the genuine all-primitive catalog,
including nonsimple primitives, with infinity for an empty catalog. No separate
nonprimitive-cover type or machine-proved bridge from that missing type is
asserted. Concrete G/H/T/C/MI instances remain phase-two constructions.
The positive all-genus scale extension is explicitly identified eventually
with the paper's square root scale. These are conclusions, not input fields. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G)

def PantsPoissonPartOne (n : ℕ→ℕ) : Prop :=
  (∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _=>0),
    (pantsLengthPointProcess H X).toMeasure=
      Measure.sum (fun γ : {γ : H.Primitive g (n g) X //
        ∃S : Finset (Fin (n g)),H.planarSide γ=some S ∧S.card=2}=>
        Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val)))) ∧
  (∃Q : ProbabilityMeasure (PointMeasure ℝ≥0),
    IsPoissonPointProcessLaw ℝ≥0 quadraticLengthIntensity Q ∧
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g (X : G.Moduli g (n g) (fun _=>0))=>pantsLengthPointProcess H X) Q id) ∧
  (∀d : ℕ,∀lo hi : Fin d→ℝ≥0,(∀j,lo j≤hi j)→
    Pairwise (fun j k=>Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))→
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>windowCountVector ℝ≥0 (fun j=>lengthIccWindow (lo j) (hi j)) (pantsLengthPointProcess H X))
      (productPoissonMeasure (fun j=>Real.toNNReal ((hi j:ℝ)^2-(lo j:ℝ)^2))) id) ∧
  (∀t : ℝ,0≤t→Tendsto (fun g=>(wpProbability G g (n g)).real
    {X : G.Moduli g (n g) (fun _=>0)|ENNReal.ofReal t<
      ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*pantsMinimumLength H X}) atTop (𝓝 (Real.exp (-(t^2)))))

def PlanarPrimitivePoissonDensityConclusion (n : ℕ→ℕ) (l : ℝ≥0∞) : Prop :=
  (∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _=>0),
    (generalPlanarMarkedLengthPointProcess H X).toMeasure=
      Measure.sum (fun γ : {γ : H.Primitive g (n g) X //IsPlanarPrimitive H γ}=>
        Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val),planarPrimitiveCuspType H γ.val))) ∧
  (∃Q : ProbabilityMeasure (PointMeasure (ℝ≥0×ℕ)),
    IsPoissonPointProcessLaw (ℝ≥0×ℕ) (generalPlanarDensityIntensity P l) Q ∧
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarMarkedLengthPointProcess H X) Q id) ∧
  (∃Q : ProbabilityMeasure (PointMeasure ℝ≥0),
    IsPoissonPointProcessLaw ℝ≥0 (generalPlanarDensityLengthIntensity P l) Q ∧
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g (X : G.Moduli g (n g) (fun _=>0))=>generalPlanarLengthPointProcess H X) Q id) ∧
  (∀ᶠg in atTop,∀X : G.Moduli g (n g) (fun _=>0),
    (primitiveLengthPointProcess H X).toMeasure=
      Measure.sum (fun γ : {γ : H.Primitive g (n g) X //True}=>
        Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val)))) ∧
  (∃Q : ProbabilityMeasure (PointMeasure ℝ≥0),
    IsPoissonPointProcessLaw ℝ≥0 (generalPlanarDensityLengthIntensity P l) Q ∧
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g (X : G.Moduli g (n g) (fun _=>0))=>primitiveLengthPointProcess H X) Q id) ∧
  (∀t : ℝ,0≤t→Tendsto (fun g=>(wpProbability G g (n g)).real
    {X : G.Moduli g (n g) (fun _=>0)|ENNReal.ofReal t<
      ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*primitiveMinimumLength H X})
        atTop (𝓝 (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*t^2)))) ∧
  Tendsto (fun g=>(wpProbability G g (n g)).real
    {X |∀γ : H.Primitive g (n g) X,IsSystolicPrimitive H γ→IsPlanarPrimitive H γ}) atTop (𝓝 1) ∧
  (∀a b : ℝ≥0,∀j : ℕ,
    generalPlanarSystolicJointMeasure P l (Ioc (a:ℝ≥0∞) (b:ℝ≥0∞)×ˢ{j})=
      (∫⁻t in Ioc a b,ENNReal.ofReal
        (Real.exp (-generalPlanarTotalWeight P (planarDensitySaddle l)*(t:ℝ)^2)) ∂quadraticLengthIntensity)*
        ENNReal.ofReal (generalPlanarDensityTypeWeight P l j)) ∧
  generalPlanarSystolicJointMeasure P l ({∞}×ˢ(univ : Set ℕ))=0 ∧
  IsProbabilityMeasure (generalPlanarSystolicJointMeasure P l) ∧
  (∀k : (∀g,G.Moduli g (n g) (fun _=>0)→ℕ),
    (∀ᶠg in atTop,Measurable (k g))→
    (∀ᶠg in atTop,∀X,IsSystolicTypeSelection H X (k g X))→
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g X=>(ENNReal.ofReal (Real.sqrt (pantsScale g (n g)))*primitiveMinimumLength H X,k g X))
      (generalPlanarSystolicJointMeasure P l) id ∧
    ∀j : ℕ,Tendsto (fun g=>(wpProbability G g (n g)).real {X|k g X=j}) atTop
      (𝓝 (generalPlanarDensityTypeWeight P l j/generalPlanarTotalWeight P (planarDensitySaddle l))))

def PantsPoissonConclusion (n : ℕ→ℕ) : Prop :=
  PantsPoissonPartOne H n ∧∀l : ℝ≥0∞,
    Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)→
      PlanarPrimitivePoissonDensityConclusion H n l

end WP.RandomGeometry
