import WPFormalization.External.ShortFullFillingGeometry
import WPFormalization.External.ShortTupleRecordingGeometry
import WPFormalization.External.ShortFundamentalGroupGeometry
import WPFormalization.External.ShortSupportingConstructionGeometry
import WPFormalization.External.ShortBorderedSingleCurveGeometry
import WPFormalization.External.ShortIntrinsicCompletionGeometry
import WPFormalization.External.ShortSupportingPieceGeometry
import WPFormalization.External.MarkedFirstPoint
import WPFormalization.External.PointMeasureMappingClassics
import WPFormalization.External.ShortIntrinsicRegionGeometry
import WPFormalization.External.ShortIntrinsicBoundaryGeometry
import WPFormalization.External.ShortCutPantsGeometry
import WPFormalization.External.PlanarRegionGeometry
import WPFormalization.External.ShortBorderedPeripheralGeometry
import WPFormalization.External.ShortSingleCurveFillingGeometry
import WPFormalization.External.FiniteCyclicIntervalGeometry
import WPFormalization.External.ShortBorderedLoopGeometry
import WPFormalization.External.ShortPeripheralAxialGeometry
import WPFormalization.External.PlanarJordanGeometry
import WPFormalization.External.PoissonLaplaceFunctional
import WPFormalization.External.ShortComplementaryRegionGeometry
import WPFormalization.External.ShortLoopStraighteningGeometry
import WPFormalization.External.PantsFamilyUniqueness
import WPFormalization.External.PointMeasureDilationTopology
import WPFormalization.External.BoundaryVolumeComparison
import WPFormalization.Statements
import WPFormalization.Statements.IntersectionInterface
import WPFormalization.External.ShortRegularNeighborhoodGeometry
import WPFormalization.External.ShortSurfaceEulerGeometry
import WPFormalization.External.ShortSingleCurveMinimalityGeometry
import WPFormalization.External.PoissonRestrictionIndependence
import WPFormalization.External.PointMeasureLaplaceConvergence
import WPFormalization.External.ShortCutPantsTypeRecognitionGeometry
import WPFormalization.External.ShortActualCutRealizationGeometry
-- Explicit hypotheses do not appear in #print axioms; inspect the structure itself.
#print WP.PsiTheory
#print axioms WP.PsiTheory
#check WP.PsiTheory.dvv
#check WP.PsiTheory.string
#check WP.PsiTheory.dilaton

-- these explicit interfaces do not appear as sorryAx dependencies.
-- Print every new classical geometric field, retaining the same G/H/T.
#print WP.External.HyperbolicCurveGeometry
#print WP.External.SpectralGeometry
#print WP.External.ShenWuPantsBound
#print WP.External.MulticurveTopology
#print WP.External.MirzakhaniIntegration
#print WP.External.CollarGeometry
#print WP.External.ProtectedCycleGeometry
#print WP.External.TightRegions
#print WP.External.BuddZonneveldTransform
#check WP.External.fixed_genus_normalized_volume_logarithm
#check WP.External.shenWu_volume_upper
#check WP.External.shenWu_volume_critical_lower

-- INT-HIGHER-KAPPA: explicit generic classical input, no concrete instance.
#print WP.External.HigherKappaRealization
#check WP.External.kappaSchurTime
#check WP.External.kappaTopIntegral
#check WP.External.HigherKappaRealization.kappa_one
#check WP.External.HigherKappaRealization.top_nonnegative
#check WP.External.HigherKappaRealization.kappa_one_top_positive
#check WP.External.HigherKappaRealization.free_energy_transform

-- classical deterministic tight geometry and exact cut integration.
-- None of these structures asserts a prescribed-cusp asymptotic or PPP limit.
#print WP.External.TightGeodesicGeometry
#print WP.External.TightMulticurveTopology
#print WP.External.BuddLionsTightIntegration
#print WP.External.BuddLionsTightGeometry
#print WP.External.MulticurveCountingMeasurability

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.QuotientSurface

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.PrimitiveAxis

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.PrimitiveGeometry

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.PackingClassics

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.BorderedGeometry

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.DoublingClassics

set_option pp.proofs false in
#print WP.External.HyperbolicPacking.AmbientRealization

set_option pp.proofs false in
#print WP.External.TightGeodesicBorelModel

set_option pp.proofs false in
#print WP.External.MulticurveRestrictionGeometry

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.SegmentClassics

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.BoundaryRealization

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.IntrinsicPiece

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.SingleCurvePieceData

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.SingleCurvePieceClassics

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.AmbientCurveCompatibility

set_option pp.proofs false in
#print WP.External.ShortFillingGeometry.CutComponentRealization

#print WP.External.wpVolume_genus_zero_boundary_upper
#print axioms WP.External.wpVolume_genus_zero_boundary_upper

-- generic topology: explicit classical data, no actual instance.
#print WP.External.ShortRegularNeighborhoodGeometry.NeighborhoodData
#print WP.External.ShortRegularNeighborhoodGeometry.RegularNeighborhoodClassics
#print WP.External.ShortSurfaceEulerGeometry.FiniteSurfaceCWModel
#print WP.External.ShortSurfaceEulerGeometry.SurfaceCellularEulerClassics
#print WP.External.pointMeasure_vague_of_semiring_count_laws
#print axioms WP.External.pointMeasure_vague_of_semiring_count_laws

-- actual pants semantics and pure point-measure topology.
#print WP.External.PantsCluster.Family
#print WP.External.PantsCluster.DeformationClassics
#print WP.External.PantsCluster.HasPantsTopology
#print WP.External.PantsCluster.PantsIsometry
#print WP.External.PantsCluster.UniquenessClassics
#print WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable
#print axioms WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable
#print WP.External.pointMeasure_nnreal_dilation_joint_continuous
#print axioms WP.External.pointMeasure_nnreal_dilation_joint_continuous

-- generic loop and annulus fields; no filled-record premise.
#print WP.External.ShortLoopStraighteningGeometry.LoopStraighteningClassics
#print WP.External.ShortLoopStraighteningGeometry.SimpleAnnulusClassics
#print WP.External.ShortLoopStraighteningGeometry.AnnulusBetween

-- generic simple-loop complementary regions, no network filling claim.
#print WP.External.ShortComplementaryRegionGeometry.DiskBoundedBy
#print WP.External.ShortComplementaryRegionGeometry.CuspEndBoundedBy
#print WP.External.ShortComplementaryRegionGeometry.SimpleComplementClassics

-- Classical PPP Laplace only, no cluster support or WP-limit premise.
#print WP.External.poisson_laplace_functional
#print axioms WP.External.poisson_laplace_functional

set_option pp.proofs false in
#print WP.External.FiniteCyclicIntervalGeometry.Classics

set_option pp.proofs false in
#print WP.External.ShortBorderedLoopGeometry.BorderedLoopStraighteningClassics

set_option pp.proofs false in
#print WP.External.ShortBorderedLoopGeometry.PrimitiveBoundaryClassics

set_option pp.proofs false in
#print WP.External.ShortPeripheralAxialGeometry.PeripheralAxialClassics

set_option pp.proofs false in
#print WP.External.PlanarJordanGeometry.PlanarJordanClassics

set_option pp.proofs false in
#print WP.External.ShortSingleCurveFillingGeometry.InteriorFilling

set_option pp.proofs false in
#print WP.External.ShortSingleCurveFillingGeometry.SingleCurveFillingClassics

set_option pp.proofs false in
#print WP.External.ShortIntrinsicRegionGeometry.IntrinsicRegionData

set_option pp.proofs false in
#print WP.External.ShortIntrinsicBoundaryGeometry.IntrinsicBoundaryData

set_option pp.proofs false in
#print WP.External.ShortCutPantsGeometry.TwoCuspCutRealization

set_option pp.proofs false in
#print WP.External.PlanarRegionGeometry.PlanarRegionClassics

set_option pp.proofs false in
#print WP.External.ShortBorderedPeripheralGeometry.BorderedPeripheralClassics

#print WP.External.CompactBorelVaguePairing

#print WP.External.AlmostSureContinuousMapping

#print WP.External.MarkedPoissonFirstPointData

#print WP.External.MarkedFirstPointConvergence

#print WP.External.ShortSupportingPieceGeometry.SupportingPieceData

#print WP.External.ShortSupportingPieceGeometry.SupportingPieceClassics

#print WP.External.ShortIntrinsicCompletionGeometry.SameImageCompletionData

#print WP.External.ShortIntrinsicCompletionGeometry.CutCompletionRealization

#print WP.External.ShortBorderedSingleCurveGeometry.SingleCurveBoundaryPieceData

#print WP.External.ShortBorderedSingleCurveGeometry.BorderedSingleCurveBoundaryClassics

#print WP.External.ShortSupportingConstructionGeometry.SupportingBoundaryRealization

#print WP.External.ShortSupportingConstructionGeometry.SupportingCarrierRealization

#print WP.External.ShortFundamentalGroupGeometry.FiniteGraphFundamentalGroupClassics

#print WP.External.ShortFundamentalGroupGeometry.SurfaceFundamentalGroupClassics

#print WP.External.ShortSingleCurveMinimalityGeometry.SingleCurveMinimalityClassics

#print WP.External.TwoColorPoissonRestrictionIndependence

#print WP.External.PointMeasureLaplaceConvergence

#print WP.External.ShortCutPantsTypeRecognitionGeometry.CutPantsTypeRecognition

#print WP.External.ShortActualCutRealizationGeometry.ActualCutRealizationData

#print WP.External.ShortActualCutRealizationGeometry.SingleCurveCutCompanionData

#print WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions
#print axioms WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions

#print WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.neighborhood
#print axioms WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.neighborhood

#print WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.surface
#print axioms WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.surface

#print WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.carrier
#print axioms WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.carrier

#print WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.boundary
#print axioms WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.boundary

#print WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics
#print axioms WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics

#print WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics.fills
#print axioms WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics.fills
