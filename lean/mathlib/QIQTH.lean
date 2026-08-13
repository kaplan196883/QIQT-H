-- QIQT-H Mathlib-rooted formalizations.
-- See standalone variants in ../Theorem*.lean for axiomatized counterparts.

import QIQTH.Theorem6
import QIQTH.Theorem7
import QIQTH.Resolution
import QIQTH.UnitarityLocality
import QIQTH.Donald
import QIQTH.DoubleSlit
-- Extensions added in the GPT-5.5 audit round:
import QIQTH.StateLevelNoSignaling
import QIQTH.KrausLocality
import QIQTH.ResolutionExt
import QIQTH.CapacityPacking
import QIQTH.RelEntPositivity
import QIQTH.QuantumRelativeEntropy
import QIQTH.Entropy.TraceConvexity
import QIQTH.Entropy.OperatorConvex
import QIQTH.Entropy.CStarMatrixBridge
import QIQTH.Entropy.MatrixOperatorMonotone
import QIQTH.Entropy.GeometricMean
import QIQTH.Entropy.WeightedMean
import QIQTH.Entropy.TensorMean
import QIQTH.Entropy.TensorPower
import QIQTH.Entropy.CommuteRpow
import QIQTH.Entropy.Lieb
import QIQTH.Entropy.RpowConj
import QIQTH.Entropy.RelEntropyConvex
import QIQTH.Entropy.RelEntropyDPI
import QIQTH.Entropy.OrderLimit
import QIQTH.Entropy.PartialTrace
import QIQTH.Entropy.WeylDesign
import QIQTH.Entropy.PartialTraceDPI
import QIQTH.Entropy.TensorLog
import QIQTH.Entropy.StrongSubadditivity
import QIQTH.HolevoCoarseGraining
import QIQTH.DPI
import QIQTH.ShannonFano
import QIQTH.OperationalCapacity
import QIQTH.MaxEntropyCapacity
import QIQTH.ModularEnergyBound
import QIQTH.InducedNewtonConstant
import QIQTH.ScopeAudit
import QIQTH.HolographicScreenCode
import QIQTH.EmergentDynamics
import QIQTH.GravitonQuantization
import QIQTH.OperatorEmergence
import QIQTH.BargmannPairing
import QIQTH.ModularTransport
import QIQTH.Keystone
import QIQTH.KeystoneOperator
import QIQTH.JoinInstance
import QIQTH.Embedding
import QIQTH.Dynamics
import QIQTH.CrossCheck
import QIQTH.Conjectures
import QIQTH.Decoupling.TruncatedCCR
import QIQTH.Decoupling.GibbsSingleMode
import QIQTH.Decoupling.EntropyRegimes
import QIQTH.Decoupling.ProductModes
import QIQTH.Rigidity.LogValuationReal
import QIQTH.Rigidity.FiniteCornerValuation
import QIQTH.Decoupling.DecouplingShadow
import QIQTH.Tower.AWFingerprint
import QIQTH.Tower.KroneckerDensity
import QIQTH.Tower.Centerpiece
import QIQTH.Tower.PowersGuard
import QIQTH.Tower.GibbsLimit
import QIQTH.Tower.NonAtomic
import QIQTH.Tower.CornerEmbed
import QIQTH.Tower.Checkpoint
import QIQTH.VonNeumann.InvariantProjection
import QIQTH.VonNeumann.GeneratedBy
import QIQTH.VonNeumann.DensityOne
import QIQTH.VonNeumann.Amplification
import QIQTH.VonNeumann.MatrixCommutant
import QIQTH.VonNeumann.DensityN
import QIQTH.VonNeumann.Bicommutant
import QIQTH.VonNeumann.CrossedProductClosure
import QIQTH.VonNeumann.DirectedUnionVN
import QIQTH.VonNeumann.WOTClosure
import QIQTH.VonNeumann.Checkpoint
import QIQTH.VonNeumann.SelfAdjointCriterion
import QIQTH.VonNeumann.GraphDecomposition
import QIQTH.VonNeumann.AdjointComp
import QIQTH.TowerGNS.EmbedTrans
import QIQTH.TowerGNS.StageInner
import QIQTH.TowerGNS.PreSpace
import QIQTH.TowerGNS.Germ
import QIQTH.TowerGNS.StageBound
import QIQTH.TowerGNS.LeftMul
import QIQTH.TowerGNS.Representation
import QIQTH.TowerGNS.CyclicVector
import QIQTH.TowerGNS.LimitVN
import QIQTH.TowerGNS.Checkpoint
import QIQTH.TowerGNS.FlowPre
import QIQTH.TowerGNS.Flow
import QIQTH.TowerGNS.FlowCovariance
import QIQTH.Rigidity.RegulatorRigidity
import QIQTH.HeatKernelOneD
import QIQTH.HeatKernelA1
import QIQTH.HeatKernelDDim
import QIQTH.FlatHeatEquation
import QIQTH.GaussianPolyBound
import QIQTH.GaussianConvolution
import QIQTH.HadamardFactor
import QIQTH.MatrixJacobi
import QIQTH.JacobiFormula
import QIQTH.MatrixRaychaudhuri
import QIQTH.ParallelTransport
import QIQTH.ParallelMetricInnerAt
import QIQTH.ParallelInnerInterval
import QIQTH.FrameRicci
import QIQTH.CovariantJacobiOffCenter
import QIQTH.CovariantJacobiNhds
import QIQTH.FrameCovariantDeriv
import QIQTH.FrameCovariantDerivNhds
import QIQTH.FrameJacobiEquation
import QIQTH.FrameJacobiEquationNhds
import QIQTH.GeodesicRaychaudhuri
import QIQTH.FrameRaychaudhuri
import QIQTH.ExpFlowRaychaudhuri
import QIQTH.ExpFlowFrameH4
import QIQTH.RaychaudhuriLogDet
import QIQTH.LogDetSecondDerivTrace
import QIQTH.TraceRaychaudhuriRescale
import QIQTH.RadialRayDeriv
import QIQTH.VanVleckRaychaudhuri
import QIQTH.ParallelOrthonormal
import QIQTH.OrthonormalFrameExists
import QIQTH.OrthonormalFrameDet
import QIQTH.OrthonormalFrameComplete
import QIQTH.FrameReconstruct
import QIQTH.FrameComponentsHexp
import QIQTH.FrameComponentsDeriv
import QIQTH.CovariantDerivCurveCongr
import QIQTH.ParallelFrameExpTube
import QIQTH.VanVleckH4Assembled
import QIQTH.VanVleckRicciAssembled
import QIQTH.RadialJacobiLink
import QIQTH.TransverseVariationDischarge
import QIQTH.VanVleckRicciReduced
import QIQTH.VanVleckRicciFrameReduced
import QIQTH.VanVleckRicciFrameReduced2
import QIQTH.FrameComponentsSecondDeriv
import QIQTH.VanVleckRicciFrameReduced3
import QIQTH.VanVleckRicciUnconditional
import QIQTH.ParametrixRadialTransportSplit
import QIQTH.ParametrixDeviationCrossTerm
import QIQTH.RNCInverseMetricJet
import QIQTH.ParametrixFlatCurvatureResidue
import QIQTH.ParametrixResidualO1Total
import QIQTH.ParametrixOffDiagCancellation
import QIQTH.ParametrixHessianCancellation
import QIQTH.RadialRicciUnconditional
import QIQTH.RNCTaylorPeano
import QIQTH.ParametrixOffDiagLittleO
import QIQTH.ParametrixResidualGaussianBound
import QIQTH.ParametrixResidualN0Bound
import QIQTH.ParametrixResidualBaseKernel
import QIQTH.GaussianWidthTolerant
import QIQTH.ParametrixResidualTPower
import QIQTH.ParametrixHEboundWiring
import QIQTH.TrueKernelA1
import QIQTH.TrueKernelA1Reduced
import QIQTH.C4cDecomposition
import QIQTH.SmoothCutoff
import QIQTH.AnnulusGaussianBound
import QIQTH.LaplaceBeltramiLeibniz
import QIQTH.CutoffAnnulusSupport
import QIQTH.CutoffResidualGlobalBound
import QIQTH.CutoffAnnulusBounds
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.NearResidualBound
import QIQTH.CutoffResidualAssembled
import QIQTH.RecenterReduction
import QIQTH.ModelIntegrableW
import QIQTH.IterConvIntegrableFull
import QIQTH.IterEMeasurable
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.CutoffResidualFiniteReg
import QIQTH.RNCExpansionFiniteReg
import QIQTH.ResidualN0FiniteReg
import QIQTH.ExpMapContDiff4
import QIQTH.PullbackMetricC3
import QIQTH.OffDiagLittleOFiniteReg
import QIQTH.ResidualN0GaussianC3
import QIQTH.NearResidualC3
import QIQTH.RecenterConnectC3
import QIQTH.RecenterConnectC3b
import QIQTH.RecenterDeWittC3
import QIQTH.RecenterConnectC3c
import QIQTH.RecenterCutoffC3
import QIQTH.RecenterHEboundW
import QIQTH.RecenterA1Capstone
import QIQTH.ExpJet4Rhs
import QIQTH.LeviInterchange
import QIQTH.ExpJet4Fund
import QIQTH.ExpJet4FundGlobal
import QIQTH.ExpJet4FundBounds
import QIQTH.ExpJet4Val
import QIQTH.ExpJet4ValFull
import QIQTH.ExpJet4D
import QIQTH.ExpJet4DFull
import QIQTH.ExpJet4Residual
import QIQTH.ExpJet4Prereq
import QIQTH.ExpJet4Remainder
import QIQTH.ExpJet4RemainderP
import QIQTH.ExpJet3SecondVarResidual
import QIQTH.ExpJet4RemainderUnif
import QIQTH.ExpMapFDeriv3
import QIQTH.ExpMapContDiffFour
import QIQTH.PullbackMetricC3Uncond
import QIQTH.RecenterResidualUncond
import QIQTH.RecenterAnnulusUncond
import QIQTH.PullbackMetricNondegNearZero
import QIQTH.FlatTail
import QIQTH.AnnulusContinuityWithinRho
import QIQTH.RecenterCutoffLocal
import QIQTH.ExpMapLocalInverse
import QIQTH.GaussCompare
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.UniformExpJacobian
import QIQTH.UniformExpSecondJet
import QIQTH.UniformFlowBridge
import QIQTH.UniformSecondJetCompact
import QIQTH.Christoffel2Jet
import QIQTH.BasepointSmoothDep
import QIQTH.BasepointFDeriv
import QIQTH.DecayOrderThree
import QIQTH.BasepointSecondJet
import QIQTH.BasepointJacobi2
import QIQTH.BasepointSecondJetFDeriv
import QIQTH.BasepointJetModulus
import QIQTH.BasepointJetLipschitz
import QIQTH.FlowVelocitySecondJet
import QIQTH.FlowVelocityJacobiField
import QIQTH.VelocitySecondJetId
import QIQTH.VelocityJacobiBaseDep
import QIQTH.AutonomousSmoothDep
import QIQTH.JacobiOperatorBaseDeriv
import QIQTH.JacobiOperatorFDeriv
import QIQTH.JacobiUniformSupply
import QIQTH.JacobiDoubledFamily
import QIQTH.DoubledFamilyConstruction
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyAssembly
import QIQTH.DoubledFamilyFullSupply
import QIQTH.DoubledFamilyConfine
import QIQTH.DoubledVariationField
import QIQTH.DoubledFamilyLink
import QIQTH.SecondVariationSupply
import QIQTH.SecondVariationLipschitz
import QIQTH.SecondVariationSourceLip
import QIQTH.CommonNondegRadius
import QIQTH.UniformFlowTransfer
import QIQTH.UniformFlowNondeg
import QIQTH.UniformFlowFDeriv
import QIQTH.UniformFlowNondegClose
import QIQTH.PullbackNondegFromFDeriv
import QIQTH.UniformRadiusCert
import QIQTH.UniformFlowPullback
import QIQTH.UniformFlowRegBound
import QIQTH.UniformFlowJacobianBound
import QIQTH.UniformPullbackEntryBound
import QIQTH.UniformFlowSecondJet
import QIQTH.UniformFlowSecondFDeriv
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowHessian
import QIQTH.UniformFlowHessianBound
import QIQTH.UniformFlowHessianDiag
import QIQTH.UniformFlowThirdJet
import QIQTH.UniformFlowThirdFDeriv
import QIQTH.QuadrupleFlowSupply
import QIQTH.UniformFlowThirdJetClose
import QIQTH.UniformFlowThirdBound
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowThirdDiag
import QIQTH.UniformFlowThirdUncond
import QIQTH.UniformFlowMetricC2
import QIQTH.UniformFlowMetricC2Bound
import QIQTH.UniformResidualB
import QIQTH.UniformInverseMetric
import QIQTH.UniformFlowMetricInvProps
import QIQTH.UniformFlowJetZero
import QIQTH.UniformResidualPacket
import QIQTH.UniformNearEngine
import QIQTH.UniformCutoffEngine
import QIQTH.UniformResidualBound
import QIQTH.UniformCoeffBound
import QIQTH.UniformTauResidual
import QIQTH.ResidualChartTransport
import QIQTH.PullbackNaturality
import QIQTH.PullbackNaturalityLocal
import QIQTH.GlobalResidualWitness
import QIQTH.UniformFlowLocalInverse
import QIQTH.GlobalWitnessHunif
import QIQTH.WidthMarginEngine
import QIQTH.NearIsometryBudget
import QIQTH.GlobalHunifAssembly
import QIQTH.HunifTrichotomy
import QIQTH.RadiusOrdering
import QIQTH.UniformChartRadius
import QIQTH.CapstoneWiring
import QIQTH.OrderNResidual
import QIQTH.ResidualN1GaussianBound
import QIQTH.RestrictedEboundW
import QIQTH.OrderOneTower
import QIQTH.OrderOneGeometry
import QIQTH.CoeffBoundsN1
import QIQTH.CoeffU1Fix
import QIQTH.GatedWitnessMeas
import QIQTH.GatedWitnessEmeas
import QIQTH.HeatConvRegularity
import QIQTH.ConcreteDominations
import QIQTH.GatedWitnessPackage
import QIQTH.HeatConvDeriv
import QIQTH.ConvApproximants
import QIQTH.ConvCarriesDischarge
import QIQTH.DeltaFamilyBoundary
import QIQTH.GaussianTailBoundary
import QIQTH.BoundaryAssembly
import QIQTH.TruncatedDuhamel
import QIQTH.DuhamelLimitWiring
import QIQTH.GaussianHessianCancel
import QIQTH.SliverEstimates
import QIQTH.AmplitudePackage
import QIQTH.ChartGaussAdapter
import QIQTH.ChartWrapperConcrete
import QIQTH.InverseChartDisplacement
import QIQTH.ChartJetHessian
import QIQTH.GaussianMomentEnvelope
import QIQTH.ChartJetBounds
import QIQTH.SliverAssembly
import QIQTH.InnerSliceBounds
import QIQTH.HessianSliceBound
import QIQTH.RemainderIntegration
import QIQTH.GaussReplaceSlice
import QIQTH.NormalFormDischarge
import QIQTH.LapTruncAssembly
import QIQTH.SliverSumPlumbing
import QIQTH.SecondOrderInterchange
import QIQTH.InterchangeThreading
import QIQTH.GeometricModuliThreading
import QIQTH.LeviLipschitz
import QIQTH.F2FamilyDischarge
import QIQTH.CapstoneStatus
import QIQTH.SpatialC2
import QIQTH.DaLimLocUnif
import QIQTH.FlowJointRegularity
import QIQTH.GeodesicGronwall
import QIQTH.ResidueThreading
import QIQTH.EngineInstantiation
import QIQTH.AmplitudeFamilyDischarge
import QIQTH.CConvLayerDischarge
import QIQTH.GeneralBaseJets
import QIQTH.UniformCRDischarge
import QIQTH.PartialsToFDeriv
import QIQTH.GcoefContinuity
import QIQTH.WitnessDerivDomination
import QIQTH.WitnessDerivMeasurability
import QIQTH.G2CarryDischarge
import QIQTH.HenvUInstantiation
import QIQTH.WitnessMeasDeriv
import QIQTH.GateChartMeasurability
import QIQTH.FoldedCoeffChartMeas
import QIQTH.ChartGeneralPContinuity
import QIQTH.GateSetMeasurability
import QIQTH.OnGateFieldRegularity
import QIQTH.ChartFieldC2General
import QIQTH.ConcreteGateAssembly
import QIQTH.GeomPTransportAssess
import QIQTH.TransportOpSmoothness
import QIQTH.HuInftyRebase
import QIQTH.JointMeasurability
import QIQTH.InnerKernelJointMeas
import QIQTH.CoeffContWdiffLift
import QIQTH.GateDiffWiringMeasSet
import QIQTH.InftyRebaseCapstone
import QIQTH.SliceInterfaceInstantiation
import QIQTH.CConvFacade
import QIQTH.FlowBallInstantiation
import QIQTH.GatedDInstantiation
import QIQTH.CompactTubeLemma
import QIQTH.ErrorKernelFactorization
import QIQTH.ErrorKernelJointMeas
import QIQTH.ParametrixGradientMeas
import QIQTH.CompactJetBounds
import QIQTH.GaussianGradAbsorption
import QIQTH.ChartThirdJet
import QIQTH.ThirdJetBounds
import QIQTH.GradEAssembly
import QIQTH.OmegaHsrcC4cAudit
import QIQTH.EboundWiringHD1
import QIQTH.SecondDerivEnvelope
import QIQTH.HD1SliverRoute
import QIQTH.HD1ConcreteWiring
import QIQTH.XUniformSliver
import QIQTH.XUniformSliverFull
import QIQTH.LeviCarriesAssembly
import QIQTH.GateOpennessExport
import QIQTH.LeviSeriesLocalData
import QIQTH.InterchangeLocalRebase
import QIQTH.CConvConcreteThreading
import QIQTH.GaussianApproxIdentity
import QIQTH.HDConvThreading
import QIQTH.TruncatedDuhamelData
import QIQTH.CapstoneAssembly
import QIQTH.HEmeasRecon
import QIQTH.FlowJointContinuity
import QIQTH.KernelJointContinuity
import QIQTH.HEmeasBorelAudit
import QIQTH.GatedDerivRepProduct
import QIQTH.GatedTauDerivRep
import QIQTH.ChartJetHessianMixed
import QIQTH.HD1CLMLift
import QIQTH.DaLimLUWallRecon
import QIQTH.ETailRateBound
import QIQTH.GrandAssemblyRecon
import QIQTH.AssemblyLadderR1R2
import QIQTH.AssemblyLadderR3
import QIQTH.AssemblyLadderR5
import QIQTH.ChartJointBorel
import QIQTH.ChartRepConstruction
import QIQTH.GatedChartMeasAudit
import QIQTH.RightInverseGeneral
import QIQTH.ImageSupportDischarge
import QIQTH.HgateSatAudit
import QIQTH.GatedRepSFix
import QIQTH.AssemblyV7Rethread
import QIQTH.ConcreteGateInstantiation
import QIQTH.OffSVanishing
import QIQTH.OnGateJets
import QIQTH.Field2NbhdReshape
import QIQTH.ChartRepFinal
import QIQTH.FlowDerivMeasurable
import QIQTH.AmpPdComposition
import QIQTH.GcConsumerMirror
import QIQTH.EnvelopeCoreDischarge
import QIQTH.DerivConvDischarge
import QIQTH.DataPileWitnessAudit
import QIQTH.InnerMeasFubini
import QIQTH.F2CarryDischarge2
import QIQTH.ContDomWindow
import QIQTH.JetsGcUnification
import QIQTH.SliverCConvBatch
import QIQTH.GaussianWidthTransfer
import QIQTH.InverseChartNormalJets
import QIQTH.WideWitnessAmplitude
import QIQTH.WideSliverBoundary
import QIQTH.FixedGateDichotomy
import QIQTH.SecondOrderMajorants
import QIQTH.SecondOrderInterchangeConcrete
import QIQTH.FixedGateSourceProviders
import QIQTH.WideA1Assembly
import QIQTH.WidthAdapters
import QIQTH.ResidualAssemblyRecon
import QIQTH.WideHIntDischarge
import QIQTH.TruncatedHIntRethread
import QIQTH.WideA1AssemblyTrunc
import QIQTH.InterfaceArrowCensus
import QIQTH.ProviderSideExports
import QIQTH.DaLimLUConcreteDischarge
import QIQTH.WideBoundaryLimDischarge
import QIQTH.ChartImageApproxIdentity
import QIQTH.ChartGaussianChangeVar
import QIQTH.ChartIFTPackage
import QIQTH.ChartImageAIConcrete
import QIQTH.BaseVaryingIFTPackage
import QIQTH.GeodesicReversalRoute
import QIQTH.TerminalVelC2
import QIQTH.FixedFChartImageAI
import QIQTH.BaseSlotAmplitude
import QIQTH.FixedFTrioDischarge
import QIQTH.EnrichedChartBundle
import QIQTH.GateAnnulusSplit
import QIQTH.MovingFBoundaryLim
import QIQTH.MovingCorrAssembly
import QIQTH.IterEContinuity
import QIQTH.HeatOpWitnessContinuity
import QIQTH.ParametrixPartsContinuity
import QIQTH.ParametrixSpatialPartials
import QIQTH.GatedWitnessHeatOpBridge
import QIQTH.ChartComposedHeatOp
import QIQTH.ChartJetFactsDischarge
import QIQTH.RDomEnvelope
import QIQTH.IterEEngineWiring
import QIQTH.InnerEngineRecursion
import QIQTH.ZeroCollarLocalZero
import QIQTH.FrozenBaseWChain
import QIQTH.HfgRadiusSelection
import QIQTH.GapACoverGapB
import QIQTH.HcontAssembly
import QIQTH.GapASdomInstantiation
import QIQTH.SdomHnearDischarge
import QIQTH.HgeoDischarge
import QIQTH.H2Instantiation
import QIQTH.TransitionAnnulusCont
import QIQTH.FullGateAssembly
import QIQTH.FastA5Fix
import QIQTH.HactiveWiring
import QIQTH.GateGeometryResiduals
import QIQTH.BoundaryLimAssembly
import QIQTH.MovingCorrRecombination
import QIQTH.EnvelopeWiringLocUnif
import QIQTH.LocUnifDerivConv
import QIQTH.TUniformFrozenAI
import QIQTH.HDerivConvComposition
import QIQTH.HDuhamelExportRethread
import QIQTH.HDConvGateThreading
import QIQTH.CConvFacadeGate
import QIQTH.S1TripleHEmeasGate
import QIQTH.VaryingRadiusS1Provider
import QIQTH.ConstRadiusGateExport
import QIQTH.OuterCarryRecon
import QIQTH.RicciSourceCoeff
import QIQTH.FacadeBundleFields
import QIQTH.B2MeasurabilityDissolution
import QIQTH.ChartParamFacadeVariant
import QIQTH.GaussianJetTheorem
import QIQTH.CConvV2Contracts
import QIQTH.CConvV2GaussianPairing
import QIQTH.CConvV2EnvelopeFromStar
import QIQTH.CConvV2LeviSource
import QIQTH.CConvV2ChartComparison
import QIQTH.CConvV2WitnessStar
import QIQTH.CConvV2ChartInterface
import QIQTH.CConvV2WgInstantiation
import QIQTH.CConvV2DerivRep
import QIQTH.CConvV2Facade
import QIQTH.DaLimCensusRecon
import QIQTH.DaLimEasyTranche
import QIQTH.DaLimHardTranche
import QIQTH.NCGaussPd3
import QIQTH.NCGaussToCyclicT
import QIQTH.NCRiemannTwoJet
import QIQTH.FrozenLaplaceSliver
import QIQTH.GlobalRawBoundFacade
import QIQTH.A1R6CoreAtGate
import QIQTH.A1R6SlotAdapters
import QIQTH.A1R6FromLabelled
import QIQTH.GaussLemmaFirstVariation
import QIQTH.GaussLemmaTransverse
import QIQTH.RiemannFirstPairAntisym
import QIQTH.GaussLemmaHomogeneity
import QIQTH.GaussLemmaAssembly
import QIQTH.GaussLemmaFlowData
import QIQTH.GaussInteriorMVT
import QIQTH.PullbackGeometryLegs
import QIQTH.Hpd2FromCyclic
import QIQTH.D2HExpandRecon
import QIQTH.HrepGermFactorization
import QIQTH.AmplitudeDataOnCollar
import QIQTH.SliverBoundOnCollar
import QIQTH.SliverTailMatched
import QIQTH.SliverOffCollarMatched
import QIQTH.SliverAssemblyMatched
import QIQTH.DisplacementDerivative
import QIQTH.CensusSweepOne
import QIQTH.HrawCampaignOne
import QIQTH.HrawChartTransfer
import QIQTH.HrawNearIsometryConcrete
import QIQTH.HrawPreCollapse
import QIQTH.Pd2ConvDissolution
import QIQTH.LabelledRethreadV2
import QIQTH.Pd2ConvPerU
import QIQTH.HgateCensusAssembly
import QIQTH.FrozenGermInternal
import QIQTH.HgateAffineRepair
import QIQTH.AffineRawResidual
import QIQTH.AffineGateTransport
import QIQTH.NearIsometry43Budget
import QIQTH.Transfer43Quad
import QIQTH.OnGateGlue
import QIQTH.PullbackAffineBallLeg
import QIQTH.AnnulusAffineLeg
import QIQTH.AnnulusAmbientTransfer
import QIQTH.AffineGateCapstone
import QIQTH.LegUniformization
import QIQTH.AnnulusUniformization
import QIQTH.CommonGateShell
import QIQTH.CensusGeometryThread
import QIQTH.CensusDominations
import QIQTH.SliceMeasurability
import QIQTH.JointContinuityAtoms
import QIQTH.DataLeviDischarge
import QIQTH.ECombinationDischarge
import QIQTH.ESLegWidening
import QIQTH.EveryCeilingFamilies
import QIQTH.AllUSliceMeas
import QIQTH.LapContBoxGlue
import QIQTH.CappedAdom2Audit
import QIQTH.MemAdjHiSliver
import QIQTH.NonLeviBoxContinuity
import QIQTH.LeviIterBoxInduction
import QIQTH.LeviMTest
import QIQTH.W2Package
import QIQTH.W2Finish
import QIQTH.AmpGeometryBundle
import QIQTH.AmpQuantBundle
import QIQTH.DataAmpAssembly
import QIQTH.GpowBridge
import QIQTH.GpowClosure
import QIQTH.SlotDischarges
import QIQTH.HDaHLapWiring
import QIQTH.PerUProviders
import QIQTH.HD1Concrete
import QIQTH.PerUCensusTuple
import QIQTH.ConstGateAssembly
import QIQTH.FinalA1Slots
import QIQTH.A1R6FromData
import QIQTH.HGaussAbsorb
import QIQTH.ConstRadiusAbsorb
import QIQTH.SlotsThreading
import QIQTH.DuhamelCoreThreaded
import QIQTH.TerminalCoverage
import QIQTH.MomentWallCoverage
import QIQTH.JointInstantiabilityAudit
import QIQTH.AuditPromotions
import QIQTH.SlotInstantiationI
import QIQTH.SlotInstantiationII
import QIQTH.SlotInstantiationIII
import QIQTH.SlotInstantiationIV
import QIQTH.SlotInstantiationV
import QIQTH.SlotInstantiationVI
import QIQTH.SlotInstantiationVII
import QIQTH.SlotInstantiationVIII
import QIQTH.InnerDataInstantiation
import QIQTH.InnerDataEnvelope
import QIQTH.PerUCensusInstantiation
import QIQTH.V2CensusInstantiation
import QIQTH.SliverRiskGate
import QIQTH.SupConstantFamily
import QIQTH.BaseSlotAmpDeriv
import QIQTH.ChartFieldJacobian
import QIQTH.ForwardFlowJet
import QIQTH.JacobiCLMExposure
import QIQTH.SupFamilyFirstOrder
import QIQTH.InnerDiffFamily
import QIQTH.FrozenProviderLegs
import QIQTH.FrozenHdiffLeg
import QIQTH.FrozenDominatorLegs
import QIQTH.SupBaseGeneral
import QIQTH.GeneralFieldContinuity
import QIQTH.UngatedChainRule
import QIQTH.HGintCutoff
import QIQTH.SliverSingularEngine
import QIQTH.ProfFacWitness
import QIQTH.ProfRateTheorem
import QIQTH.ProdMomentWitness
import QIQTH.ProdPtwiseWitness
import QIQTH.LeviCapWitness
import QIQTH.WeightedPairingHelper
import QIQTH.DHrefinedWitness
import QIQTH.ProdMeasAndEnvelope
import QIQTH.DHrefinedFull
import QIQTH.HerrHminCoercivity
import QIQTH.GateFarFieldSplit
import QIQTH.FarFieldDecay
import QIQTH.WallAInstantiation
import QIQTH.WallAThreading
import QIQTH.HInterGrounding
import QIQTH.HAdom2capGrounding
import QIQTH.HdiffGrounding
import QIQTH.InnerDataCensusThread
import QIQTH.PresentationBridges
import QIQTH.CLSlotWire
import QIQTH.Phase9Replumb
import QIQTH.HslotGrounding
import QIQTH.HcapEndpointGrounding
import QIQTH.BoxCensusGrounding
import QIQTH.HProvGrounding
import QIQTH.HFintDiagGrounding
import QIQTH.Phase14Transport
import QIQTH.BoxAtomsGrounding
import QIQTH.IterRungGrounding
import QIQTH.XSlotBaseParts
import QIQTH.WitnessSpatialPartialsX
import QIQTH.LeafBoxSplice
import QIQTH.SmoothCarrierGrounding
import QIQTH.ChartSecondJet
import QIQTH.Flow3Regularity
import QIQTH.SecondVariationModulus
import QIQTH.HbaseJ2Gronwall
import QIQTH.HbaseJ2Assembly
import QIQTH.Hfwd2Weld
import QIQTH.ExpRhoReachability
import QIQTH.OperatorPdBridge
import QIQTH.AmplitudeSecondJet
import QIQTH.C2CarrierCollapse
import QIQTH.Hid2Germ
import QIQTH.C2AggregatorPhase6
import QIQTH.FarFieldMomentOrder
import QIQTH.OnCollarMomentOrder
import QIQTH.RemainderAssembly
import QIQTH.FrameDecompLogDet
import QIQTH.ExpDiffVariation
import QIQTH.ExpJacobianFlow
import QIQTH.ExpMatrixJacobi
import QIQTH.ExpJacobianRegularity
import QIQTH.LogJacobianRegularity
import QIQTH.JacobiRescale
import QIQTH.JacobiDerivReal
import QIQTH.JacobiC2
import QIQTH.ExpJacobianRescale
import QIQTH.ExpJacobianRicci
import QIQTH.VanVleckRicciODE
import QIQTH.VanVleckLogDetSplit
import QIQTH.LogJSecondDerivRescale
import QIQTH.VanVleckGenericPoint
import QIQTH.Deriv2SubHalf
import QIQTH.VanVleckRayRicci
import QIQTH.VanVleckRayRicciAt
import QIQTH.VanVleckTransportRadial
import QIQTH.ParametrixTransportRadial
import QIQTH.ParametrixTransportRicci
import QIQTH.GaussianConvBound
import QIQTH.TimeSimplexBeta
import QIQTH.LeviSeries
import QIQTH.HeatParametrixAnsatz
import QIQTH.ParametrixFunction
import QIQTH.SpeciesCrossCheck
import QIQTH.TowerGNS.FlowContinuity
import QIQTH.TowerGNS.Generator
import QIQTH.TowerGNS.RightMul
import QIQTH.TowerGNS.Separation
import QIQTH.TowerGNS.Tomita
import QIQTH.TowerGNS.ConjClosure
import QIQTH.TowerGNS.TomitaBar
import QIQTH.TowerGNS.ConjAdjoint
import QIQTH.TowerGNS.ModularOp
import QIQTH.TowerGNS.ModularSurjective
import QIQTH.TowerGNS.ModularSelfAdjoint
import QIQTH.TowerGNS.Resolvent
import QIQTH.TowerGNS.ResolventOrder
import QIQTH.TowerGNS.ModularUnitary
import QIQTH.TowerGNS.ModularUnitaryCont
import QIQTH.TowerGNS.ModularUnitaryComm
import QIQTH.TowerGNS.ModularEigenbasis
import QIQTH.TowerGNS.ModularEigenvectors
import QIQTH.TowerGNS.ModularUnitaryEigen
import QIQTH.TowerGNS.Identification
import QIQTH.TowerGNS.TomitaFirstHalf
import QIQTH.TowerGNS.JStage
import QIQTH.TowerGNS.JEmbed
import QIQTH.TowerGNS.ConjPre
import QIQTH.TowerGNS.ModularConj
import QIQTH.TowerGNS.PolarCore
import QIQTH.TowerGNS.ConjFlow
import QIQTH.TowerGNS.ConjImplements
import QIQTH.TowerGNS.TomitaSecondHalf
import QIQTH.TowerGNS.CommutationTheorem
import QIQTH.TowerGNS.CommutationEquality
import QIQTH.TowerGNS.Factor
import QIQTH.LinearizedEinstein
import QIQTH.MatterCoupling
import QIQTH.WedgeBoostClausius
import QIQTH.AreaEmergence
import QIQTH.SoftGraviton
import QIQTH.CHMKernel
import QIQTH.BallClausius
import QIQTH.CHMTransport
import QIQTH.BridgeAssembly
import QIQTH.CHMSymbolProbe
import QIQTH.FreeFieldWedgePackage
import QIQTH.AreaDecoder
import QIQTH.CalibratedAreaLaw
import QIQTH.CodeEquilibrium
import QIQTH.DeserRung
import QIQTH.FormalDeser
import QIQTH.DualAction
import QIQTH.LogClockWeight
import QIQTH.ZClockRegression
import QIQTH.MonomialTrace
import QIQTH.EigenCore
import QIQTH.TraceCapacityFromCore
import QIQTH.FiniteCornerEigen
import QIQTH.BellMarginal
import QIQTH.Bell
import QIQTH.Tsirelson
-- Central audits proposed by GPT-5.5-pro:
import QIQTH.H1H2Audit
import QIQTH.NoConcentration
-- Entropy-focused audits from second GPT-5.5-pro consultation:
import QIQTH.EntropyBridge
-- Araki relative entropy via the relative modular operator (Phase A foundation):
import QIQTH.ArakiEntropy
import QIQTH.ArakiModularEntropy
-- Non-commutative matrix function calculus (the matrix power/trace derivative Mathlib lacks):
import QIQTH.MatrixFunctionCalculus
import QIQTH.BranchLedger
import QIQTH.ArakiInterface
-- Final non-entropy audits proposed by GPT-5.5-pro:
import QIQTH.FQDynamicsNoGo
import QIQTH.CompressionLocality
-- Born-rule audits from fourth GPT-5.5-pro consultation:
import QIQTH.NoBornFromNothing
import QIQTH.EquivarianceGap
import QIQTH.BornTypicality
-- Born from symmetric equiprobability (audit candidate ii): the Zurek amplitude→count bridge:
import QIQTH.BornEquiprobable
-- Sub-theorems B, C for the Canonical IC Measure Principle (sub-theorem A — the content-free
-- `TypicalityMackeyGleason` placeholder — was DELETED 2026-06, superseded by `EffectGleason`):
import QIQTH.OperationalNoGo
import QIQTH.FQEquivarianceUniqueness
-- Concrete finite-dim Goldstein-Struyve (Steps 2, 4 proved; 1, 3 axiomatized):
import QIQTH.GoldsteinStruyveFinDim
import QIQTH.GoldsteinStruyveStep3
import QIQTH.GoldsteinStruyveKronecker
import QIQTH.GoldsteinStruyveStep1
-- Regression suite: positive (non-vacuity) + negative (countermodel) witnesses:
import QIQTH.GoldsteinStruyveModels
-- Finite Born-typicality (non-vacuous replacement for the LLN placeholder content):
import QIQTH.BornTypicalityFinite
-- Quantum bridge: product trace factorization connecting Born weights to the product measure:
import QIQTH.BornTypicalityQuantum
-- λ-identification: the product-history Born measure is the UNIQUE additive measure
-- carrying the Born marginals, and equals the trace functional tr(ρ^⊗ⁿ · F_S):
import QIQTH.BornMeasureUniqueness
-- A1 strengthening: locality discharged from equivariance + local dynamics:
import QIQTH.MarginalLocality
-- General bipartite no-signaling for an ARBITRARY (possibly entangled) state — strengthens the
-- product-state ("toy") no-signaling: the local marginal is independent of the remote POVM choice:
import QIQTH.NoSignalingGeneral
-- P1 of the covariant-μ plan: coarse-graining naturality — the Born measures on a directed system
-- of measurement contexts are Kolmogorov-consistent (coarse Born = pushforward of fine Born):
import QIQTH.CoarseGrainNaturality
-- P3: the cylinder typicality (pre)measure on a directed projective system of finite contexts — a
-- canonical finite-record covariant μ (consistent, normalized, covariant) bypassing the TT walls:
import QIQTH.CylinderTypicality
-- XL-step Phase A smoke test: the Finset ι projective-family shape validated against Mathlib's
-- Kolmogorov extension — i.i.d. case gets a genuine σ-additive limit measure μ∞ via infinitePi:
import QIQTH.FiniteMarginals
-- XL-step A0: the matrix Born law as a PMF (bornPMF); the i.i.d. quantum history measure on ℕ→α
-- (σ-additive, Born marginals) — the concrete quantum endpoint of the reachable part of Phase A:
import QIQTH.QuantumHistoryMeasure
-- XL-step A2b: the general (correlated/entangled) Kolmogorov extension for FINITE discrete fibers —
-- every consistent finite-fiber marginal family has a σ-additive projective-limit measure μ∞:
import QIQTH.KolmogorovFiniteFiber
-- XL-step Phase B (formalizable core): the typicality measure is STATE-AGNOSTIC — any positive
-- normalized linear state ω on a net of compatible effects yields μ∞ (Type III₁ realization cited):
import QIQTH.StateNetMeasure
import QIQTH.HolographyScaffolding
-- Phase B Part A (first brick): a genuine infinite-dim NORMAL STATE on B(H) — the diagonal density
-- operator ω(x)=∑ pₙ⟨eₙ,x eₙ⟩ (positive, normalized, additive), bypassing general Schatten theory:
import QIQTH.NormalState
-- Phase B Part A — CLOSING THE LOOP on B(H): the diagonal normal state drives the EffectStateNet →
-- σ-additive μ∞ pipeline end-to-end (first fully infinite-dimensional instance of the prize):
import QIQTH.BHTypicalityMeasure
-- Phase B Part A — general trace-class step (Simon §1.1): the operator absolute value |T|=√(T⋆T) via
-- cfc on the nonneg-spectrum T⋆T (|T| self-adjoint, |T|²=T⋆T, ‖|T|x‖=‖Tx‖) — foundation of trace-class:
import QIQTH.AbsoluteValue
-- Toward the prize: the FREE-FIELD (finite-mode) covariant typicality measure — μ∞ on occupation-sector
-- histories, INVARIANT under the (geometry-moving) mode-permutation boost (finite-mode Lorentz action):
import QIQTH.FreeFieldTypicality
-- A6 strengthening: minimality/independence table for Born premises:
import QIQTH.BornMinimalityTable
-- A4 strengthening: Chebyshev concentration upgrading Born means to frequencies:
import QIQTH.BornConcentration
-- Open Problem 3b (Lorentz covariance): discrete sheaf skeleton + covariance
-- one-liner proved; AQFT analytic inputs named as interface axioms:
import QIQTH.LorentzSelection
-- Finite-dimensional Tomita–Takesaki (modular flow σ_t, KMS) proved from
-- matrix algebra + trace cyclicity — engine for the free-field finite-mode
-- record instance; NO axioms beyond the standard three:
import QIQTH.FiniteModularTheory
-- λ's pointer law, finite (Type I) shadow of Takesaki's conditional-expectation
-- criterion: σ(P)=P ⟺ [ρ,P]=0 (exact decoherence), algebraic Born weights are a
-- probability, the dephasing map is the ω-preserving conditional expectation;
-- NO axioms beyond the standard three:
import QIQTH.LambdaPointer
-- The weak/strong split of state-supervenience: naturality is f-blind (cannot
-- force Born), the α-family witnesses it, refinement-additivity is the strong
-- discriminating premise that linearizes; NO axioms beyond the standard three:
import QIQTH.WeakStrongSplit
-- λ's selection-event constructor: an explicit inverse-CDF selector from an
-- actuality seed — exactly one record per seed (single-world consistency) and
-- the uniform seed measure pushes to Born; NO axioms beyond the standard three:
import QIQTH.SelectionEvent
-- A particular finite inverse-CDF sampler (correct axiom-free arithmetic). Its
-- interpretation as a physical "finite-information λ" is RETRACTED after red-team
-- (the grid is ordering-dependent and breaks QIQT-H's own envariance + no-signaling;
-- finite value-space λ reproduces Born exactly with no deviation). See its header:
import QIQTH.FiniteInfoLambda
-- The finite-information λ that SURVIVES: a finite INDEX over a finite record
-- space with the EXACT Born law (Born-transparent). Machine-checks the dividing
-- line: the index preserves marginals + equal-weights, while the grid provably
-- BREAKS envariance and no-signaling. NO axioms beyond the standard three:
import QIQTH.FiniteIndexLambda
-- (Φ,λ) in a VERY LIMITED information space: the one-bit universe (M=2, exact
-- Born (p,1-p); the grid distorts it to (1/2,1/2) at N=2) and the
-- pre-statistical→statistical transition (Born as finite-sample frequency,
-- 1/(4Kε²)→0 as the number of actual records K→∞). NO axioms beyond standard three:
import QIQTH.TinyUniverse
-- (Φ,λ) at TWO bits: the actuality factors into two sub-bits λ=(λ_A,λ_B). New structure:
-- entanglement (product Φ → independent bits, joint = product of marginals; Bell Φ →
-- perfectly correlated bits with uniform marginals, joint ≠ product) + marginal/no-signaling.
-- NO axioms beyond the standard three:
import QIQTH.TwoBitUniverse
-- (Φ,λ) in an EIGHT-record (three-qubit) world with 1/2/3 bits of actuality: the
-- resolution hierarchy (k bits → 2^k-block coarse-graining, exact partial Born; 3 bits =
-- full per-record law) + the GHZ entropy ceiling (8 records but supported on 2, so even a
-- 2/3-bit λ reveals 1 bit; dimension ≠ information). NO axioms beyond the standard three:
import QIQTH.ThreeQubitUniverse
-- The (Φ,λ) record/area CONTRACT (labeled scaffold, NOT new physics): the four explicit
-- inputs (factorization → einselection → area-cap → λ), coarse-graining as a capacity-
-- non-increasing pushforward, and the area bridge in BOTH versions (Bousso entropy vs the
-- stronger dim-capacity postulate, kept distinct), threading postulates as HYPOTHESES (no
-- axioms). Metaselector = einselection, NOT capacity; operationally = Everett. Standard three:
import QIQTH.RecordContract
import QIQTH.DifferentialAreaLaw
import QIQTH.QiqtToGR
import QIQTH.QiqtGrWitness
import QIQTH.WedgeKMSToGR
-- T3-1: the four Clausius/area-law premises (bound/saturation/positivity/tightness) are theorems of
-- the finite QIQT entropy model + the holographic area-capacity identification, not assumptions.
import QIQTH.ClausiusFiniteWitness
-- GR scaffolding: the capstone HasDerivAt facts hS/hK derived from smoothness of the finite record law
-- (Shannon/KL derivatives; KL flat at equilibrium ⟹ hK from hS) — pure analysis, not the physics floor.
import QIQTH.EntropyDeriv
-- T3-1 Stage 2: the thermodynamic free-field QIQT→GR capstone — entropy/heat built from a finite record
-- law, hsat/hDnn/hD0 discharged via the witness; only the dynamical FQ capacity bound stays labelled.
import QIQTH.QiqtGrThermo
-- T3-3 continuum: the localization mode from the field (ff = (v^a ∂_a φ)·g₀); the per-generator hTkk
-- reduces to ONE universal mode calibration (Im ∫ conj g₀ g₀' = −1/ℏ).
import QIQTH.LocalizedMode
-- T3-3-C2: the concrete calibrated profile — a Gaussian wave packet satisfies the mode calibration,
-- closing the last analytic input (hcal) of the localization map.
import QIQTH.GaussianMode
-- GR scaffolding C: the localization discharge is not specific to one Gaussian — a width-parametrized
-- family gaussModeA (a>0) hits the SAME calibration 2π/ℏ for every width (reuses integral_gaussian a).
import QIQTH.GaussianModeFamily
-- T3-3-C3: the free-field QIQT→GR capstone with the localization mode CONSTRUCTED from φ
-- (ff = field-gradient · Gaussian), hTkk discharged in the GR theorem itself.
import QIQTH.QiqtGrGaussian
-- The maximally-discharged capstone: combines T3-1 (entropy from a finite record law) and T3-3-C3
-- (mode from φ) — hbridge/hFocus/hWarea/hsat/hDnn/hD0/hTkk/ff-block all discharged.
import QIQTH.QiqtGrComplete
-- T3-GR-Raychaudhuri: the congruence premises hWgeo/hWequil from one condition (W covariantly
-- constant), discharged fully for a flat (constant) metric.
import QIQTH.RaychaudhuriCongruence
-- The complete capstone with hWgeo/hWequil collapsed to the single covariant-constancy condition.
import QIQTH.QiqtGrCovCong
-- BORN-A1: Actuality Projective Consistency — grounding the Born additivity bridge in selector
-- no-signaling under outcome-refinement (Stage 1: honest coarse-graining selectors satisfy APC).
import QIQTH.BornActualityConsistency
-- BORN-C: μ-selection grounded in refinement equivariance (quantum equilibrium) — equivariance ⟹
-- selector no-signaling ⟹ (via BORN-A1) Born; the canonical measure is equivariant.
import QIQTH.BornMuSelection
-- A1-ppwave: a non-flat (curved) witness for the Raychaudhuri congruence premises — the pp-wave
-- metric whose null field ∂_v is covariantly constant (Stage 1: metric, inverse, symmetry).
import QIQTH.PPWaveMetric
-- A1+A2 worked example: QIQT→GR for the explicit pp-wave spacetime — all geometry (metric, tetrad
-- congruence, smoothness) discharged concretely; FQ/realization + matter field carried (conditional).
import QIQTH.QiqtGrPPWave
-- The instantiated SHOWCASE: pp-wave QIQT→GR with the floor laid bare — geometry + area-derivative hA
-- (via area_hasDerivAt_of_covConst) + entropy bound hbound (via shannon_le_log_card) all discharged;
-- only EOM (hKG) + FQ capacity (hcap) + the localization map (hS/hK) carried.
import QIQTH.QiqtGrShowcase
-- Sakharov Stage C: the per-mode Gaussian entanglement entropy S(ν)=(ν+½)log(ν+½)−(ν−½)log(ν−½),
-- the Srednicki building block summed by the entropy area law. S(½)=0 (pure), increasing, nonneg.
import QIQTH.GaussianStateEntropy
-- SG1: grounds gaussModeEntropy in first principles — it IS the Shannon/von Neumann entropy −∑ₖ pₖ log pₖ
-- of the thermal geometric occupation distribution pₖ=(1−q)qᵏ at ν=thermalNu q=(1+q)/(2(1−q)).
import QIQTH.GaussModeEntropyDerived
-- SG2/SG3/SG5: the entanglement-entropy AREA LAW S∝A for an EXPLICIT boundary-local Gaussian model
-- (each of the 6L² boundary plaquettes carries the same Srednicki modes) — turns the previously-carried
-- assumption S∝A into a theorem; the volume-law guard (bulk L³ vs boundary 6L²) isolates the locality input.
import QIQTH.BoundaryGaussianAreaLaw
import QIQTH.WilliamsonNormalForm
-- VACAREA-1: the regulated finite harmonic chain K_ε=m²−Δ_ε on a periodic lattice + its vacuum Gaussian
-- data (covariances X=½K^{−1/2}, P=½K^{1/2}; X·P=¼·1; reduced state on a subset; symplectic spectrum
-- =spec√(X_Ω P_Ω); entropy Σ gaussModeEntropy(ν_j)). Finite Gaussian INFRASTRUCTURE — NOT the area law.
import QIQTH.VacuumAreaLaw
-- The Sakharov/induced-gravity 1/4 RATIO (circularity-clean algebraic core): S_ent/(A/G_ind)=1/4 with the
-- matter coefficient + regulator cancelling; the geometric 4π/16π. Lean mirror of scripts/sakharov_kg.py.
import QIQTH.SakharovRatio
-- Born FROM PROJECTORS: the operator bridge grounding the record/area contract. For a
-- finite orthogonal PVM {P_r} and a normalized Φ, μ(r)=‖P_r Φ‖²=⟨Φ,P_rΦ⟩ is a genuine
-- RecordContract.RecordLaw — so the contract rests on Born-from-Φ, not a toy distribution.
-- First concrete piece of the decoherent record algebra. Standard three:
import QIQTH.BornProjBridge
-- SYMMETRY CANNOT BE THE METASELECTOR: the unitary group acts transitively on frameworks
-- (orthonormal bases), so any unitarily-invariant typicality score is CONSTANT — selects no
-- preferred framework. The continuous form of capacity_underdetermines_realm; closes the
-- "select the most typical framework by symmetry" route. The metaselector must be einselection.
import QIQTH.SymmetryNoGo
-- What DOES select the framework (the positive answer): EINSELECTION via Zurek's
-- commutativity criterion — a record commuting with the monitored observable A commutes with
-- the interaction A⊗B (decoherence-free); plus the finite-budget overlap floor (a holographic
-- dimension cap forces record overlap above D records). Complements the symmetry/capacity no-gos.
import QIQTH.MetaselectorSelection
-- STATE-ALONE no-go (completes the trilogy): a single projection P=|Φ⟩⟨Φ| generates only the
-- trivial framework {0,P,1−P,1} — a state alone cannot select a finer record basis. So neither
-- capacity, nor symmetry, nor Φ selects the framework: the metaselector is einselection.
import QIQTH.StateAloneNoGo
-- Continuum λ-law (Stage 1 of CONTINUUM_LAMBDA_ROADMAP): the modular automorphism
-- σ_t = Ad(Δ^{it}) on the genuine continuum modular flow, the continuum Takesaki
-- criterion, and continuum persistence (decoherence map commutes with σ_t ∀t,
-- unconditional for spectral pointers); NO axioms beyond the standard three:
import QIQTH.ContinuumLambda
-- Continuum λ-law Stage 2: the Type-independent algebraic Born rule via the
-- scalar spectral measure — the spectral measure of pointer Borel sets is a
-- genuine probability (no trace); NO axioms beyond the standard three:
import QIQTH.NaturalConeBorn
-- Continuum λ-law Stage 3: the continuum selection event — exactly one record per
-- actuality seed driven by the continuum Born weights, realizing Born; the
-- selection event is Type-blind (needs only the finite record structure). NO
-- axioms beyond the standard three:
import QIQTH.ContinuumSelection
-- Continuum λ-law Stage 4 capstone foundation: the second-quantized free-field
-- modular flow Γ(Δ^{it}) is a bijective isometry (vector-level unitarity), and
-- Weyl records on modular-fixed modes commute with it (Γ-level persistence); NO
-- axioms beyond the standard three:
import QIQTH.ContinuumLambdaFock
-- Γ(Δ^{it}) repackaged as a bounded operator on the Fock Hilbert space (the
-- ContinuousLinearMap one-parameter group), the substrate for field-level
-- Ad(Γ) persistence; NO axioms beyond the standard three:
import QIQTH.Fock.SecondQuantCLM
-- The continuum λ-persistence at the genuine FREE-FIELD level: the modular
-- automorphism σ_t = Ad(Γ(Δ^{it})), the field-level Takesaki criterion, and
-- field-level persistence (decoherence map commutes with σ_t ∀t) on the
-- second-quantized modular flow; NO axioms beyond the standard three:
import QIQTH.Fock.ContinuumLambdaField
-- The Born rule at the genuine free-field level: vacuum-state weights of a POVM
-- are a probability (instantiated at the Weyl-bit record POVM) — the Born layer
-- on the real Fock vacuum state; NO axioms beyond the standard three:
import QIQTH.Fock.FieldBorn
-- The selection event at the genuine free-field level: exactly one Weyl-bit
-- record per actuality seed, realizing the Fock-vacuum-state Born weights; NO
-- axioms beyond the standard three:
import QIQTH.Fock.FieldSelection
-- Free-field finite-mode instance: (a) holographic record count, (b) Gaussian
-- decoherence decay, (c) finite-mode Lorentz action — concrete theorems
-- instantiating parts of the LorentzSelection AQFT axioms; standard axioms only:
import QIQTH.FreeFieldRecord
-- Gleason-route μ construction (Open Problem 1): the deep finite-dim
-- effect-Gleason representation is one named axiom; the μ-is-Born history
-- corollary and the finite no-signaling marginal are PROVED from it:
import QIQTH.GleasonSelector
-- Strengthened Lorentz layer (GPT-5.5-pro A–G): externalized geometry (rigid
-- holographic bound + boundary), a real Poincaré GROUP action with covariance
-- ∀g, an equivariant-measure total-mass theorem that consumes covariance, and
-- the BORN LINK (normalization derived from GleasonSelector.born, not assumed).
-- Zero project axioms; turns the conditional interface rigid + connected:
import QIQTH.LorentzSelectionStrong
-- A CONCRETE NON-TRIVIAL model of the strengthened Lorentz interface: a genuine
-- 2-outcome PVM record system with Born weights (9/25, 16/25) — proves the
-- conditional interface is not vacuously satisfied only by the one-point net.
-- Does NOT touch the continuum realization (still open). Standard axioms only:
import QIQTH.LorentzWitness
-- Prize Stage 1 (PRIZE_EXECUTION_PLAN.md): a NON-TOY recorded-history net with genuine
-- marginalizing restriction and the product Born measure — the no-signaling marginal ω_marg is
-- a THEOREM about the product Born measure (vs LorentzWitness's trivial restriction). Axiom-free:
import QIQTH.FreeFieldNet
-- Prize Stage 1 (diamond-permuting action): a 2-atom diamond net (left,right ≤ top) whose
-- left↔right swap is a GENUINE non-trivial order-iso moving the geometry, exercising the
-- covariance machinery over a real orbit with a marginalizing restriction. Axiom-free:
import QIQTH.DiamondSwapNet
-- Prize Stage 2 (sheaf / gluing layer): global sections λ ∈ Γ(X) exist and are CLASSIFIED by the
-- top fibre for a poset directed to a greatest element — gluing unobstructed (Roberts–DHR cocycle
-- trivial for the product/finite case); selectors over the diamond net = joint records. Axiom-free:
import QIQTH.SheafSection
-- Phase 1 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md): the
-- projection-valued-measure / bounded-spectral-theorem keystone. Structural PVM
-- content proved axiom-free; the analytic core (σ-additivity, bounded-Borel FC,
-- spectral theorem) is the named Phase-1 target. General Mathlib-bound material;
-- ZERO project axioms:
import QIQTH.Spectral.PVM
-- Phase 1.3 (bounded spectral theorem, in progress): PVM_of_selfAdjoint from a bounded self-adjoint
-- T via cfc + Riesz–Markov + boundedFC_mul. Begins by validating cfc fires on B(H) (CStarAlgebra
-- (H→L[ℂ]H) instance). Both earlier-feared blockers (cfc-on-B(H), RMK representation) absent in v4.30.
import QIQTH.Spectral.SpectralTheorem
-- Stone M1 (STONE_THEOREM_PLAN Phase 1 / P4_TO_GR_MASTER_PLAN M1): the unbounded functional calculus
-- ∫ f dE on a PVM — the domain D(∫f dE) = {x : ∫ f² dμ_x < ∞} as a ℂ-submodule (the keystone toward
-- K = ∫ log(r/(2−r)) dE_R as a self-adjoint operator). Builds on scalarMeasure + the parallelogram law.
import QIQTH.Spectral.UnboundedFC
import QIQTH.Spectral.HeatSemigroup
import QIQTH.Spectral.MultiplicationOp
-- The POSITION PVM: E(A)=M_{𝟙_A} bundled as a genuine ProjectionValuedMeasure on L²(μ) (self-adjoint
-- idempotents, PV-content, strong HasSum σ-additivity). The route to the momentum PVM (Fourier) / boost gen.
import QIQTH.Spectral.PositionPVM
-- Unitary conjugation of a PVM: U E(A) U⁻¹ is again a PVM (the mechanism Fourier uses to carry the position
-- PVM to the momentum PVM). Unitary-generic, axiom-free.
import QIQTH.Spectral.PVMConj
-- The MOMENTUM PVM on L²(ℝ): Ê(A)=ℱ E(A) ℱ⁻¹, the Fourier–Plancherel conjugate of the position PVM (via
-- Mathlib's fourierTransformₗᵢ). A genuine ProjectionValuedMeasure, axiom-free — the spectral measure of P=ℱXℱ⁻¹.
import QIQTH.Spectral.MomentumPVM
-- The translation operator τ_t on L²(ℝ) ((τ_t f)(x)=f(x+t)): a ℂ-linear isometry, one-parameter group law
-- τ_s∘τ_t=τ_{s+t}. The unitary family whose generator is the momentum operator P (toward WedgeKMSFlux #5).
import QIQTH.Spectral.TranslationFlow
-- Translation-covariance of the position observable: conjugating the position PVM by τ_t shifts the Born
-- position distribution by t (the covariance making momentum the translation generator, conjugate to position).
import QIQTH.Spectral.PositionCovariance
-- The modulation operator e^{isX}=M_{e^{isx}} on L²(ℝ): a one-parameter UNITARY group (|e^{isx}|=1), generated by
-- the position operator X — the Fourier-dual of the translation group e^{itP}; the canonical pair behind the Weyl CCR.
import QIQTH.Spectral.ModulationFlow
-- STONE Phase 3.1 (P4-wall Phase 4.2): the infinitesimal generator A x=−i(d/dt U_t x)|₀ of a one-parameter operator
-- family, as an unbounded operator (LinearPMap) on the smooth domain. Self-adjointness (Cayley) is the frontier.
import QIQTH.Spectral.Stone
import QIQTH.Spectral.MomentumGenerator
-- CCR DUAL: the position operator X = stoneGen modulationLp = x· on L²(ℝ), the self-adjoint generator of the
-- modulation group e^{isX} — the Fourier-dual twin of momentumOp, completing the canonical CCR pair (P, X).
import QIQTH.Spectral.PositionGenerator
import QIQTH.Spectral.ModularGenerator
import QIQTH.Spectral.Garding
import QIQTH.Spectral.StoneProduct
import QIQTH.Spectral.StoneExp
import QIQTH.Spectral.PVMEigen
-- Prize Stage 3.1 (finite case): the matrix spectral theorem packaged as a PVM — eigenprojections
-- Pᵢ = U·diag(δᵢ)·U⋆ with ∑Pᵢ=1 (resolution of identity), Pᵢ²=Pᵢ, PᵢPⱼ=0, Pᵢ⋆=Pᵢ. The finite,
-- axiom-free case of the bounded-spectral-theorem target (continuum stays open). Standard axioms:
import QIQTH.SpectralPVM
-- Prize Stage 3′ (Track B): free-field / standard-subspace modular theory via the bounded-operator
-- approach of Rieffel–Van Daele (PJM 69, 1977). On Mathlib's StandardSubspace: the projections
-- P,Q onto 𝒦,i𝒦, R=P+Q, and RvD Prop 2.2(1) ⟪Rξ,ξ⟫=‖Pξ‖²+‖Qξ‖² (engine for R injective). Standard axioms:
import QIQTH.StandardSubspaceModular
-- Track B continuation: the CONTINUUM MODULAR FLOW Δ^{it}=u_t(R) of a standard subspace, via the
-- bounded BOREL functional calculus (boundedFC/PVM_of_selfAdjoint). u_t(r)=exp(it·log((2−r)/r)) is
-- discontinuous at the spectral endpoints r=0,2 (continuous cfc cannot reach it). One-parameter
-- unitary group: U_0=1, U_{s+t}=U_s·U_t, U_t⋆=U_{-t}, unitary. Standard axioms:
import QIQTH.StandardSubspaceModularFlow
-- P4-derivation Stage 1: the modular Hamiltonian K = −log Δ spectral function kFn(r)=log(r/(2−r)) and the
-- generator identity Δ^{it} = e^{−itK} (toward the JLMS route deriving the holographic capacity P4).
import QIQTH.ModularHamiltonian
-- Type II crossed product Increment 1a-0: the modular automorphism σ_t(a)=Δ^{it}aΔ^{-it} as a one-parameter
-- group of unital *-homomorphisms (the ℝ-action M ⋊_σ ℝ is built from) — toward an honest area operator.
import QIQTH.CrossedProduct
-- The Wall, Phase 1.1: measurability of the matter-rep fiber s ↦ σ_{-s}(a)(ξ s) on L²(ℝ;H) — toward π(a)
-- as an operator on the crossed-product Hilbert space (operator-valued Lp multiplication).
import QIQTH.CrossedProductRep
-- The Wall, Phase 2.1: the clock translation λ_t ξ = ξ(·+t) as a ℂ-linear isometry on L²(ℝ;H) — the L²(ℝ)
-- clock factor of the crossed product (via Mathlib compMeasurePreservingₗᵢ).
import QIQTH.CrossedProductTranslation
-- The Wall, Phase 3.1: the covariance λ_{-t} π(a) λ_t = π(σ_t a) — the defining identity of the crossed
-- product M ⋊_σ ℝ, joining the matter rep (Phase 1) and the clock group (Phase 2).
import QIQTH.CrossedProductCovariance
-- The Wall, Phase 4.1: strong continuity of the clock group λ_t — t ↦ λ_t ξ continuous in L²(ℝ;H), completing
-- "λ_t is a strongly-continuous one-parameter unitary group" (Stone's theorem hypothesis; X = the frontier).
import QIQTH.CrossedProductGenerator
import QIQTH.CrossedProductModularFlow
-- MODULAR RELATIVE ENTROPY (Phase B, one-particle / standard-subspace continuum object): the
-- Casini–Grillo–Pontello relative entropy of a coherent state vs vacuum, as the SCALAR spectral
-- integral S(ξ)=−∫log((2−r)/r)dμ^R_ξ over the bounded RvD operator R=P+Q (no unbounded log Δ).
-- entropyDensity = the modular-flow generator (modChar t r = exp(i t·g(r))); cgpEntropy + total
-- mass ‖ξ‖² + zero. Genuine continuum one-particle object (full vN-algebra needs Γ(Δ^{it}), cited).
import QIQTH.ModularRelativeEntropy
-- Stone M2: the modular Hamiltonian K = −log Δ as a GENUINE unbounded operator K = ∫ kFn dE_R (via the
-- unbounded FC), upgrading the spectral function; ⟨ξ,Kξ⟩ = cgpEntropy (operator-level JLMS first law).
import QIQTH.ModularHamiltonianOp
-- QIQT-H CORE (post-2026-06 GPT-5.5-pro strategic pivot): the conditional
-- representation theorem for single-outcome-without-collapse. The non-circular
-- finite-capacity exclusion (coactual_subsingleton) + actuality selector give
-- EXACTLY ONE actual record; collapse recovered as conditionalization. This —
-- NOT the Tomita–Takesaki tower — is the load-bearing part of the breakthrough:
import QIQTH.CoreNoCollapse
-- Capacity MODEL: DERIVES the finite-capacity bound (and the saturation premise)
-- of CoreNoCollapse from orthonormality of records in a finite-dim register
-- (∑ recDim ≤ D = finrank). Removes the "cost > Q_max/2" assumption for this model:
-- macroscopic_subsingleton is now a THEOREM. Grounds Strasberg et al. arXiv:2601.19703.
import QIQTH.CapacityModel
-- Grounding the subadditive core: pairwise overflow DERIVED from orthogonality of
-- distinct records (span-dimension joint cost; no additivity assumed):
import QIQTH.OrthogonalCapacity
-- Prize bridge C1: one actual RECORD → one actual VALUE (redundant same-value records
-- coexist; the experienced pointer value is unique), iterated to a unique value history:
import QIQTH.ValueSelection
-- Prize bridge C2: one-site Born — the prepared state's vector valuation on a PVM effect
-- IS the Born weight ‖Eᵣψ‖², packaged as a probability vector for the typicality layer:
import QIQTH.OneSiteBorn
-- THE PRIZE (C3+C4): join A and B — capacity-selected actual VALUE histories have the Born
-- PRODUCT law (from one-site calibration + independence) and are Born-typical; no collapse:
import QIQTH.BornJoin
-- Toward the REAL prize: DERIVE the single-trial Born law from NON-CONTEXTUALITY (effect-
-- Gleason) instead of assuming it — μ(Pₐ) = tr(ρ Pₐ) forced for any non-contextual assignment:
import QIQTH.OneSiteGleason
-- Wiring non-contextuality into the join: the ensemble's single-trial law p is FORCED Born
-- (no longer a free parameter); the representation with p DERIVED, only non-contextuality +
-- independence assumed:
import QIQTH.BornJoinGleason
-- Tier B (GPT-5.5-pro review): the BRIDGE theorem via Spectrum Broadcast Structures.
-- DERIVES the saturation premise cost>Q_max/2 from an objective record's redundancy +
-- an INFORMATION cost R·log n (tensor/log, fixing the rank-model flaw): distinguishability
-- ⇒ dimension (proved), broadcasting tensors spaces ⇒ dims multiply (proved), so a
-- macroscopic (redundant) record costs > half the capacity. Grounds arXiv:2007.04276 (SBS):
import QIQTH.SBSBridge
-- Discharging the ONE isolated physical input of the SBS chain (GPT-5.5-pro): the
-- per-collision distinguishability γ<1 is DERIVED from a concrete toy Hamiltonian
-- H_int = g σ_z^S ⊗ σ_x^E (Zurek collisional/QND monitoring). The branch-conditioned
-- records overlap by cos 2θ, so γ = |cos 2θ| < 1 for generic coupling; over L independent
-- collisions the overlap factorizes to γ^L → 0, feeding overlap_amplifies. Axiom-free.
import QIQTH.CollisionalGamma
-- Toward the PRIZE (PRIZE_ROADMAP.md, GPT-5.5-pro "be bold" plan): Stage 1 of the
-- Effect-Gleason route to the canonical covariant typicality measure μ. Extends the
-- single-state Gleason core (GleasonSelector.positive_ray_certain_forces_born) with the
-- two gaps the prize needs: Born tensor-multiplicativity (independent experiments factor)
-- and decoherent coarse-graining additivity (Born for ALL decoherent partitions). Axiom-free.
import QIQTH.RecordGleason
-- Toward the PRIZE, step G1 (GLEASON_SCOPE.md): finite-dimensional Busch/effect (POVM)
-- Gleason. Foundation installment — effect predicate + closure (0/1/smul/sub), μ 0 = 0,
-- monotonicity, scaling-additivity. Will discharge the finite-dim Mackey-Gleason axiom and
-- the Goldstein-Struyve Born-uniqueness axioms, and complete Stage 1. Axiom-free.
import QIQTH.EffectGleason
-- Prize Stage 1.2 (PRIZE_EXECUTION_PLAN.md): finite Covariant Record-Completeness, qubit case —
-- an explicit rational IC-POVM on ℂ² whose four record traces SEPARATE density matrices
-- (informationally complete), the finite case of the make-or-break lemma. Axiom-free:
import QIQTH.QubitIC
import QIQTH.Fock.OneParticle
import QIQTH.Fock.ExpKernel
import QIQTH.Fock.FockSpace
import QIQTH.Fock.VacuumState
import QIQTH.Fock.Weyl
import QIQTH.Fock.FockTypicality
import QIQTH.Fock.SecondQuant
import QIQTH.Fock.SecondQuantModularFlow
import QIQTH.Fock.OneParticleBW
import QIQTH.Fock.StressTensor.RapidityMomentum
import QIQTH.Fock.StressTensor.HorizonField
import QIQTH.Fock.StressTensor.NullStressFlux
import QIQTH.Fock.StressTensor.HorizonPlancherel
import QIQTH.Fock.StressTensor.HorizonFourier
import QIQTH.Fock.StressTensor.HorizonParseval
import QIQTH.Fock.StressTensor.L2Plancherel
import QIQTH.Fock.StressTensor.WedgeBoostWiring
import QIQTH.StripUniqueness
import QIQTH.KMSCorrelation
import QIQTH.Fock.RelativeModularFlow
import QIQTH.Fock.WeylOp
import QIQTH.Fock.WeylCovariance
import QIQTH.Fock.WeylCCR
import QIQTH.Fock.WeylBit
import QIQTH.Fock.WeylBitProcess
import QIQTH.Fock.WeylBitMeasure
import QIQTH.Fock.WeylBitConsistency
import QIQTH.Fock.WeylBitStrongDecoherence
import QIQTH.Fock.WeylBitBell
import QIQTH.Fock.WeylBitEffect
import QIQTH.Fock.WeylBitGeoCovariance
import QIQTH.Fock.LocalizationSkeleton
import QIQTH.Fock.WeylCLM
import QIQTH.Fock.BoostOrbit
import QIQTH.Fock.Localization
import QIQTH.Fock.WedgeAnalyticity
import QIQTH.Fock.BoostKMS
import QIQTH.Fock.SchwartzDecay
import QIQTH.Fock.PauliJordan
import QIQTH.Fock.LocalizedCovariance
import QIQTH.Fock.LocalizedWitness
import QIQTH.Fock.CyclicWitness
import QIQTH.Fock.FreeFieldHFlux
import QIQTH.Fock.FieldBWUnconditional
import QIQTH.Fock.TranslationCovariance
import QIQTH.Fock.Dirac.QuasiFreeEntropy
import QIQTH.Fock.Dirac.CAR
import QIQTH.Fock.Dirac.Parity
import QIQTH.Fock.Dirac.KleinTwist
import QIQTH.Fock.Dirac.KleinTwistUnitary
import QIQTH.Fock.Dirac.KleinTwistWitness
import QIQTH.Fock.Dirac.FermiDirac
import QIQTH.Fock.Dirac.EvenObservables
import QIQTH.Fock.Dirac.DiracGamma
import QIQTH.Fock.Dirac.LocalDifferentialSupport
import QIQTH.Fock.Dirac.FockKleinTwist
import QIQTH.Fock.Dirac.PhysLeanBridge
import QIQTH.Fock.Dirac.PhysLeanGammaBridge
import QIQTH.Fock.Dirac.ModularKMS
import QIQTH.Fock.Dirac.CARModularFlow
import QIQTH.Fock.Dirac.GradedCapacity

import QIQTH.Fock.Photon.PhotonFock
import QIQTH.Fock.Photon.PhotonCapacity
import QIQTH.Fock.Photon.PhotonUnruh
import QIQTH.Fock.Photon.PhotonModularFlow
import QIQTH.Fock.Photon.PhotonGaugeRecords
import QIQTH.Fock.Photon.PhotonEdgeModes
import QIQTH.Fock.Photon.PhotonFluxSectors
import QIQTH.Fock.Photon.PhotonBRST
import QIQTH.Fock.Photon.PhotonFieldStrength
import QIQTH.Fock.Photon.PhotonHelicity
import QIQTH.Fock.Photon.PhysLeanEMBridge

import QIQTH.RefinementBorn
import QIQTH.SBSBoolean
import QIQTH.SBSSuppression
import QIQTH.RedundancyCompressible
import QIQTH.CovariantGluing
import QIQTH.ContextualitySafe
import QIQTH.SelectorRefinement
import QIQTH.SelectionDynamics
import QIQTH.BornRoutes
import QIQTH.Envariance
import QIQTH.EnvarianceJustification
import QIQTH.StateSupervenience
import QIQTH.Relaxation
import QIQTH.RankCountNoGo
import QIQTH.BornChain
import QIQTH.RotationBorn
import QIQTH.SymmetrySquare
import QIQTH.RealmSelection
import QIQTH.EinsteinEquationOfState
import QIQTH.SpectralSum
import QIQTH.EntanglementFirstLaw
import QIQTH.Curvature
import QIQTH.RadialDistance
import QIQTH.RNCDecay
-- GEO1: the geodesic ODE of a component connection — local existence + uniqueness via Picard–Lindelöf
-- on the phase space Point n × Point n. Geodesic EXISTENCE only: NOT the exp-map / normal coordinates,
-- does NOT discharge the RNC gauge (gated on smooth dependence on IC, absent from Mathlib), NOT numerical-G.
import QIQTH.Geodesic
import QIQTH.ParallelTransportField
import QIQTH.FrameTransportField
import QIQTH.FrameGeodesicAlign
import QIQTH.ParallelOrthoFrameData
import QIQTH.ParallelTransportParallel
import QIQTH.FrameTransportParallel
-- RNC1: the √det g atom of the Riemann-normal-coordinate 2nd-order expansion — √det g = 1 − ⅙R_{cd}x^cx^d,
-- CONDITIONAL on a carried tr∂∂g(0)=−⅔Ric (RNC3 discharges it). The ⅙ = source of the κ=1/6 conformal factor.
-- NOT numerical-G, NOT a curved heat kernel. Standard three axioms.
import QIQTH.RNCExpansion
-- exp-map campaign, first bricks: the STRICT derivative of the geodesic field at the equilibrium
-- e=(p,0) is the explicit A(ξ,η)=(η,0) (S2, HasStrictFDerivAt_geodesicField); the geodesic rescaling
-- γ_{p,sv}(t)=γ_{p,v}(st) as a property of any integral curve (S1, geodesic_rescale); and the flow
-- scaffolding (geodesicSol as a function + expMap). Groundwork toward HasStrictFDerivAt exp_p id 0 →
-- the RNC local diffeo; NOT yet exp_p's strict derivative, NOT the diffeo, NOT the RNC gauge, NOT
-- numerical-G. Axiom-free (standard three).
import QIQTH.ExpMap
import QIQTH.GeodesicVariation
import QIQTH.GeodesicSmoothDep
import QIQTH.JacobiEquation
import QIQTH.JacobiSecondOrderLocal
import QIQTH.ExpFlowJacobi
import QIQTH.CovariantJacobi
import QIQTH.ExpMapContDiff
import QIQTH.ExpMapContDiff2
import QIQTH.ExpMapContDiff3
import QIQTH.GeodesicFieldJets
import QIQTH.PullbackMetric
import QIQTH.JacobianDet
import QIQTH.JacobianRadial
import QIQTH.VanVleck
import QIQTH.Polarization
import QIQTH.RNCGauge
import QIQTH.RNCGaugeExp
import QIQTH.EinsteinFieldEquation
import QIQTH.KGStressConservation
import QIQTH.QiqtGrExplicitKG
import QIQTH.QiqtGrFreeField
import QIQTH.HTkkPhysical
import QIQTH.KGSymplectic
import QIQTH.RicciSymm
import QIQTH.ChristoffelSmooth
import QIQTH.HregExplicitKG
import QIQTH.ManifoldCurvature
import QIQTH.ManifoldCommutator
import QIQTH.PseudoRiemannian
import QIQTH.LeviCivita
import QIQTH.ClausiusIntegral
import QIQTH.ClausiusToPernull
import QIQTH.Raychaudhuri
import QIQTH.RaychaudhuriConstCurv
import QIQTH.Unruh
import QIQTH.FQBoundConditional
import QIQTH.FQBoundCGP
import QIQTH.FQBoundMicro
import QIQTH.GRFromMicro
import QIQTH.CodeCapacityBridge
import QIQTH.CornerConstruction
import QIQTH.EmergentSpacetime
import QIQTH.MetricFromState
import QIQTH.MetricRefinement
import QIQTH.MetricRefinement2D
import QIQTH.ContinuumLimit
import QIQTH.IsotropyNoGo
import QIQTH.StencilGraph
import QIQTH.StencilWalk
import QIQTH.StencilDistortion
import QIQTH.StencilGH
import QIQTH.StencilDimGraph
import QIQTH.StencilDimWalk
import QIQTH.StencilDimDistortion
import QIQTH.StencilDimGH
import QIQTH.StencilFromState
import QIQTH.TorusStencilGraph
import QIQTH.TorusStencilWalk
import QIQTH.TorusStencilGH
import QIQTH.TripodGH
import QIQTH.ConeMetric
import QIQTH.ConeGH
import QIQTH.TorusFromState
import QIQTH.TripodFromState
import QIQTH.SphereMetric
import QIQTH.SphereGH
import QIQTH.ConeIntrinsicGraph
import QIQTH.ConeIntrinsicWalk
import QIQTH.ConeIntrinsicGH
import QIQTH.ConeFromState
import QIQTH.ConeFlat
import QIQTH.HawkingWick
import QIQTH.MinkowskiDiamond
import QIQTH.CausalStencil
import QIQTH.DeSitterTime
import QIQTH.RecordChannel
import QIQTH.RecordEquilibrium
import QIQTH.RecordUnraveling
import QIQTH.InteractingChannel
import QIQTH.PointerCompetition
import QIQTH.BulkRelaxation
import QIQTH.ContinuumEntropy
import QIQTH.HeatKernelThermal
import QIQTH.ConicalHeatKernel
import QIQTH.ConicalSakharov
import QIQTH.SaturationBridge
import QIQTH.OneLoopDeterminant
import QIQTH.ReplicaContinuation
import QIQTH.CorrespondenceAssembly
import QIQTH.SeeleyDeWittInterface
import QIQTH.HeatTraceAsymptotics
import QIQTH.BulkGeneration
import QIQTH.ScaleDimension
import QIQTH.BulkAutonomy
import QIQTH.CoordinateCurvature
import QIQTH.CurvatureBridge
import QIQTH.HyperbolicPlane
import QIQTH.RevolutionSurface
import QIQTH.HeatCoeffDetermination
import QIQTH.HeatCoeff2Determination
import QIQTH.HeatCoeff3Determination
import QIQTH.HeatCoeffBridge
import QIQTH.DeWittDiagonal
import QIQTH.LaplaceBeltrami
import QIQTH.HeatDuhamel
import QIQTH.TrueHeatKernel
import QIQTH.HeatTransportRecursion
import QIQTH.RadialTransport
import QIQTH.HeatParametrixError
import QIQTH.HeatParametrixOrder
import QIQTH.HeatResidualBound
import QIQTH.VanVleckCancellation
import QIQTH.VanVleckRadial
import QIQTH.VanVleckTwoJet
import QIQTH.A1GaugeDischarge
import QIQTH.ResidueBound
import QIQTH.HeatParametrixTrace
import QIQTH.HeatParametrixTraceDerived
import QIQTH.FlatTorusHeatKernel
import QIQTH.SphereHeatTrace
import QIQTH.Sphere3HeatTrace
import QIQTH.Sphere3HeatTraceA1
import QIQTH.ProductHeatTrace
import QIQTH.TraceClass.HilbertSchmidt
import QIQTH.TraceClass.Trace
import QIQTH.TraceClass.Cyclic
import QIQTH.TraceClass.Spectral
import QIQTH.TraceClass.CompactSpectral
import QIQTH.TraceClass.Compact
import QIQTH.TraceClass.ResolventSpectrum
import QIQTH.TraceClass.IntegralKernel
import QIQTH.TraceClass.IntegralKernelHS
import QIQTH.TraceClass.Mercer
import QIQTH.BellCutRank
import QIQTH.ReducedDensity
import QIQTH.RecordMincut
import QIQTH.RecordMincutMPS
import QIQTH.RecordMincutEntropy
import QIQTH.OneParticleMeasure
import QIQTH.WeightedL2
import QIQTH.PosFreqDomain
import QIQTH.OneParticleInner
import QIQTH.PosFreqInner
import QIQTH.OneParticleBoost
import QIQTH.OneParticleMap
import QIQTH.OneParticleFockBridge
import QIQTH.FreeFieldCorner
import QIQTH.QG.FinitePoincareNoGo
import QIQTH.QG.LatticeDispersionBound
import QIQTH.QG.CpsuvGate
import QIQTH.QG.DiamondTipGate
import QIQTH.QG.StateLevelLVGate
import QIQTH.QG.FiniteModularRecurrence
import QIQTH.QG.LatticeDispersion
import QIQTH.QG.FiniteTracePhase5
import QIQTH.QG.ExactRT
import QIQTH.QG.MaxFlowMinCut
import QIQTH.QG.MinCutRecords
import QIQTH.QG.WardSpeedSplitting
import QIQTH.QG.CpsuvEscape
import QIQTH.QG.FiniteMatterNoLorentz
import QIQTH.QG.EntropyNotCardinality
-- THE NON-TRACIALITY campaign, N1: the finite Gibbs state is genuinely non-tracial —
-- ω(E_{nm}·E_{mn}) = w_n ≠ w_m = ω(E_{mn}·E_{nm}) when the weights differ. HONEST SCOPE:
-- a state-level inequality, NOT a type classification (see the file header). Standard three:
import QIQTH.NonTracial.FiniteNonTrace
import QIQTH.NonTracial.TowerNonTrace
import QIQTH.NonTracial.ModularNonTrivial
import QIQTH.NonTracial.Checkpoint
import QIQTH.NonTracial.ModularDataComplete
import QIQTH.ConcreteRemainderOrder
import QIQTH.AmpDiffGrounding
import QIQTH.FormGateGrounding
import QIQTH.GaussianMomentExtraction

import QIQTH.DuhamelSimplexAssembly
import QIQTH.SliceBoundO1
import QIQTH.CorrHigherReduction
-- J4-504: residual factorization `E₁ = t·G·q` for the two-term parametrix `G·(u₀+t·u₁)` —
-- (a) reusable Leibniz engine `heatOpFun_mul`, (b) factorization `E = −t·G·Δu₁` MODULO two carried
-- transport-cancellation equations, (c) flat-model witness (hyps inhabited, E=0). std-3, a₁=R/6 CONDITIONAL.
import QIQTH.ResidualFactorization
-- J4-505: REDUCTION of the k=0 van-Vleck transport eqn `hT0` (`𝒯u₀=0`) to a scalar radial equation
-- via banked flat-Gaussian gradient calculus: cross-gradient `C(u)=−(1/2t)·G·R_g(u)`, `hT0` discharged
-- from radial input `hRad`, Gauss-lemma input isolated. std-3, hRad CARRIED, a₁=R/6 CONDITIONAL.
import QIQTH.TransportEqZero
-- J4-506: REDUCTION of the k=1 van-Vleck transport eqn `hT1` (`(𝒯+1)u₁=Δu₀`) to a scalar radial
-- equation `hRad1` via the SAME generic cross-gradient reduction; `hT1` discharged from `hRad1`,
-- factorization now modulo BOTH {hRad0,hRad1} (same Gauss-lemma family). std-3, hRad1 CARRIED.
import QIQTH.TransportEqOne
-- J4-507: NAME the single geometric input closing BOTH hRad0/hRad1 — the coordinate GAUSS LEMMA
-- `CoordGaussGauge : ∀x j, Σᵢ gⁱʲxᵢ = xʲ`; residual factorization from ONE named gauge + Euler eqns;
-- ∀x flat witness; bridge to mainline `hGauss` germ. VERDICT (c): irreducible geodesic/exp-map floor
-- (NOT derivable from finite `hgauge`). std-3, Gauss lemma CARRIED.
import QIQTH.GaussLemmaGauge
-- J4-510: CURVED-parametrix heat-mass → 1 (approximate-identity sub-lemma vs the J4-509 flat-only
-- obstruction). `heatParametrix_setMass_tendsto_one`: ∫_{w∈Ω} heatParametrix N Θ u τ w → 1 over a
-- FIXED neighbourhood Ω, from Θ(0)=1 ∧ u₀(0)=1 + continuity + eventual a.e.-meas/uniform-bound; L=1
-- PROVED (not assumed) via joint continuity. Reuses banked ChartImageApproxIdentity moving approx-id.
-- Curved certificate (Θ=1+‖w‖², Θ≢1) proves NOT flat-only. Decouples hmassone's CONTENT from hframeK;
-- full hmassone still needs Layer-A/B chart transfer + Jacobian. std-3.
import QIQTH.CurvedParametrixMass
-- J4-511: the `hmassone` CHART-BRIDGE (second fix piece decoupling hmassone from hframeK). Route B:
-- `weightedParametrix_setMass_tendsto_one` (∫_Ω gaussDdim·(parametrixAmp·φ) → 1 for a fixed chart
-- weight φ with φ(0)=1) → `chartMass_tendsto_one_of_weightedCovar` transports across an abstract
-- eventual change-of-variables `hcov` to the z-variable ∫_z Wit τ 0 z → 1 on 𝓝[>]0 →
-- `gatedKernel_mass_tendsto_one_of_localChart` = the exact atTop/epsSeq `hmassone` shape. φ(0)=1 (=
-- first-order Jacobian J(0)=1) is the SOLE normalisation — NO hframeK/g=δ-on-nbhd. Curved certificate
-- (Θ=1+‖w‖²≢1, φ=(1+‖w‖²)⁻¹≢1) proves NOT flat-only. Concrete base-varying CoV bundle for W₀ still
-- MISSING; hframeK also lives in hDaLimLU. std-3.
import QIQTH.MassChartBridge
-- J4-512: DECOUPLING `hframeK` (g=δ on a neighbourhood) from the Da-limit GAUGE members of
-- `GlobalRawBoundFacade.hDaLimLU_from_labelled` (the SECOND flat-only channel after J4-510/511's
-- `hmassone`). AUDIT: `hframeK` enters the capstone at exactly ONE place — `gauge_from_geometry` —
-- and is used ONLY as `hframeK 0 hK0`, i.e. to extract the 0-jet VALUE `g(0)=δ`; the two gauge members
-- `MemGaugeGi`/`MemGaugeGamma` are pointwise-at-0. `gauge_from_pointwise` rebuilds both from the
-- pointwise RNC jet {hg0 (value), hdg0 (1-jet), hinvF} with `hframeK`/`hK0` REMOVED (role (c),
-- value-reducible). CURVED GATE: `curved_gauge_inhabited` — a conformal witness (confMetric on Point 2)
-- satisfies {hg0,hdg0,hinvF} yet has ∂²g₀₀(0)=2≠0, so the decoupled antecedent is curved-satisfiable
-- (NOT vacuous, NOT secretly flat). NOT a₁=R/6. std-3.
import QIQTH.DaLimCurvedGauge

-- J4-514: Layer-A on-gate factorization — vanVleckGatedWitness τ 0 z factors as
-- gaussDdim τ (W₀ z)·chartFieldAmp; the amplitude origin value normalizes to
-- exactly 1 as τ→0⁺ (needs only det(g 0)=1, curved-safe). The de-risking gateway
-- for the Layer-B change-of-variables. std-3.
import QIQTH.LayerAFactorization

-- J4-515: Layer-B change-of-variables MAJORANT — the Gaussian-phase domination
-- gaussDdim τ (W₀ z) ≤ gaussDdimWide τ z for the base-varying inverse chart W₀,
-- from the banked two-sided near-isometry (half radial lower bound ½·r² ≤ r²(W₀z)).
-- ⚠ WIDTH 4τ→8τ: a MAJORANT for integrability/hbound/tail control ONLY (wrong total
-- mass 2^{n/2}), NOT the exact CoV/unit mass. Discharges the integrability side of the
-- concrete hcov; M1–M4 + exact CoV equality + assembly remain. Curved-satisfiable. std-3.
import QIQTH.LayerBChangeVars

-- J4-516: M4 (|det DW₀(0)| = 1) as STANDALONE pinnable lemmas — chartW0_hasFDerivAt_zero
-- (fderiv W₀ 0 = -id) + chartW0_fderiv_zero + chartW0_absdet_fderiv_zero. DON'T-UNDERCREDIT:
-- M4 was already banked inside BaseVaryingIFTPackage / EnrichedChartBundle (the J4-515 "M4
-- BLOCKED" note was stale); this file extracts the buried conjuncts as directly-consumable
-- lemmas, reusing baseVaryingChart_hasFDerivAt_center. Dimension-only, curved-generic. std-3.
import QIQTH.ChartW0Fderiv
-- J4-519: CURVED-VALID hraw-channel rewire of the final facade a1_R6_from_labelled —
-- a1_R6_from_labelled_curved swaps the step (vii) flat-only LINEAR hraw (GlobalGatedRawBound,
-- curved-unsatisfiable) for the honest curved-VALID on-gate width-4/3 QUADRATIC hgate carry,
-- routing hDa through the banked LabelledRethreadV2.hDaLimLU_from_hgate. Coefficient-neutral;
-- removes ONE of the capstone's flat-only channels. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.A1R6FromLabelledCurved

-- J4-520: the CURVED-VALID hframeK-channel rewire of the a₁ capstone, built on J4-519 —
-- a1_R6_from_labelled_curved_gauge removes the SECOND flat-only binder, the neighbourhood
-- frame hframeK (∀ q∈K, g q=δ, which forces ∂²g=0⟹Ric(0)=0), routing hDa through
-- hDaLimLU_from_hgate_gauge (gauge census rebuilt from the pointwise RNC jet {hg0,hinvF,hdg0}
-- via DaLimCurvedGauge.gauge_from_pointwise). BOTH flat-only capstone binders now removed
-- (2 of 3). Curved-satisfiable (J4-512 confMetric). NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.A1R6FromLabelledCurvedGauge

-- J4-521: boundary-threaded curved-signature a₁ capstone. Supplies the opaque hBoundaryLim
-- (Section H) from the banked EnvelopeWiringLocUnif.hBoundaryLim_DONE (dataLevi REUSED as its
-- hLocal; htT/hgdet0 derived), replacing it with concrete curved-valid analytic + RNC-geometry +
-- window-floor data. All three flat-only/pending capstone items (hraw, hframeK, hBoundaryLim) now
-- resolved from the signature — 3 of 3. NOT a₁=R/6 (CONDITIONAL: iterE positive-time continuity,
-- htr/hGauss bridges, full RNC curved witness remain). std-3.
import QIQTH.A1R6FromLabelledCurvedBoundary

-- J4-523: a genuinely CURVED RNC witness for the hGauss geometric floor. curvedRNCMetric K
-- x i j = δ_ij − (K/3)(‖x‖²δ_ij − x_i x_j) satisfies MetricGaussGauge EXACTLY (∀x, all orders)
-- — the first curved inhabitant of the Gauss-lemma floor beyond the flat metric — and feeds the
-- capstone's labelled hGauss germ. Its metric-Hessian trace ∑_a ∂∂g_aa(0) = −(2/3)(n−1)K δ (the
-- htr=−(2/3)Ric datum) is ≠0 for K≠0, n≥2: genuinely curved (Ric(0)=(n−1)Kδ≠0), NOT a
-- confMetric-lookalike (those fail hGauss). Inhabits the geometric slice only; the full ~280-binder
-- capstone antecedent (analytic piles) is NOT thereby non-vacuous. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.CurvedRNCGaussWitness

-- J4-524: the GaussHessianCyclic → hgauge bridge. Collapses the christoffel-symmetrization
-- normal-coordinate gauge hgauge (∂_{(a}Γ^i_{bc)}(0)=0, consumed by RNCExpansion.rnc_htr_of_gauge)
-- to the pure metric-second-derivative identity GaussHessianCyclic (∂_q∂_p g_ir(0) cyclic sum = 0),
-- the triple-differentiated shadow of the radial Gauss gauge. Pure jet algebra atop pd_christoffel_origin
-- + Schwarz. The CURVED witness g^K then DISCHARGES hgauge concretely (curvedRNCMetric_hgauge, first
-- curved inhabitant of the Christoffel gauge) and its htr = −(2/3)Ric is DERIVED from the gauge
-- (curvedRNCMetric_htr_from_gauge), pinning Ric(0)=(n−1)Kδ (curvedRNCMetric_ricci_from_gauge). The
-- geometric side of g^K is now self-contained. Remaining: MetricGaussGauge → GaussHessianCyclic
-- (triple-diff), plus the ~250-binder ANALYTIC instantiation. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.GaussGaugeToHgauge

-- J4-525: the g^K inverse-metric gauge bundle. The capstone antecedent binds the inverse metric gi as
-- a FREE function paired with g via hinvF (∑_σ g_cσ gi_σd = δ ∀y); flat δ FAILS this off the origin
-- (would force g=δ), so gi must be the true Sherman–Morrison inverse curvedRNCInv K x = (1/α)(δ −
-- (K/3)x⊗x), α=1−(K/3)‖x‖². For K<0, α≥1>0 globally ⟹ gi smooth (curvedRNCInv_contDiff) and
-- g^K·gi^K=δ EVERYWHERE (curvedRNCMetric_hinvF, via the exact radial Gauss lemma) — first curved
-- inhabitant of hinvF. curvedRNC_geomGaugeBundle packages the geometric+gauge HALF of the antecedent
-- (banked hg/hgsymm/hg0/hdg0/hGauss + new hgi/hgiC/hinvF/hΓ), K<0 genuinely curved. The ANALYTIC piles
-- (heat-kernel Gaussian dominations, Levi series) + hgpos REMAIN. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.CurvedRNCGaugeBundle
-- J4-526 (CurvedRNCPosDef): hgpos for g^K. wᵀg^K(x)w = ‖w‖²+(K/3)(⟨x,w⟩²−‖x‖²‖w‖²) (curvedRNCMetric_quadForm);
-- for K≤0 Cauchy–Schwarz ⇒ ≥‖w‖²>0 ⇒ g^K PosDef (curvedRNCMetric_posDef) ⇒ det g^K>0 (curvedRNCMetric_det_pos =
-- curvedRNCMetric_hgpos), the exact ∀v,0<det(g v) capstone binder. K<0 genuinely curved (Ric≠0). Completes the
-- geometric-gauge half; ANALYTIC heat-kernel Gaussian dominations REMAIN. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.CurvedRNCPosDef
-- J4-527 (CurvedRNCWitnessMeas): the type-(iii) hWmeas/hWslice binders of a1_R6_from_labelled_curved_boundary,
-- INSTANTIATED for the genuinely curved witness g^K=curvedRNCMetric K (K<0). Inner order-1 parametrix slice
-- discharged END-TO-END from the curved smoothness bundle (curvedRNCMetric_contDiff/curvedRNCInv_contDiff/
-- curvedRNCMetric_hgpos) at ∞ via vanVleck_witnessInner_continuous_ofGeom (no ω), composed with the base chart;
-- fed with compactGate_measurableSet through the generic vanVleckGatedWitness_slice_aestronglyMeasurable.
-- hWmeas/hWslice reduced to two curvature-independent carries {hSm, hVmap}. NOT a₁=R/6 (CONDITIONAL, flat-only). std-3.
import QIQTH.CurvedRNCWitnessMeas
import QIQTH.CurvedRNCWitnessMeasSC
import QIQTH.CurvedRNCChartReach
import QIQTH.CurvedRNCVanVleckBound
import QIQTH.CurvedRNCBaseWitnessDom
import QIQTH.CurvedRNCModuliBound
import QIQTH.CurvedRNCPhaseTransfer
import QIQTH.CurvedRNCBaseWitnessDomCollar
import QIQTH.CurvedRNCBaseWitnessDomAdom
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.CurvedRNCHeatOpDom2
-- J4-539 (DaLimLUCapped): the LEG-1 LO-CAPPED integrability sub-assembly
-- integrability_from_dominations_capped — leg-1 mirror of leg-2's memLapFull_from_pairing_dominations.
-- Replaces integrability_from_dominations' FALSE uncapped hAdom2 with {per-m capped hAdom2cap} (LO leg
-- built via CappedAdom2Audit.hII_lo_from_capped) + {carried hII_hi : MemAdjHi residual}; strips stay on
-- uncapped hAdomHeat (heat operator, no τ⁻¹ blow-up). Drop-in for the eventual capped capstone. Sol-
-- confirmed leg-1 factors identically to leg-2 through the pairing LO/HI split. NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.DaLimLUCapped
-- J4-540 (DaLimLUCappedStep2): leg-1 LO-CAPPED MemLapFull splice — routes J4-539's
-- integrability_from_dominations_capped into its immediate downstream consumer
-- GlobalRawBoundFacade.memLapFull_from_labelled, producing MemLapFull with NO uncapped hAdom2 on the
-- path (LO leg capped-built, HI leg MemAdjHi carried, strip legs discarded). NOT a₁=R/6 (CONDITIONAL). std-3.
import QIQTH.DaLimLUCappedStep2
-- J4-541 (DaLimLUCappedStep3): leg-1 LO-CAPPED capstone hDaLimLU_from_labelled_capped — reproduces the
-- whole DaLimLUGoal Da-limit assembly (GlobalRawBoundFacade.hDaLimLU_from_labelled) with the FALSE
-- uncapped whole-time hAdom2 PURGED: step-(v) census swapped to integrability_from_dominations_capped
-- (per-m hAdom2cap + carried MemAdjHi residual), hmeas2Hi dropped, every other binder + downstream
-- discharge (incl. final hDaLimLU_concrete) identical. Confirms leg-1 has NO second clean-hAdom2 site.
-- NOT a₁=R/6 (CONDITIONAL, effectively FLAT-ONLY). std-3.
import QIQTH.DaLimLUCappedStep3
-- J4-542: leg-1 LO-capped capstone with the carried MemAdjHi HI-leg residual DISCHARGED via the banked
-- MemAdjHiSliver.hII_hi_from_sliver (moment-aware τ^{-1/2} carry). NOT a₁=R/6. std-3.
import QIQTH.DaLimLUMemAdjHi

-- J4-543: CONSTRUCTING the τ^{-1/2} moment-cancellation carry hGpow from the concrete amplitude data bundle
-- (slice2_inner_bound = exposed per-slice hinner of sliver2_bound; hGpow_of_amplitudeData = the capstone). NOT a₁=R/6. std-3.
import QIQTH.MemAdjHiMomentBound

-- J4-544: DISCHARGE hEndpoint/hAzero for the concrete van-Vleck witness + wire the hGpow capstone with hEndpoint removed.
-- vanVleckGatedWitness_eq_zero_of_nonpos (concrete witness =0 at τ≤0, discharges the abstract hAzero carry),
-- witnessSecondXDeriv_endpoint_zero (standalone τ=0), hEndpoint_discharged (exact binder shape, unconditional n≥1),
-- hGpow_of_amplitudeData_noEndpoint (hGpow_of_amplitudeData with hEndpoint supplied internally). PART B (hD2Hexpand
-- curved carry) SCOPED not closed = amplitudeData_concrete_residual. NOT a₁=R/6 (still FLAT-ONLY/CONDITIONAL). std-3.
import QIQTH.AmplitudeDerivativeDataConcrete
-- J4-545: factor the hGpow closure into a ROUTE-AGNOSTIC boundary hGpow_from_innerWindow (from ANY per-slice
-- open-window inner bound in the K₁(u−s)^{-1/2}+K₀ shape + 1≤n, produce the uIoc hGpow via leviSecondPairing_le_invSqrt
-- ∘ hGpow_uIoc_of_Ioo_zeroEndpoint, τ=0 endpoint supplied internally from hEndpoint_discharged). Collar bundle CANNOT
-- feed slice2_inner_bound (all-z full-space Hessian moment; collar shrinks with τ) — genuine gap SCOPED as
-- collar_hGpow_residual (hOnCollar BANKED via amplitudeDataOn_concrete + hjets; hOffCollarTail = corrected off-collar
-- tail, the surviving curved carry). NOT a₁=R/6 (still FLAT-ONLY/CONDITIONAL). std-3.
import QIQTH.HGpowFromCollar
-- J4-546: make the leg-1 HI-leg hOffCollarTail a CONCRETE exponentially-suppressed Gaussian-tail moment integral
-- (the sharp poly·e^{−c²/8} refinement DEFERRED by SliverTailMatched.tailMoment_bound). gaussDdim_tail_le_scaled =
-- pointwise G_τ(z) ≤ (√2)ⁿ·e^{−R²/8τ}·G_{2τ}(z) on ‖z‖>R (banked width-split gaussDdim_eq_wide_mul +
-- gaussDdimWide_eq_scaled_gaussDdim + norm_sq_le_rncRadialSq). tailMoment_expSuppressed_bound = |tailMoment i τ R| ≤
-- (√2)ⁿ·e^{−R²/8τ}·(2n+1)/(2τ); collar R=c√τ ⟹ tailMoment_collar_expSuppressed = (√2)ⁿ·e^{−c²/8}·(2n+1)/(2τ). Still
-- O(τ⁻¹) for fixed c (matched-pair sliver_term1_on_collar_matched is the real O(τ^{−1/2}) closure); NOT a₁=R/6. std-3.
import QIQTH.OffCollarTailMoment

import QIQTH.Leg2HLapFull

import QIQTH.CurvedA1Assembled

import QIQTH.CurvedA1FullyWired

import QIQTH.CurvedA1Leg2Core

import QIQTH.CurvedA1FullyWiredCapstone

import QIQTH.CurvedA1ClassB

import QIQTH.CurvedA1MemAdjHiWired

import QIQTH.CurvedA1AmplitudeData

import QIQTH.CurvedChartJets

import QIQTH.CurvedCenterIdentities

import QIQTH.CurvedChartJetsCollar

import QIQTH.CurvedA1ClassBMeas
import QIQTH.CurvedA1ClassBMeas2
import QIQTH.CurvedA1GateS1
import QIQTH.CurvedA1ClassBMeas3
import QIQTH.CurvedA1ClassBMeas4
import QIQTH.CurvedA1ClassBMeas5
import QIQTH.CurvedA1ClassBMeas6
import QIQTH.CurvedA1ClassBMeas7
import QIQTH.CurvedA1ClassBMeas8
import QIQTH.CurvedA1ClassBFint

import QIQTH.CurvedA1FintAdomSource

import QIQTH.CurvedA1FintDAdomSource

import QIQTH.CurvedA1FintHcrudeSource

import QIQTH.CurvedA1FintHFarSource

import QIQTH.CurvedA1FintHFirstEnvSource

import QIQTH.CurvedA1FintHlam4

import QIQTH.CurvedA1FintHdata

import QIQTH.CurvedA1FintHdataUniform

import QIQTH.CurvedA1FintHdataDerivCont

import QIQTH.CurvedA1FintHdataReg

import QIQTH.CurvedA1FintHdataJet

import QIQTH.CurvedA1FintHdataBundle

import QIQTH.CurvedA1FintHFarCoercivity

import QIQTH.CurvedA1FarConsumeCheck

import QIQTH.CurvedA1FrameAudit

import QIQTH.CurvedA1CenterGauge

-- J4-585 (DaLimLUCappedStep3Center): CENTER-GAUGE VARIANT of the leg-1 LO-CAPPED capstone
-- hDaLimLU_from_labelled_capped — the two geometry binders {hK0, hframeK} REPLACED by the single
-- center-only value gauge hg0 : g(0)=δ, gauge line routed through DaLimCurvedGauge.gauge_from_pointwise
-- (curved-compatible drop-in) instead of gauge_from_geometry. SAME DaLimLUGoal conclusion (not weakened);
-- hg0 curved-satisfiable via curvedRNCMetric_zero (no K={0} collapse), so J4-582 vacuity removed.
-- Step 1 of the certified center-only-gauge rethread. NOT a₁=R/6 (still FLAT-ONLY until capstone lands). std-3.
import QIQTH.DaLimLUCappedStep3Center

-- J4-586 (Leg2HLapFullCenter): CENTER-GAUGE VARIANT of the curved leg-2 external hLapFull producer
-- Leg2HLapFull.curved_leg2_hLapFull — the two geometry binders {hK0, hframeK} REPLACED by the single
-- center-only value gauge hg0 : g(0)=δ, gauge line routed through DaLimCurvedGauge.gauge_from_pointwise
-- (curved-compatible drop-in) instead of gauge_from_geometry. SAME MemLapFull conclusion (not weakened);
-- hg0 curved-satisfiable via curvedRNCMetric_zero (no K={0} collapse), so J4-582 vacuity removed. Leg-2
-- body is a thin assembly (like leg-1) — a proof copy with the ONE gauge-line swap, no census re-elaboration.
-- Step 2 of the certified center-only-gauge rethread. NOT a₁=R/6 (still FLAT-ONLY until capstone lands). std-3.
import QIQTH.Leg2HLapFullCenter

-- J4-587 (CurvedA1FullyWiredCenter): THE CULMINATING curved-capstone rethread — the CENTER-GAUGE variant
-- chain up to curved_a1_R6_fully_wired_center, making the curved a₁=R/6 capstone NON-VACUOUS. Threads the
-- center gauge UP: curved_hDa_at_gate_center (LEG 1), curved_core_at_gate_center (LEG 2, both gauge sites
-- swapped gauge_from_geometry→gauge_from_pointwise + curved_leg2_hLapFull→_center), and the full capstone
-- curved_a1_R6_fully_wired_center (hframeK→hg0, hK0 KEPT for geomWired, reusing curved_a1_R6_geomWired
-- UNCHANGED). curved_a1_R6_center_nonvacuous = THE VACUITY GUARD: the weakened capstone's antecedent bundle
-- {hg0, 0∈K, ∃q≠0∈K, gauge members, Ric(0)≠0, ¬hframeK} is JOINTLY SATISFIABLE at a genuinely-curved
-- witness on a GENUINE K (closed unit ball, not the J4-582 {0}) — anti-J4-582 for the REAL capstone.
-- Every variant conclusion = the original a₁ R/6 two-jet; hg0 discharged by curvedRNCMetric_zero; no
-- hframeK/K={0} collapse. ⚠ hmassone STILL a carried analytic input — the guard removes the STRUCTURAL
-- obstruction, not hmassone. std-3 all. NOT a₁=R/6 (conditional on the carried residuals incl. hmassone).
import QIQTH.CurvedA1FullyWiredCenter
-- J4-588: hmassone (curved base-mass ∫z→1) ASSESSED + REDUCED — the first genuinely-analytic wall on the
-- curved a₁=R/6 side. VERDICT: DEEP-CARRIED analytic input (like hsrc) with a THIN reduction, NOT a banked
-- Gaussian mass fact. curved_hmassone_at_gate = the f≡1 case of the banked conditional W1 capstone
-- chartImage_approx_identity_conditional + epsSeq→𝓝[>]0, producing the EXACT curved capstone hmassone shape
-- MODULO the UNBANKED base-varying CoV bundle (M1–M4 for Wbv, the MISSING brick) + Layer-C moving facts.
-- curved_hmassone_gate_forces_nontrivial_K = non-vacuity guard (ρ>0 ⟹ K≠{0}, anti-J4-582). std-3 both.
-- NOT a₁=R/6 (still CONDITIONAL on the carried residuals incl. hmassone).
import QIQTH.CurvedA1Hmassone
-- J4-589: the mass-side endgame — base-varying CoV bundle M1–M4 for the curved Wbv + reduced hmassone.
-- ⚠ DON'T-UNDERCREDIT: J4-588's "MISSING brick" (the Wbv M1–M4 bundle) was ALREADY built UNCONDITIONALLY +
-- metric-generic (J4-274 baseVaryingIFTPackage_unconditional; J3 base-slot blocker via terminal-velocity).
-- curved_Wbv_CoV_bundle_at_gate = the FULL M1–M4 bundle for g^K (instantiation, UNCONDITIONAL given K∈𝓝0).
-- curved_Wbv_hasFDeriv_center_at_gate = near-identity anchor (DWbv(0)=-id, non-vacuous).
-- curved_hmassone_via_v2_at_gate = curved hmassone with M1–M4+hΩmeas+hΩnhds+hmeas discharged (f≡1 case of
-- chartImage_approx_identity_v2 ∘ epsSeq→𝓝[>]0); carried surface 12→4 (hGgate/hSupp/hbound/hlocal). std-3 all.
-- NOT a₁=R/6 (hmassone still carried MODULO the FOUR residuals; hbound/hlocal need enriched bundle).
import QIQTH.CurvedA1WbvCoV
-- J4-590: sheds hmassone's hbound/hlocal carriers via the EnrichedChartBundle. curved_hmassone_via_bundle_at_gate
-- = the curved hmassone as the f≡1 case of EnrichedChartBundle.chartImage_approx_identity_v3 (M1–M4 + hΩmeas +
-- hΩnhds + hmeas + hbound + hlocal ALL discharged) ∘ epsSeq→𝓝[>]0; carried surface 4→2 (only hGgate/hSupp).
-- curvedRNCMetric_det_center (det g^K 0 = 1) + curved_hmassoneBound_satisfiable (κ<0 non-vacuity: gauge holds
-- while ∃w, 1<det g^K w). std-3 all. NOT a₁=R/6 (hmassone still carried MODULO hGgate/hSupp; capstone CONDITIONAL).
import QIQTH.CurvedA1HmassoneBound
-- J4-591: sheds hmassone's LAST ρ-gate carriers hGgate/hSupp via the banked GateAnnulusSplit.chartImage_approx_
-- identity_final. curved_hmassone_final_at_gate = the curved hmassone (exact capstone shape) with hGgate/hSupp
-- DISCHARGED (f≡1 case ∘ epsSeq→𝓝[>]0); the two ρ-DEPENDENT carriers removed, replaced by the satisfiable pre-ρ
-- carriers {rS,hKball,hSact,hWslice,hDom}. curved_hmassone_final_curved_satisfiable = κ<0 non-vacuity. std-3.
-- NOT a₁=R/6 (hmassone now unconditional-in-ρ MODULO the four satisfiable pre-ρ carriers; capstone CONDITIONAL).
import QIQTH.CurvedA1HmassoneFinal
-- J4-592: drains the hInnerCont carrier of the curved capstone. curved_hInnerCont_at_gate = the EXACT
-- hInnerCont binder (interior-time ContinuousOn of the inner W·L pairing on Ioo 0 u) at g^K, as the g:=g^K
-- specialization of the banked std-3 engine InnerMeasFubini.hInnerCont_concrete — reducing hInnerCont to the
-- honest per-interior-point dominated-continuity datum hContDom for g^K (local Gaussian dominator + local
-- ae-strong-meas + local ae-domination + ae-z time ContinuousAt), genuinely TRUE on the OPEN Ioo 0 u (both s
-- and u−s strictly positive ⟹ no τ→0 degeneracy). curved_hInnerCont_satisfiable = κ<0,n≥2 non-vacuity
-- (∃w,1<det g^K w: NOT flat). std-3 both. NOT a₁=R/6 (capstone still owes hContDom + the other residuals).
import QIQTH.CurvedA1HInnerCont
-- J4-593: hOffCollarTail carrier of the curved a₁=R/6 capstone DISCHARGED (generic in the amplitude).
-- KEY: the off-collar tail's leading integrand hessGaussFactor is the FLAT heat-kernel Hessian —
-- metric-independent — so the reconstitution is banked & generic in the Lipschitz amplitude q. Delivers
-- the matched √τ-gain reconstitution (sliver_term1_on_collar_matched) + exp-suppressed bare tail
-- (tailMoment_collar_expSuppressed, J4-546). Satisfiable at κ<0,1≤n with a non-constant 1-Lipschitz
-- amplitude. std-3. NOT a₁=R/6 (capstone still owes the other residuals; curved input = ON-collar hjets).
import QIQTH.CurvedA1HOffCollarTail
-- J4-594 (CurvedA1Hsrc): drains the hsrc carrier (Seeley–DeWitt transport-source C^∞ smoothness) of the
-- center-gauge curved a₁=R/6 capstone. hsrc = ContDiff ℝ ∞ (transportOp Θ g^K gi^K (transportCoeff T 0)).
-- KEY: transportCoeff T 0 = (fun _ => 1) (u₀≡1), so hsrc is ONE transport-source application to the CONSTANT
-- base coefficient — no ray-integral solve, hence NO analytic wall. Discharged via banked
-- transportOp_preserves_contDiff (J4-174 Part A) + curved carries {curvedRNCMetric_contDiff,
-- curvedRNCInv_contDiff (κ≤0), curvedRNCMetric_hgpos (κ≤0)}, at ⊤ then .of_le le_top to ∞. std-3.
-- NOT a₁=R/6 (capstone still owes census/domination/convergence-trio/hmassone-pre-ρ/hContDom/on-collar hjets).
import QIQTH.CurvedA1Hsrc
-- J4-595 (CurvedA1Hjets): discharges/assesses the ON-COLLAR hjets chart-jet bundle (AmpGeometryBundle.HjetsShape)
-- for g^K — the genuine curved input the capstone's amplitude carriers (hOffCollarTail/hInnerCont) lean on.
-- Assembler curved_hjets_bundle_of_pullback = HjetsShape from jets + geodesic pullback bridge (J4-554 ⊕ J4-555,
-- three centre identities discharged via the two EXACT radial gauges); curved_hjets_secondJet_banked = the Q/hP1
-- field banked from centre-C² (chartField_secondJet_of_contDiffAt); curved_hjets_bundle_from_banked_secondJet =
-- FULL bundle with second jet discharged internally, residual = {global ∀x first jet, global amp C¹, amp pd-pd@0,
-- pullback bridge}. curved_hjets_bundle_satisfiable = NON-FLAT (both radial gauges hold ∧ g^K≠δ off-diagonal, κ<0).
-- All std-3. NOT a₁=R/6 (capstone still owes census/domination/convergence-trio/hmassone-pre-ρ/hContDom).
import QIQTH.CurvedA1Hjets
-- J4-596 (CurvedA1HContDom): drains the hContDom carrier that J4-592's hInnerCont reduction carries, for the
-- center-gauge curved a₁=R/6 capstone at g^K. hContDom = per-interior-point dominated-continuity datum for the
-- space-time slice W(u−s)0z·L s z 0. KEY: banked generic builder ContDomWindow.hContDom_discharged produces the
-- EXACT hContDom shape from {hAdom (D1 witness dom, width 3/2), hBdom (width-2 Levi dom), hmeas, hcont},
-- CONSTRUCTING the analytic conjuncts (integrable dominator + window norm bound) internally. curved_hContDom_at_gate
-- = EXACT hContDom binder specialized to g^K (analytic half discharged → {hAdom,hBdom,hmeas,hcont}).
-- curved_hInnerCont_of_dominations = composed reduction into J4-592 (removes opaque ContinuousOn AND hContDom
-- existential). curved_hContDom_satisfiable = NON-FLAT (κ<0,n≥2). RESIDUAL: hAdom banked only frozen-p=0/windowed
-- (curvedRNC_baseWitness_dom), hBdom = D2/convergence-trio frontier → hContDom NOT fully closed. std-3.
-- NOT a₁=R/6 (capstone still owes {hAdom,hBdom,hmeas,hcont} + census/domination/convergence-trio/hmassone-pre-ρ/hjets).
import QIQTH.CurvedA1HContDom
-- J4-597 (CurvedA1HBdom): discharges (modulo the SINGLE M1 carry hEmeas) hBdom — the width-2 Levi-series
-- Gaussian domination for g^K (κ<0), the D2/convergence-trio frontier flagged "NOT attempted" by
-- ConcreteDominations. Route (banked, at the pkg's ∃ gate params): curvedRNC_heatOp_dom_pkg (clean uncapped
-- width-2 defect bound) → iterConvIntegrableW_of_locally_bound_baseMeas (hEzero banked, 1≤n) →
-- leviSeries_dominatedW_le (width stays EXACTLY 2 at every iterate; C_L = Σ' C^(k+1)·modelCoeff finite) →
-- baseKernelW_zero_apply ⟹ EXACT hBdom binder |leviSeries(heatOp g^K gi^K W)| ≤ C_L·gaussDdim(2s)(z−y) on
-- (0,T]. curved_hInnerCont_of_pkg = consumption certificate: hBdom slot of the J4-596 builder CLOSED —
-- hInnerCont now owes {hEmeas, hAdom, hmeas, hcont}. curved_hBdom_satisfiable = NON-FLAT (κ<0,n≥2). std-3.
-- NOT a₁=R/6 (still owes hEmeas M1 wall + hAdom global + hmeas/hcont + piles/trio/hmassone-pre-ρ/hjets).
import QIQTH.CurvedA1HBdom
-- J4-598 (CurvedA1HEmeas): the hEmeas M1-wall carry of J4-597 ASSESSED + measurability content CLOSED for
-- g^K (kappa<0): curved_hEmeas_at_gate = the EXACT joint StronglyMeasurable hEmeas binder at ANY gate params
-- 0<a<b<c, modulo the jet reach c<delta0 (from banked curved_hS1_at_gate J4-561; tripleHEmeas defeq binder;
-- Route B continuity-free, measurable ACROSS the tau<=0 gate boundary, no strip caveat). curved_hBdom_of_reach /
-- curved_hInnerCont_of_reach = J4-597's hBdom / ladder consumption with the M1 measurability carry REPLACED by
-- the pure ARITHMETIC reach residual c<delta0 (FLAGGED OPEN at the pkg's own existential c: the pkg's c=(b+rhoc)/2
-- and the Gc jet reach delta0(a,b) are independent exists-chains, alignment not banked). curved_hEmeas_satisfiable
-- = witness genuinely curved. std-3. NOT a1=R/6 (owes reach alignment + hAdom + hmeas/hcont + piles/trio/
-- hmassone-pre-rho/hjets).
import QIQTH.CurvedA1HEmeas
-- J4-599 (ReachRequant + CurvedA1ReachAlign): THE REACH ALIGNMENT. Part 1: the S1/tripleHEmeas jet reach
-- delta0 REQUANTIFIED BEFORE (a,b) (honest exists-forall swap; audited: every supplier radius is (a,b)-free
-- geometry; 13 hoisted replays, capstone tripleHEmeas_flowball_requant). Part 2: the J4-316 CONST producer +
-- J4-536 curved pkg replayed with a PRESCRIBED radius ceiling eps (c=(b+rhoc)/2<eps); eps:=delta0(jet) aligns
-- the two exists-chains ==> curved_hBdom_unconditional (NO reach antecedent, NO hEmeas antecedent; only
-- mainline {hChr,hw,hu} carried) + curved_hInnerCont_of_meas (capstone hInnerCont reduced to {hAdom,hmeas,
-- hcont} ONLY). Gate genuinely inhabited; witness genuinely curved. std-3. NOT a1=R/6 (owes hAdom global +
-- hmeas + hcont + piles/trio/hmassone-pre-rho/hjets).
import QIQTH.ReachRequant
import QIQTH.CurvedA1ReachAlign
-- J4-600 (CurvedA1HAdom): hAdom DISCHARGED — the global all-(p,q) D1 witness Gaussian domination for
-- g^K=curvedRNCMetric kappa (kappa<0), produced JOINTLY with hBdom at ONE gate-parameter set:
-- curved_hAdom_hBdom_at_gate = prescribe the J4-599 pkg ceiling eps := min deltajet (min r1 (delta0/2)) so
-- the pkg's own radius c clears BOTH the hEmeas jet reach (==> hBdom, verbatim J4-599 assembly) AND the
-- GateSqControl radii (==> hAdom via banked gateSqControl_of_flowBall + exists_D1_constants_of_gateSqControl
-- at the pkg's own (a,b)). curved_hInnerCont_of_two = the consumption certificate: capstone hInnerCont
-- reduced to {hmeas, hcont} ONLY (hAdom/hBdom/hEmeas slots ALL internally discharged). Witness genuinely
-- curved. std-3. NOT a1=R/6 (owes hmeas + hcont + piles/trio/hmassone-pre-rho/hjets + {hChr,hw,hu}).
import QIQTH.CurvedA1HAdom
-- J4-601 (CurvedA1Hmeas): hmeas AND hcont both discharged CARRY-FREE, hInnerCont CLOSED
-- (curved_hInnerCont_closed) — PLUS the adversarial DEGENERACY PIN curved_innerPairing_zero: the J4-592+
-- chain hard-codes hK := isCompact_singleton {0}, the gate kills every source z ≠ 0, so the z-integrand is
-- a.e. 0 and the inner pairing is IDENTICALLY 0 — the closed hInnerCont is continuity of the constant-0
-- function (same K={0} source-collapse family as cp466 / CurvedA1FarConsumeCheck). Genuine analytic
-- hInnerCont content lives only at a NON-collapsed base compact. std-3 all 7. NOT a1=R/6.
import QIQTH.CurvedA1Hmeas
-- J4-602 (CurvedA1ReBase): (A) the K={0} DEGENERACY AUDIT sharpened to PROVED collapse lemmas — at the
-- singleton pin the defect kernel E dies at every source q≠0, ALL Levi iterates >=2 vanish, and
-- leviSeries = -E LITERALLY (singleton_leviSeries_eq_negE): the J4-597/599 hBdom bounds ONE first-order
-- defect term (y=0 slice; constant-0 off it), NOT a series. Capstone binder verdict: the capstone is
-- GENERAL-K (hK0 only); J4-592/596 engines are general-K; the {0} pin enters at J4-597 and makes
-- J4-597..601 degenerate INSTANTIATIONS, inconsistent with J4-591's mass-side hKball (ball 0 rS ⊆ K).
-- (B) RE-BASE START at K := Metric.closedBall 0 r (r>0): co-instantiation certificates (ball ⊆ K,
-- positive measure), gate-open-on-ball, and rebased_hmeas_at_gate = the FIRST re-based hInnerCont
-- carrier (witness-slice reach supplier × Levi-slice supplier, prescribed-ceiling production shape),
-- conditional on {geometric reach, hLcont}. std-3 all 12. NOT a1=R/6 — the honest residual EXPANDS:
-- re-based hcont/hAdom/hBdom/hContDom + co-instantiated capstone application are OWED.
import QIQTH.CurvedA1ReBase
-- J4-603 (CurvedA1ReBaseHBdom): the re-based hBdom at the fat base compact K=closedBall 0 r — VERDICT +
-- engine + scoping. VERDICT (rebased_hframeK_unsat, PROVED): the banked CONST defect-bound producer chain
-- (gatedWitnessN1_hEboundW_le_lin_CONST -> curvedRNC_heatOp_dom_pkg) is K-parametric in FORM but its
-- hframeK (delta-frame at EVERY q in K, load-bearing through the amplitude chain) PROVABLY FAILS at the
-- curved witness on the fat ball — the J4-597 route does NOT re-instantiate; the missing (hbound-fat)
-- producer = center-only-gauge amplitude rework, scoped OPEN. LANDED: gated_hBdom_of_defect_bound = the
-- FULL J4-597 Neumann-tail route factored GENERAL-(g,K,S) (hEzero -> hInt -> D2 engine -> width-2 clean,
-- antecedent inhabited at the banked {0} pkg); rebased_hBdom_of_defect_bound = its fat-K curved
-- instantiation (EXACT J4-596 hBdom binder shape, conditional on {hEmeas, hbound-fat});
-- rebased_hInnerCont_of_dominations = fat-K consumption certificate into the general-K builder;
-- rebased_no_offOrigin_kill + rebased_hBdom_noncollapse = structural non-collapse (nonzero source with
-- OPEN gate + positive base measure: the series is NOT -E by the J4-602 mechanism). std-3 all 9.
-- NOT a1=R/6: (hbound-fat) producer, fat-K hEmeas/hAdom/hcont, capstone co-instantiation remain OWED.
import QIQTH.CurvedA1ReBaseHBdom
-- J4-604 (CurvedA1CenterAmp): FIRST layer of the (hbound-fat) wall — center-only-gauge variant of the
-- uniform-flow pullback-metric deviation bound. USE-SITE VERDICT (by construction): in the banked
-- uniformFlowPullbackMetricInv_dev_uniform, hframeK is INITIAL-CONDITION-ONLY (sole entry = value jet
-- g~(0)=g(q) via expPullbackMetric_at_zero; the pd-jet, the uniform C2 packet, and the uniform inverse
-- bound are all frame-free). Center-gauge replay replaces hframeK by hdevK (|g(q)-delta| <= eps0 on K)
-- and pays EXACTLY +eps0: forward |g~(v)-delta| <= M*|v|^2+eps0, inverse |g~inv(v)-delta| <=
-- M*(rncRadialSq v+eps0), with r0/M produced BEFORE eps0 (M independent of eps0). Supplier:
-- curvedRNC_frame_dev_pointwise/_on_ball = |g^k(q)-delta| <= (|k|/3)*rncRadialSq q <= (|k|/3)*n*r^2 on
-- closedBall 0 r (honest, entrywise from the closed form). FAT-K CURVED INSTANTIATION:
-- curvedRNC_pullbackInv_dev_uniform_center (k<=0, all carries discharged: curvedRNCMetric_contDiff /
-- hgnd_of_hgpos+curvedRNCMetric_hgpos / curvedRNCMetric_symm / curvedRNCMetric_hinvF / curvedRNC_hChr).
-- NON-VACUITY: curvedRNC_center_gauge_satisfiable (fat K has nonzero point AND hdevK holds) +
-- curvedRNC_center_eps_arbitrarily_small (eps0 -> 0 with r). std-3 all 10. NOT a1=R/6: remaining
-- (hbound-fat) layers = center-gauge Christoffel decay, uniformCoeff bounds, tau-narrow residuals,
-- producer re-assembly; plus fat-K hEmeas/hAdom/hcont + capstone co-instantiation.
import QIQTH.CurvedA1CenterAmp
-- J4-605 (CurvedA1CenterChr): SECOND layer of the (hbound-fat) wall — center-gauge variant of the
-- load-bearing Christoffel linear decay. USE-SITE VERDICT (by construction): in the banked
-- uniformFlowChristoffel_linear_decay, hframeK enters through EXACTLY ONE inner call — the R1 pd-decay
-- layer, which consumes only the pd-jet component of uniformFlowPullbackMetric_jet_zero (value jet
-- discarded); the inverse entry bound never takes hframeK. Since the pd-jet is frame-free (J4-604's
-- uniformFlowPullbackMetric_pd_zero_center, RNC radiality), the center-gauge decay survives with the
-- form UNCHANGED and NO eps0 term at all: |Chr(v)| <= KdG*|v|, KdG = (1/2)*n*Kg*3*Kpd — hframeK is
-- REMOVED, not weakened. Landed: uniformFlowPullbackMetric_pd_linear_decay_center (R1 frame-free),
-- uniformFlowChristoffel_zero_at_zero_center (Chr(0)=0 frame-free, feeds layer 3),
-- uniformFlowChristoffel_linear_decay_center (THE BRICK), curvedRNC_Chr_linear_decay_center (fat-K
-- curved instantiation, k<=0, all carries from banked curved lemmas), curvedRNC_Chr_center_satisfiable
-- (non-vacuity: fat K nonzero point + conclusion inhabited; no hdevK/eps0 antecedent remains to gate).
-- std-3 all 5. NOT a1=R/6: remaining (hbound-fat) layers = center-gauge uniformCoeff bounds (eps0 from
-- layer 1 WILL surface there), tau-narrow residuals, producer re-assembly; plus fat-K
-- hEmeas/hAdom/hcont + capstone co-instantiation.
import QIQTH.CurvedA1CenterChr
-- J4-606 (CurvedA1CenterCoeff): THIRD layer of the (hbound-fat) wall — center-gauge uniformCoeff_bound /
-- uniformCoeffLinear_bound. hframeK's two use-sites: hdev (layer-1 center, pays Md*(rncRadialSq+eps0) at
-- the (A1) trace AND the (TC) coeffDevF entries) and hChb (layer-2 center, FREE); the entry bound (Kg)
-- and heat-side EVT blocks never took hframeK. Honest degraded form
-- |totalRadialO1_coeff| <= C_c*rncRadialSq v + C_eps*eps0 (Linear: *rncRadial v) with a REAL 0th-order
-- floor C_eps*eps0 (does NOT vanish as v->0); C_c literally the banked constant; rho_c/C_c/C_eps all
-- produced BEFORE eps0 (no eps0-inflation). Landed: uniformCoeff_bound_center (THE BRICK),
-- uniformCoeffLinear_bound_center (no-flatness branch for the shifted van-Vleck profile),
-- curvedRNC_coeff_bound_center / curvedRNC_coeffLinear_bound_center (fat-K curved instantiations,
-- k<=0, explicit eps0=(|k|/3)*n*r^2, supplier curvedRNC_frame_dev_on_ball),
-- curvedRNC_coeff_center_satisfiable (non-vacuity: fat K nonzero point + heat-side antecedents
-- INHABITED (Theta=1,u=1 => foldedCoeff=1, smooth+center-flat) + hdevK holds at the curved witness).
-- std-3 all 5. NOT a1=R/6: remaining (hbound-fat) layers = center-gauge tau-narrow residuals (the
-- C_eps*eps0 term enters the T1 slot as a (1/tau)-weighted constant coefficient — layer 4 must track
-- it, not drop it), producer re-assembly; plus fat-K hEmeas/hAdom/hcont + capstone co-instantiation.
import QIQTH.CurvedA1CenterCoeff
-- J4-607 (CurvedA1CenterResid): FOURTH layer of the (hbound-fat) wall — center-gauge tau-narrow
-- N=0 residual engines. FINDING: hframeK entered the banked engines at TWO sites — (T1) via the
-- explicit hCoeffU/hCoeffLin hypothesis AND (T2) DIRECTLY via uniformFlowPullbackMetricInv_dev_uniform
-- feeding the quadratic term; the center substitution pays eps0 TWICE. Honest output:
-- |R0| <= (C0 + Ceu*eps0*(1/tau))*G_{3/2} (O(r^2)) resp. (C0 + C1*(sqrt(tau)/tau) + Ceu*eps0*(1/tau))*G
-- (O(r)), Ceu = sqrt(3/2)^n*(C_eps + 3n^2*M*W); constants before eps0; the eps0/tau term is
-- irreducible (a constant coefficient cannot be width-folded: at v=0 all Gaussians are 1, 1/tau
-- diverges). Landed: residualQuadratic_pointwise_narrow_center, the two _center engines, fat-K curved
-- instantiations curvedRNC_resid(Linear)_bound_center (eps0=(|k|/3)*n*r^2, coeff antecedent
-- DISCHARGED from layer 3), gate curvedRNC_resid_center_satisfiable. Layer-5 tension SCOPED: the
-- tau*R0[u'] branch folds eps0/tau benignly (tau*(1/tau)=1) but the R0[u] branch keeps raw eps0/tau
-- => N=1 shape (B0+B1*tau+Be*eps0/tau)*G; integral of 1/tau diverges at fixed eps0, so layer 5 needs
-- an eps0-dependent tau-threshold OR the eps0->0 (shrink r) limit BEFORE tau-integration. std-3 all
-- 6. NOT a1=R/6: curved re-base still owes layer 5 (producer re-assembly) + fat-K hEmeas/hAdom/hcont
-- + capstone co-instantiation + piles/trio/hmassone-pre-rho/hjets.
import QIQTH.CurvedA1CenterResid
-- J4-608 (CurvedA1CenterN1): FIFTH-layer FIRST INCREMENT of the (hbound-fat) wall — the
-- center-gauge N=1 mixed residual engine + THE ORDER-OF-LIMITS ROUTE DECISION (Sol-confirmed).
-- uniformResidualN1_narrow_mixed_lin_center: honest N=1 shape
-- (B0 + B1*tau + (Bc + Bdelta*(1/tau))*eps0)*G_{3/2} — the tau*R0[u'] branch folds eps0/tau
-- BENIGNLY (kept explicit as Bc*eps0), the raw 1/tau survives only through R0[u].
-- curvedRNC_residN1_bound_center = fat-K curved instantiation, BOTH coeff antecedents discharged
-- from layer 3. ROUTE DECISION: (a) tau-threshold FAILS (iterE convolutions integrate down to 0
-- even at interior times; the J4-596 window restricts only the outer Duhamel variable) and
-- (b) eps0->0-first FAILS (sup eps0/tau = infinity at every fixed fat radius) — formal gates
-- centerShape_no_uniform_majorant / centerShape_no_width2_kernel_majorant; the forward route is
-- (c) per-q frozen-metric/vielbein Gaussian (kills the eps0 floor; linear normalization gives the
-- classical tau^(-1/2) Levi defect = alpha=-1/2-integrable; full alpha=0 needs per-q first-jet
-- cancellation or an alpha-generalized D2 consumer). Thresholded artifact recorded transparently;
-- non-vacuity gate curvedRNC_residN1_center_satisfiable. std-3 all 6. NOT a1=R/6 (flat tower
-- only; curved re-base still owes the per-q re-based producer + fat-K hEmeas/hAdom/hcont +
-- capstone co-instantiation + piles/trio/hmassone-pre-rho/hjets).
import QIQTH.CurvedA1CenterN1
-- J4-609 (FrozenGauss): SIXTH layer of the (hbound-fat) wall — the per-q FROZEN-SPD GAUSSIAN
-- (Sol's forward-route steps 1-3). frozenGauss A tau v = (sqrt(4*pi*tau))^-n * sqrt(det A) *
-- exp(-Q_A(v)/(4*tau)) (exponent carries the frozen METRIC A=g(q), operator carries the frozen
-- INVERSE B=g^-1(q); det to the PLUS 1/2 => Gamma_delta = gaussDdim and classical mass 1 — mass
-- NOTED not proved). frozenGauss_frozen_heat (THE BRICK) = the EXACT frozen heat cancellation
-- d_tau Gamma = sum_ij B^ij pd_i pd_j Gamma (all tau>0, all v; symmetric A, componentwise left
-- inverse B) — kills the J4-608 eps0/tau floor at order 0. frozenGauss_heatOp_zero = the SAME
-- cancellation through the repo's OWN heatOp/laplaceBeltrami (christoffel_const: frozen metric
-- => zero Christoffel) — the convention pin. frozenGauss_le_gauss / gauss_le_frozenGauss = the
-- two-sided ellipticity comparison with EXPLICIT constants (prefactors match EXACTLY; the
-- inequality lives in the exponent alone). Space form g^K (K<=0): eigenvalue bounds
-- |v|^2 <= Q <= (1+(-K/3)r^2)|v|^2 on |q|<=r (repo sign => g^K >= delta globally, NO smallness
-- condition on r), assembled comparison frozenGauss_comparison_spaceForm, cancellation at the
-- curved witness frozenGauss_frozen_heat_spaceForm (inverse discharged from banked hinvF).
-- NON-VACUITY: frozenGauss_matrix_ne_delta (K/=0, n>=2, q/=0 => frozen matrix NOT delta).
-- FrozenDefectBound = the O(tau^-1/2) Levi/Lipschitz defect J4-610 TARGET, a Prop ONLY (NOT
-- proved). std-3 all 18. NOT a1=R/6 (flat tower only; curved re-base still owes the defect
-- bound + alpha-fork + per-q producer re-assembly + fat-K hEmeas/hAdom/hcont + capstone
-- co-instantiation + piles/trio/hmassone-pre-rho/hjets).
import QIQTH.FrozenGauss
-- J4-610 (FrozenDefect): the tau^{-1/2} LEVI DEFECT BOUND — FrozenDefectBound n K r C 2
-- INHABITED (frozenDefectBound_spaceForm: for K<=0, r>=0, explicit C>0 with
-- |sum_ij (gi(q+v)-gi(q))*dd_ij Gamma_q| <= (C/sqrt tau)*G_{2tau}(v), 0<tau<=1, q in ball, ALL v).
-- Ingredients: curvedRNCInv_diff_bound (honest affine-in-(|v|,|v|^2) coefficient modulus from the
-- closed rational form, denominator >=1 for K<=0); entry/row/det bounds (det <= n!*M^n via
-- Matrix.det_le, M=1+(-K/3)r^2) + frozenGauss_pd_pd_abs_le; defect_scalar_fold (the tau^{-1/2}
-- bookkeeping, s*sqrt(tau) <= tau+s^2) + banked gaussDdim_absorb_zero/one/two at width lam=2.
-- NON-VACUITY: frozenDefect_witness_ne_zero (K<0, n>=2: defect sum >0 at q=0, v=unit vector).
-- GO/NO-GO certificates: width2_closed_fold (D2 width-2 CLOSED fold, G_{2t}*G_{2s}=G_{2(t+s)});
-- betaTime_negHalf_integral (alpha=-1/2 per-step Beta integral = pi; SERIES summability still
-- 0<=alpha — reported gap). std-3 all. NOT a1=R/6 (curved re-base still owes the alpha-fork
-- consumer generalization + per-q producer re-assembly + fat-K piles + capstone co-instantiation).
import QIQTH.FrozenDefect
-- J4-611 (AlphaLevi): alpha-generalization slice — Levi-series summability extended to alpha>-1
-- (gamma_ratio_tendsto_zero_general via Gamma log-convexity/Gautschi for beta<=1) + the
-- alpha-parametrized D2 consumer leviSeries_dominatedW_le_alpha (honest tau^alpha weight kept) +
-- alpha=-1/2 instantiation leviSeries_dominatedW_le_negHalf in the J4-610 frozen-defect shape
-- (C/sqrt(tau))*G_2tau. Series bound INHERITS tau^(-1/2) — no clean const*G claim. std-3.
-- NOT a1=R/6 (downstream consumer of the weighted series bound + producer re-assembly remain).
import QIQTH.AlphaLevi
-- J4-612 (FrozenWire): the frozen defect WIRED into the alpha=-1/2 Neumann engine —
-- frozenDefectKernel (gated two-point kernel, jointly measurable) + FULL-forall-tau
-- (C/sqrt tau)*G_2tau bound + the alpha>-1 per-step-integrability producer (Beta interval
-- integrability + alpha-agnostic replay of the alpha=0 producer, hInt DISCHARGED) +
-- frozenWire_leviSeries_dominated (the wired series bound on (0,1]) + witness non-vacuity.
-- FINAL-RATE AUDIT verdict (ii): diagonal hCorrHigher consumer needs the center-column alpha=0
-- sharpening — PROVED (frozenDefectCenterZero_spaceForm, clean C*G_2tau, all tau>0). std-3.
-- NOT a1=R/6 (per-q producer re-assembly + center-column splice + fat-K piles + capstone remain).
import QIQTH.FrozenWire
-- J4-613 (FrozenColumn): the center-column alpha=0 series splice — the mixed ladder
-- |iterE E (m+1) (s,.,0)| <= D_{m+1}*s^{m/2}*G_2s (clean alpha=0 inner seed, one alpha=-1/2
-- outer factor per level), the CLEAN column series bound <= C*G_2s on (0,1], and the HONEST
-- k>=2 tail = O(sqrt s)*G (NOT O(s)); frozen instantiation + column non-vacuity + budget
-- certificates (sqrt exceeds the linear slice budget; tail integrates to t^{3/2} = o(t)).
-- NOT a1=R/6 (consumer wiring across the sqrt(s)-vs-s gap + transport-cancellation remain).
import QIQTH.FrozenColumn
-- J4-614 (FrozenK2): the k=2 budget bridge, route (b) landed in full — sqrt-tolerant Duhamel
-- assembly (mixed K*((t-s)+s)+K'*sqrt(s) slice budget => K*t^2+K'*t^{3/2}), the o(t)-budget
-- consumer corrHigher_bounded_of_slice_sqrt (hCorrHigher equality shape kept; cRem=O(t^{-1/2})
-- NOT bounded) + the o(t)-sufficiency Tendsto certificates (correction/t -> 0: a1 unshifted),
-- the route-(a) half-moment absorb lever (|v|*G_tau <= C*sqrt(tau)*G_{lam*tau} + cubic), and
-- the frozen wiring: the k>=2 column tail fits the sqrt(s) budget and assembles to O(t^{3/2})
-- relative to the EXPLICIT diagonal mass G_{2t}(0). Sol: genuine E*E O(s) upgrade TRUE but
-- multi-brick (affine-difference supplier + refined center-column) — deferred. std-3 all.
-- NOT a1=R/6 (k=1 transport budget + E*E O(s) restoration + producer/capstone piles remain).
import QIQTH.FrozenK2
-- J4-615 (AffineDiff): the zero-constant-term affine-difference supplier — route-(a) brick (ii).
-- GLOBAL UNGATED structured bound |gi^K(z)-gi^K(w)| <= (2(-K)/3)*||z-w||*(||z||+||w||) for the
-- closed Sherman-Morrison inverse (K<=0; alpha>=1 everywhere + E-factor/alpha(w) cancellation),
-- same honest constant as the polynomial metric; + (q,v)-shape Levi corollary, summed n^2
-- compatibility form, nonzero witness (K<0, n>=2). Norm factors are sqrt(rncRadialSq .) —
-- the exact gaussDdim_moment_half shape the J4-616 refined E*E O(s) composition consumes.
-- NOT a1=R/6 (J4-616 E*E composition + k=1 transport + producer/capstone piles remain).
import QIQTH.AffineDiff
-- J4-616 (FrozenK2Sharp): the refined E*E center-column composition — the O(sqrt(s)) -> O(s)
-- UPGRADE. Sharpened two-term outer bound |E(a,z,w)| <= C_A*G_{2a} + C_B*|w|*a^{-1/2}*G_{2a}
-- (J4-615 structured coefficient, triangle-split |z| <= |v|+|w| so no free |z| survives;
-- quadratic part folds with NO time cost, linear part pays a^{-1/2} keeping |w| in reserve),
-- composed with the J4-612 center-column bound: the reserved |w| pays sqrt(sigma) against the
-- inner Gaussian (moment lever), Beta(1/2,3/2) time integral <= 2s ==> |E*E(s,z,0)| <=
-- C*s*G_{8s}(z), ALL s>0. Full k>=2 tail O(s) (with banked k>=3), linear slice budget
-- K*((t-s)+s) met, and corrHigher_O_t2_restored: BOUNDED cRem O(t^2) API restored (K carries
-- the diagonal mass G_{8t}(0) explicitly; G_{8t}(0)/pref = 8^{-n/2}, a genuine constant).
-- NOT a1=R/6 (k=1 transport-cancellation + producer re-assembly + capstone piles remain).
import QIQTH.FrozenK2Sharp
import QIQTH.CoInstSmoke
-- J4-618 (BridgeDefect): FrozenTransportBridge REDUCED — the bridge compares only the two
-- k>=2 tails (k=1 cancels), so triangle from separate O(s) tail bounds suffices; frozen side
-- banked (J4-616), transport side GENERIC under a uniform O(1) Gaussian domination (the (0,0)
-- Beta step gives the s for free) + banked k>=3 ladder. Bridge + bounded-cRem O(t^2) API now
-- hold at the capstone's own capstoneDefect under carried labelled hAdom-family dominations;
-- non-vacuity: a proved bridge instance at a nonzero gated-Gaussian witness (kappa=-1,r=1/2).
-- NOT a1=R/6 (transport dominations owed + K1TransportBudget + fat-K piles remain).
import QIQTH.BridgeDefect
-- J4-619 BridgeWidth: width-general (w in [2,8], tau-capped) bridge tail engine consuming the
-- capstone's own carried domination shapes; hEuni landscape: hEuni RIDES ON the capstone's own
-- hpkgBound carry (t'=1 slice, C_U=2C) — retired as a separate pile member; {0}-gate supply
-- banked (J4-536) but DEGENERATE (tail identically 0); CONST route to fat K obstructed
-- (hframeK forces K={0}); fat-K supplier = (hbound-fat)-class per-q transport analysis.
import QIQTH.BridgeWidth
-- J4-620 EquivProbe: the equivariance probe CORE READ verdict — uniform* machinery IS per-q-uniform
-- (charts based at q); hframeK enters ONLY via the dev bound's zeroth jet g̃_q(0)=g(q)≠δ (FRAME, not
-- base point); obstruction pin: tr g̃_q(0)≠n at every off-center row of the curved witness (+ the
-- row-q J4-608 diagonal-witness coefficient tr gi^κ(q)≠n formalized); equivariance route collapses
-- onto J4-608 route (c) = per-q whitening, whose closed-form first lemma E_q^T g^κ(q) E_q = δ is
-- proved (curvedRNC_whitening). NOT a1=R/6 (hpkgBound@fat-K still owed; as-built flat-phase witness
-- plausibly FAILS it — whitened witness variant is the forward route).
import QIQTH.EquivProbe
-- J4-621 WhiteWitness: the formal diagonal NO-GO pin (flatPhase_hpkgBound_fails: no C bounds the
-- flat-phase kernel's heat defect by C·G_2τ on (0,1] at κ<0 — the J4-620 assessment now a THEOREM
-- for the on-gate representative; exact diagonal identity heatOp M = (tr gi−n)/(2τ)·(4πτ)^{-n/2}),
-- the whitened witness (whiteVel/whiteExp/whiteW/whitePullbackMetric via banked E_q; ĝ_q(0)=δ and
-- ∂ĝ_q(0)=0 at EVERY row — the hframeK δ-frame requirement now HOLDS for the whitened chart), and
-- the adapters (two-sided E_q bounds, √n confinement, exact phase transfer Q_g(E_q w)=‖w‖²).
-- NOT a1=R/6 (whitened replay J4-622 + whitened hpkgBound + downstream piles still owed).
import QIQTH.WhiteWitness
-- J4-622 WhiteReplay: the whitened replay — (i) chart-level identification ĝ_q = fderiv-pullback
-- of whiteExp (chain rule through E_q), (ii) ★ whitePullbackMetricInv_dev_uniform = the sole
-- hframeK consumer REPLAYED for the whitened family with NO hframeK/hdevK/ε₀ (value jet exactly δ),
-- (iii) whitened hpkgBound START: whiteChart_heatOp_diag_clean (the 1/τ diagonal floor VANISHES
-- for the whitened chart pair; tr ĝ⁻¹(0)=n by construction) + genuine-curvature gates (det=5/3≠1).
-- NOT a1=R/6 (off-diagonal Gaussian domination + hEbound/hInt + downstream piles still owed).
import QIQTH.WhiteReplay
-- J4-623 WhiteOffDiag: the whitened hpkgBound OFF-DIAGONAL layer — ★ whiteChart_heatOp_offdiag_bound:
-- |heatOp ĝ_q ĝ⁻¹_q (flat G) τ x 0| ≤ C·G_{2τ}(x) on the gate, ALL τ>0, uniform q∈K (the bound the
-- as-built witness provably lacks; CenterZero globalized: quadratic dev × Hessian + NEW whitened
-- Christoffel linear decay × gradient + banked width levers), + √det amplitude bookkeeping
-- (det bounds on the fat ball, whiteW two-sidedly flat-comparable, amp-carrying bound) +
-- whiteExp_fderiv (Jacobian chain, naturality weld opener). Chart→ambient naturality = J4-624.
-- NOT a1=R/6 (naturality transfer + hEbound/hInt + downstream piles still owed).
import QIQTH.WhiteOffDiag
-- J4-624 (WhiteAmbient): the chart→ambient naturality WELD at whiteExp + the AMBIENT transfer of
-- the banked whitened off-diagonal bound. laplaceBeltrami_whiteExp_naturality (the general local
-- engine at φ=whiteExp: Jacobian unit = banked nondeg radius × NEW explicit two-sided whitening
-- inverse E⁻¹=g^κ(q)·E from the banked EᵀgE=δ; pullbackMet=ĝ bridge; Neumann entrywise inverse);
-- whiteInvChart/whiteAmbientKernel (√det·G_τ∘E⁻¹∘uniformInverseChart, mirrors the as-built
-- witness's inverse-chart evaluation); white_ambient_heatOp_eq (EXACT transfer via germ collapse)
-- → ★ white_ambient_heatOp_bound (|heatOp g^κ gi^κ W_white| ≤ C·G_{2τ}(w), chart velocity) +
-- _displacement (ambient Gaussian, honest width λ=2(nC₀²+1)) + white_hpkgBound_gateShaped
-- (capstone hpkgBound SHAPE on-gate; labelled residues R1 off-gate/cutoff, R2 width-2, R3 roles).
-- Witness gate: n=2, κ=−1, K=closedBall 0 2 (ambient pin fails; amplitude √(5/3)≠1 curved).
-- NOT a1=R/6 (R1–R3 + hEbound/hInt + K1TransportBudget + fat-K carriers + capstone
-- co-instantiation + prior piles still owed).
import QIQTH.WhiteAmbient
-- J4-625: WhiteGated — R1 gating lift + R2 width alignment of the whitened hpkgBound.
-- whiteCutKernel/whiteGatedWitness = whitened kernel through the banked radialCutoff +
-- gatedKernel constructor (vanVleckGatedWitness's structure at the whitened chart+amplitude).
-- Off-gate vanishing + cutoff collar + DEEP on-gate agreement (no commutator on the plateau);
-- width-parametric cover engine; ★ white_hpkgBound = FULL ∀(p,q) capstone-hpkgBound shape at
-- width λ=2(nC₀²+1), conditional on labelled gate-certificate legs (i)-(iii) + annulus/commutator
-- bound (iv) — THE honest analytic residue. R2: C₀ opaque (no numeric λ≤8); widen8 (λ∈[2,8]→
-- literal width 8, 2ⁿ cost); hEuni_of_hpkgBound_w feeds BridgeWidth at w=λ; literal width-2
-- capstone slot NOT served at λ>2. NOT a1=R/6 (R1 certificates+annulus, R2 λ≤8, hEbound/hInt,
-- K1TransportBudget, fat-K carriers, capstone co-instantiation + prior piles still owed).
import QIQTH.WhiteGated
-- J4-626 (WhiteAnnulus): ★ white_hann_bound — leg (iv) of the J4-625 package DISCHARGED
-- chart-side (cut-kernel weld transfer + C² Leibniz split + Δ_ĝχ bound + the exponential
-- annulus absorption (1/τ)G_τ≤√2ⁿ(8/a²)G_{2τ} + displacement widening to λ=whiteLam=2(nC₀²+1));
-- gate legs (i)-(iii) at the concrete fat flow-ball gate whiteFlowGate (W1 openness/closure,
-- whitening-inverse chart certificate, frontier via whitening expansion into the b<c collar);
-- ★★ white_hpkgBound_discharged = the FULL ∀(p,q) capstone-hpkgBound SHAPE at the whitened
-- gated witness UNCONDITIONAL at a fat open gate (q∈S q ∀q∈K), width whiteLam (⚠ NOT the
-- literal 2 — J4-625 R2 stands); witness gate: discharged package + diagonal positivity at
-- n=2 κ=−1. NOT a1=R/6 (hEbound/hInt at the whitened kernel, K1TransportBudget, fat-K
-- carriers, capstone co-instantiation at the whitened witness, R2 width + prior piles owed).
import QIQTH.WhiteAnnulus
-- J4-627 (WhiteBridge): the BRIDGE FEED — J4-626's whitened hpkgBound threaded into the bridge
-- consumer chain. whiteDefectKernel = τ-gated ((0,1]) heatOp defect of the whitened gated
-- witness (gate dissolves the affine C(1+t') obstruction → fixed-constant full-∀τ α=−1/2 bound);
-- width-κ α-PARAMETRIC hInt producer (FrozenWire un-pinned from width 2); ★ white_tail_O_s_
-- discharged: ∀ κ≤0, compact K⊆B̄(0,R), ∃ fat gate + lam≥2 with the k≥2 tail O(s)·G_{lam·s}
-- MODULO exactly one labelled input (S1 tripleHEmeas of the WHITENED witness); ★ white_
-- transport_bridge/white_corrHigher = bridge + bounded-cRem API carrying additionally
-- hlam8: lam≤8 (⟺ nC₀²≤3, opaque C₀ — the R2 width reconciliation). NOT a1=R/6 (S1 hEmeas at
-- the whitened witness, R2 lam≤8, K1TransportBudget, fat-K carriers, capstone co-instantiation
-- at the whitened witness + prior piles still owed).
import QIQTH.WhiteBridge
-- J4-628 (WhiteS1): S1 at the whitened witness, FIRST SLICES — Route-B measurable-representative
-- mirror: whitened chart Gc rep (banked hWG_gate_concrete consumed verbatim + closed-form
-- whitening layer), whiteCutKernel Gc rep, witness VALUE triple strongly measurable, and the
-- ∂_τ E3d slot CLOSED (white_hDtau_concrete, unconditional at concrete flow-ball gates) +
-- hgi/hchr coefficient slots. Residue: hP1/hP2 field-pd slots + E3d assembly (= the remaining
-- hEmeas). NOT a1=R/6.
import QIQTH.WhiteS1
-- J4-629 (WhiteS1P1): S1-a at the whitened witness — the hP1 FIRST field-pd measurable-
-- representative slot: raw kernel whiteFieldDeriv; off-base/nonpos/off-CLOSURE vanishing proved;
-- full-gate indicator rep whiteP1Rep + EVERYWHERE identity; on-gate PdiffAt from chart-C2 +
-- whitened first field-jet (banked chart jet through one matToCLM) + on-gate chain-rule identity
-- (cutoff-pd symbolic); measurable on-gate pd rep via the abstract dq engine at whiteCutKernelGc;
-- ★★ white_hP1_concrete = the exact hP1 slot at concrete flow-ball gates MODULO exactly one
-- labelled input hOffS (the whitened-collar/W2 frontier vanishing; exterior proved). NOT a1=R/6
-- (S1-b hP2, S1-c assembly, hOffS collar, hlam8, K1TransportBudget, fat-K carriers, capstone
-- co-instantiation + prior piles still owed).
import QIQTH.WhiteS1P1
-- J4-630 (WhiteCollar): THE WHITENED COLLAR — hOffS DISCHARGED at concrete flow-ball gates;
-- mechanism FREE from the banked κ≤0 contraction (whiteVel_radialSq_le at E_q(E_q⁻¹v)=v; NO
-- frame norm bound needed): whiteCut_locally_zero_offGate (gated witness ≡0 near off-gate
-- points, 0<a<b<c<δ₀), ★ white_hOffS_discharged + ★ white_hOffS2_discharged (hP2-shaped),
-- ★★ white_hP1_unconditional (J4-629 hP1 slot, no carried measurability-side input). NOT
-- a1=R/6 (S1-b hP2, S1-c assembly, hlam8, K1TransportBudget, fat-K carriers, capstone
-- co-instantiation + prior piles still owed).
import QIQTH.WhiteCollar
-- J4-631 (WhiteS1P2): S1-b at the whitened witness — the hP2 SECOND field-pd measurable-
-- representative slot: whiteFieldDeriv2 + everywhere dichotomy (off-base/τ≤0/off-closure/
-- gate-germ order 2), SECOND difference quotient on the J4-629 first-pd witness (PdiffAt of
-- pd_j from whiteCut C² at chart-C² points — NO τ-split, gaussDdim_contDiff ∀τ),
-- ★★ white_hP2_concrete + ★★ white_hP2_unconditional (hOffS2 discharged by J4-630, radii
-- 0<a<b<c<δ₀); order-2 jet layer whiteFlowSecondJet_concrete + whitened mixed Gaussian
-- normal form (Field2NbhdReshape engine). NOT a1=R/6 (S1-c assembly, hlam8,
-- K1TransportBudget, fat-K carriers, capstone co-instantiation + prior piles still owed).
import QIQTH.WhiteS1P2
-- J4-632 (WhiteS1C): S1-c — the E3d assembly at the whitened witness: (a,b,c)-UNIFORM
-- mirrors of the S1 suppliers (the per-slot radii are (a,b,k,ij)-free at source, so the
-- binder closures come free), **white_tripleHEmeas** (tripleHEmeas g^k gi^k
-- (whiteGatedWitness S a b) a THEOREM at concrete flow-ball gates, 0<a<b<c<delta0), the
-- radius-PARAMETRIC J4-626 pkg mirror white_hpkgBound_at_radius, and the PAYOFF
-- **white_tail_O_s_unconditional**: the whitened k>=2 tail <= C_os*s*G_{lam*s} on (0,1]
-- with NO tripleHEmeas antecedent (co-instantiated gate c = min(dp,dS1)/2); bridge Prop
-- feeder now modulo lam<=8 (hlam8) ONLY. NOT a1=R/6 (hlam8, K1TransportBudget, fat-K
-- carriers, capstone co-instantiation + prior piles still owed).
import QIQTH.WhiteS1C
-- J4-633 (WidthFree): THE hlam8 AUDIT + DELETION — the frozen-side G_{8s} landing pin of the
-- FrozenTransportBridge triangle was SPURIOUS: clean widening gaussDdim_le_of_width_le
-- (c<=d => G_c <= sqrt(d/c)^n G_d, NO ratio-4 restriction — the banked gaussDdim_widen_le's
-- d<=4c was itself spurious, recovered at any ratio by gaussDdim_widen_le_ratio);
-- width-parametric bridge Prop FrozenTransportBridgeW w (= banked Prop at w=8, defeq gate) +
-- width-general sufficiency (tail_slice_of_pointwise_w / smoke_bridge_verdict_w: C-K exact at
-- any width, widening ratio <= w/2, H-side width 2 is the model side — NO genuine 8-pin);
-- ★★ white_transport_bridge_unconditional / white_corrHigher_unconditional: the whitened
-- bridge + corrHigher API at landing width max 8 lam with hEmeas discharged AND hlam8 DELETED.
-- NOT a1=R/6 (K1TransportBudget, fat-K carriers, capstone co-instantiation at the whitened
-- witness + width-(max 8 lam) capstone-side re-thread + prior piles still owed).
import QIQTH.WidthFree
-- J4-634 (WhiteCapstoneWire): capstone-side width re-thread + K1 scope. gaussDdim_zero_scale:
-- G_{wt}(0)/pref = (sqrt w)^-n t-FREE => the width re-thread is mechanical. **
-- white_corrHigher_capstone_shaped: the FULL leviSeries E_white slot in the EXACT capstone
-- hCorrHigher binder shape (equality at cRem := heatConv/(pref t^2)) + t-uniform |cRem| <=
-- (C_H C_t + C1)(sqrt(max 8 lam))^-n, from (i) K1TransportBudgetW (max 8 lam) (sole bridge
-- residue) + (ii) the Duhamel split carry (derived: heatConv_leviSeries_split). K1 REDUCED:
-- linear-gain rung + Gaussian moment absorption (r^2 G_tau <= 8 tau sqrt2^n G_2tau) => k=1
-- budget falls from the quadratic-coefficient column bound on E_white (J4-635 target).
-- NOT a1=R/6 (quad-coeff bound + split integrability + fat-K carriers + co-instantiation owed).
import QIQTH.WhiteCapstoneWire
-- J4-635 (WhiteK1): the k=1 WALL — SHAPE VERDICT (Sol-confirmed). The J4-634 quadratic-coeff
-- interface |E|<=C r^2 G is the WRONG shape for the ORDER-0-amplitude whitened witness: the TRUE
-- near-diagonal column shape is INVERSE-LINEAR |E| <= cA (r^2/tau) G + cB (r^2/tau)^2 G, proved
-- at the actual whitened chart data (whiteChart_heatOp_invtau_bound, un-absorbed normal form;
-- banked absorbed O(1) G_2tau shape re-derives from it). Interface gap PINNED
-- (invtauProbe_not_quadratic_coeff: the 1/s is real — no C_E serves); far O(1) G bound SUBSUMED
-- by inverse-linear on r>=a (far_O1_le_invtau) => inverse-linear = the honest GLOBAL interface.
-- What it delivers: K1LinearCeilingW — |heatConv H E| <= C1 G_wt(0) t (O(t) CEILING via
-- absorption + C-K pairing + antitone peak), ONE power short of the t^2 budget; the budget is
-- OUT OF REACH for the order-0 witness (the k=1 term carries the a1 t pref mass; capstone pins
-- heatParametrixFn N>=1). K1 re-scoped: ORDER-ONE (tau u1 transported amplitude) whitened
-- witness with linear-gain defect = J4-636. NOT a1=R/6 (order-1 witness + split integrability +
-- fat-K carriers + co-instantiation + prior piles owed).
import QIQTH.WhiteK1
-- J4-636 (WhiteOrder1): the ORDER-1 whitened witness — the u0+tau*u1 TRANSPORTED amplitude
-- (whiteChartKernel1/whiteAmbientKernel1 = heatParametrixFn 1 at the whitened chart data; the
-- p-dependent transportCoeff u1, NOT a q-only 1+tau*c1). N=1 layer normal form
-- (parametrixResidual_N1_layers: Res1 = (1/t^2) G B w0 + (1/t) G (K0 + B w1) + G K1 - t G Lap w1)
-- + ★ THE CANCELLATION (parametrixResidual_N1_linear_gain): hGauss (radial compat, kills B) +
-- h0 (k=0 transport eq, the CHECKPOINTED identity) + h1 (k=1 eq, level1 coeff NEW) ==> Res1 =
-- -t G Lap(w1) — THE LINEAR GAIN, exact. Gated defect whiteDefect1 (window x residual) obeys
-- |E1(s,p,0)| <= (sqrt w)^n C_Delta s G_ws(p) — the EXACT rung antecedent ==> ★
-- white_K1BudgetW_of_transport: the k=1 t^2 budget K1TransportBudgetW, conditional ONLY on the
-- labelled transport inputs {hwsm,hGauss,h0,h1,hDelta} (+concrete-H version, H-side discharged).
-- Gates: flat antecedent INHABITANCE (cp466: {hw,hGauss,h0,h1} jointly satisfiable, consistency
-- not curved applicability) + cancellation fires (flat residual = 0 THROUGH the theorem) +
-- curved kernel nonzero (kappa=-1) + diagonal a1 CARRIER (u1(0)=R/6 labelled, NOT derived).
-- NOT a1=R/6 (discharge of {hGauss,h0,h1,hDelta,hwsm} at whitened data + Duhamel-split carry +
-- fat-K carriers + co-instantiation + prior piles owed).
import QIQTH.WhiteOrder1
-- J4-637 (WhiteGauss): hGauss at the whitened chart DISCHARGED (unconditional, std-3). The raw
-- radial identity was BANKED (hgball_concrete general-base first-variation Gauss + coordinate
-- contraction + flow weld); uniformFlow_gauss_radial (g̃_q(v)v = g^κ(q)v per-q ball) →
-- whitePullbackMetric_gauss (ĝ(w)w = w exactly — the whitened chart is a TRUE-Gauss-lemma chart)
-- → whiteGauss_discharged (ĝ⁻¹(x)x = x via Neumann unit + sum_invMat_mul = the EXACT WhiteOrder1
-- hGauss binder) → white_K1BudgetW_of_transport_gaussFree (K1 budget conditional on {hwsm,h0,h1,
-- hΔ} only, hGauss GONE). Curved-witness gate at nonzero gate point. NOT a1=R/6 (remaining four
-- K1 inputs + Duhamel-split carry + fat-K carriers + co-instantiation + prior piles owed).
import QIQTH.WhiteGauss
-- J4-638 (WhiteDelta): hΔ at the whitened chart DISCHARGED (conditional ONLY on hwsm, std-3).
-- Operator decomposition |Δ_g f| ≤ Gb·Σ|∂∂f| + Gb·CΓ·n²·Σ|∂f| (laplaceBeltrami_abs_le_of_entry_
-- bounds) + compact-gate jet bounds (smooth_jet_bounds_on_closedBall: contDiff_pd twice +
-- exists_bound_of_continuousOn; û₁'s ray-integral regularity enters ONLY through hwsm) fed by the
-- banked whitened suppliers whiteInv_entry_bound + whiteChart_christoffel_linear_uniform →
-- whiteDelta_discharged (the EXACT WhiteOrder1 hΔ binder, ∃ rΔ>0 ∃ C_Δ≥0, per-row q) →
-- white_K1BudgetW_of_transport_deltaGaussFree (K1 budget conditional on {hwsm,h0,h1} only —
-- hGauss AND hΔ gone). Unconditional supplier gate + hwsm-conditional witness gate at the curved
-- witness (nonzero gate point). NOT a1=R/6 (remaining three K1 inputs + Duhamel-split carry +
-- fat-K carriers + co-instantiation + prior piles owed).
import QIQTH.WhiteDelta
-- J4-639 (WhiteSmooth): the hwsm rung — ★ ORDER READ: the hwsm binder's ⊤ = ω (analytic) is
-- unreachable (ray-integral solve reaches ∞ not ω; whitened metric banked only IsC2At/ContDiffAt-4
-- per point) ⟹ the sanctioned C²-weakened variant BUILT: the full N=1 residual chain
-- (decomp/absorbed/O1-total/4-layer regroup/linear-gain cancellation) replayed at ContDiffAt ℝ 2
-- of {w₀,w₁} AT the point (R1/R3b pattern extended to N=1); whiteDefect1_linear_gain_C2 +
-- white_K1BudgetW_of_transport_C2 (budget consuming the gate-local C² pair, k≤1 only);
-- hΔ discharge re-based at GLOBAL C² (whiteDelta_discharged_C2 via finite-order pd calculus);
-- ★★ white_K1BudgetW_C2_gaussDeltaFree: K1 INPUT LIST NOW {hw0C2, hw1C2, h0, h1} (was
-- {hwsm(∀k,global,ω), h0, h1}); supplier white_K1BudgetW_of_metric_smooth reduces the C² pair to
-- whitened-metric ω-smoothness via the banked HuInftyRebase ∞ tower (metric antecedent = frontier).
-- Gates: flat C² chain fires end-to-end (unconditional), ⊤⟹C² monotonicity (no strengthening),
-- curved witness gate. NOT a1=R/6 (C² pair + h0 + h1 + Duhamel carry + fat-K + co-instantiation owed).
import QIQTH.WhiteSmooth
-- J4-640 WhiteW0: hw0C2 discharged GATE-LOCALLY — w₀ = Θ̂^{−1/2} is ContDiffAt ℝ 2 on a per-q gate:
-- C⁴ flow chart (expRho gate, no hReach) ⟹ C² g̃ entries ⟹ (linear whitening) C² ĝ entries ⟹
-- det C² + det>0 (Neumann unit + segment IVT from det ĝ(0)=1) ⟹ Θ̂ C²,>0 ⟹ w₀ C² (rpow).
-- ★★ white_K1BudgetW_C2_w0Free: K1 INPUT LIST NOW {hw1C2, h0, h1}. w₁ leg scoped:
-- star-shaped solve locality + gate C² of û₁/w₁ given a global-C^∞ source extension (labelled
-- Whitney/cutoff residue; J4-641 = local interchange OR gate C² of T̂û₀). Gates: unconditional
-- curved witness (n=2, κ=−1, q=(1,1), nonzero gate point) + global⟹gate monotonicity.
-- NOT a1=R/6 ({hw1C2, h0, h1} + Duhamel carry + fat-K + co-instantiation + prior piles owed).
import QIQTH.WhiteW0
-- J4-641 WhiteW1: the w₁ leg. ★ ORDER LEDGER: chart C^{k+1} ⟹ ĝ entries C^k; T̂û₀ ∈ C² needs
-- Θ̂ ∈ C⁴ ⟹ chart C⁵ — the banked C⁴ chart does NOT close it (gives C¹ only); the ONE missing
-- order = the Jet-5 rung, carried as labelled hch5. LANDED: (L-a) CLOSED unconditionally —
-- finite-order ray tower (C^N source ⟹ C^N solve) + ContDiffBump cutoff extension + ★ local
-- interchange radialTransportSolve_contDiffAt_two_of_ball (ball-C² source ⟹ ball-C² solve);
-- (L-b) conditional on hch5 — entries C⁴ ⟹ det/Θ̂ C⁴ ⟹ ĝ⁻¹ C² (Ring.inverse at Neumann unit)
-- ⟹ ★ T̂û₀ C² ⟹ ★★ gate-local hw1C2; whiteDelta binder LOCALIZED (hΔ from ball-local C² of
-- w₁); ★★ budget with gate-local w₁ binder; ★★★ white_K1BudgetW_h0h1_of_chartC5:
-- K1 INPUT LIST = {h0, h1} GIVEN the chart-C⁵ residue. hch5 inhabitance NOT claimed (cp466).
-- NOT a1=R/6 ({h0,h1}+hch5 + Duhamel carry + fat-K + co-instantiation + prior piles owed).
import QIQTH.WhiteW1
-- J4-642 WhiteTransport: the h0/h1 transport-wall AUDIT — ★★ conjugation-direction verdict:
-- Gauss reduction K₀ = ¼ρw₀ + r∂_r w₀, K₁ = ¼ρw₁ + w₁ + r∂_r w₁ − Δ_g w₀ (ρ = radialLogDetSym,
-- deviation layer killed, pure algebra); banked fold Θ^{−1/2} = (det g̃)^{+1/4} has WRONG exponent
-- sign ⟹ K₀ = ½ρw₀ ≠ 0 at curved Gauss data (h0-as-bound FALSE; explicit exponential-metric
-- counterexample gate K₀ = 1 with actual vanVleck/transportCoeff suppliers); F1 fix Θ := vanVleck⁻¹
-- ⟹ K₀ = 0 (mod labelled Jacobi chain rule) AND K₁ = 0 near-definitionally from the banked ODE
-- (the Sol-flagged identification, landed; transportOp_inv_inv preserves the R/6 supplier).
-- Curved h0 gate pair discriminates the direction; flat ∃-inhabitance of the K₁ antecedent set.
-- NOT a1=R/6 (F1 re-instantiation + Jacobi bridge + Jet-5 + Duhamel + fat-K + piles owed).
import QIQTH.WhiteTransport
-- J4-643 WhiteF1: the F1 RE-INSTANTIATION. ★ Jacobi bridge r∂_r log det g = ρ (radialLogDetSym)
-- LANDED (banked adjugate Jacobi formula + hasDerivAt_pi slice assembly; honest generality:
-- entrywise PdiffAt + pointwise right inverse + gi-symmetry at the point) ⟹ hamp DISCHARGED
-- (radialDeriv_correctedFold: r∂_r (det g)^{−1/4} = −¼ρ·(det g)^{−1/4}); corrected order-1
-- whitened witness whiteChartKernel1' at Θ̂' := (whiteTheta)⁻¹ (fold = (det ĝ)^{−1/4}, SAME banked
-- û coefficients — transportOp_inv_inv ⟹ R/6 supplier preserved, diagonal carrier intact);
-- h0/h1/htr THEOREMS at the corrected witness (white_h0/h1_corrected); re-derived K1 budget
-- white_K1BudgetW_corrected with h0/h1/hamp/htr GONE — residue = whitened-Gauss geometric legs
-- {hsymI,hgsym,hdGauss(→hdGauss_of_metric_gauss),hinv,hdet} + regularity legs {hwsm,hd,hu1d,hsm,hΔ}
-- (Jet-5; corrected-fold re-instantiation of J4-640/641 dischargers owed). Gates: Jacobi bridge
-- fires at curved data (ρ = 2, two independent routes agree); machinery-route K₀ = 0 end-to-end.
-- NOT a1=R/6 (post-F1 K1 residue + Jet-5 + Duhamel + fat-K + co-instantiation + piles owed).
import QIQTH.WhiteF1
-- J4-644 WhiteF1Reg: the corrected-fold REGULARITY re-instantiation + FINAL ASSEMBLY. ★ Local
-- transport ODE (J3 Leibniz/IBP rebased at C¹ + cutoff/ball localization — the global hsm leg
-- is GONE); ★ GLOBAL det ĝ ≥ 0 (congruence factorization ĝ = E·(Jᵀ·g·J)·E — the honest hdet0;
-- global det > 0 is false territory); corrected dischargers: w₀' = Θ̂'^{−1/2} C² gate (WhiteW0
-- replay through one inv), hΔ at w₁' (fold-generic WhiteW1 mechanism, verbatim), w₁' chart-C⁵
-- C² (banked û₁ leg + corrected fold); hinv from the Neumann unit (sum_mul_invMat); level1
-- engine replayed at NONNEG-global + strict-at-point weight (true unconditionally for
-- Θ̂' = √det ĝ). ★★★ white_K1BudgetW_final: the corrected h0h1-free K1 t² budget with ALL
-- legs internal — THE K1 INPUT LIST IS NOW {hch5 (chart-C⁵/Jet-5 rung)} (+ generic H-side,
-- discharged at the concrete Gaussian witness in _concreteH). Gates: K₀ = 0 at the genuinely
-- curved whitened witness UNCONDITIONAL at a nonzero gate point; R/6 carrier re-pin (labelled
-- hu1, NOT derived); ODE no-silent-strengthening record.
-- NOT a1=R/6 (Jet-5 rung + Duhamel carry + fat-K carriers + capstone co-instantiation owed).
import QIQTH.WhiteF1Reg
-- J4-645: ExpJet5Phase1 — JET-5 phase 1: the PROVEN Rung-5 reduction (C⁵ ⟸ C¹ of fderiv⁴, mirror
-- of the Rung-4 reduction, bootstrapped off unconditional expMap_contDiffOn_four) + the D5
-- STATEMENT layer (expJet5Rhs = 51-term fifth-variation source, continuity, IsExpJet5FundSol
-- shape, source-independent Grönwall uniqueness). hfd4 NOT discharged; hch5 NOT claimed.
import QIQTH.ExpJet5Phase1
-- J4-646: ExpJet5Phase2 — JET-5 phase 2 (J5-2): clmApply5_norm_le + the 51-term uniform [0,1]
-- norm bound expJet5Rhs_norm_le + the order-5 compactness clones (D⁵F unif tube bound +
-- Lipschitz) + the [0,1] GLOBAL fundamental-solution existence expJet5Fund (glue mirror) +
-- IsExpJet5FundSol inhabited + curved-witness non-vacuity gates. J5-3…J5-6 NOT closed.
import QIQTH.ExpJet5Phase2
-- J4-647: ExpJet5Phase3 — JET-5 phase 3 (value-bounds bridge): the D5 Grönwall a-priori value
-- bounds expJet5Fund_value_bound(_Icc) (51-term ρ₅ residual), the order-4 curve mirrors
-- expJet4Curve/expJet4CurveG (t=1 values = expJet4Val/expJet4ValG), the fifth-variation values
-- expJet5Val/expJet5ValG (25 Q-slots instantiated by expJet2Curve/expJet3CurveG/expJet4CurveG)
-- + the uniform 5-linear bound expJet5ValG_norm_le + curved-witness non-vacuity gates.
-- J5-3 crux…J5-6 NOT closed; a₁=R/6 remains conditional (curved).
import QIQTH.ExpJet5Phase3
-- J4-648: ExpJet5Phase4 — JET-5 phase 4 (the J5-3 crux, STAGED): (i) the [0,1]-uniform
-- fourth-variation two-point bound expJet4Val_v_two_pt_Icc_const (51-sub-term ρ₄-telescope
-- re-run with gronwall_vec_residual_Icc — the jet-5 (4+1) telescope feeder), (ii) the Jet₅
-- residual ODE identity expJet5_v_residual_hasDerivWithinAt (51-term source difference),
-- (iii-a) expJet5Val_v_two_pt_diff_gronwall (carried genuine ρ₅-residual bound) + curved
-- non-vacuity gate. Stage (iii-b) 202-sub-term ρ₅-telescope + J5-4/5/6 NOT closed;
-- a₁=R/6 remains conditional (curved).
import QIQTH.ExpJet5Phase4
-- J4-649 (partial): ExpJet5TeleA — JET-5 telescope family file A: the four generic
-- multilinear peel bounds (expJet5TelePeel2/3/4/5, pure normed-space combinatorics) + the
-- assembled aggregate two-point constant expJet5VtpConst (+ nonneg). The 202-sub-term
-- assembly monolith (single-theorem, 217KB) hit a deterministic 25.6M-heartbeat elaborator
-- timeout and is NOT banked; per-block split (J4-650) is the live fix.
-- a₁=R/6 remains conditional (curved).
import QIQTH.ExpJet5TeleA
-- J4-650: the J5-3 crux CLOSED — per-block split architecture replacing the timed-out
-- monolith: ExpJet5BlkA/B/C (13 head-threaded chunk lemmas over the TeleA peels: 15xD2F /
-- 25xD3F / D5F+10xD4F difference blocks, fully generic normed-space form), ExpJet5RhoEq
-- (the isolated pure-R closing ring identity), ExpJet5Phase5 (thin assembly ⟹
-- ★ expJet5Val_v_two_pt_diff, the order-5 two-point Lipschitz bound), ExpJet5Phase5Gate
-- (curved non-vacuity satisfiability gate at curvedRNCMetric (-1), genuine witness tower).
-- J5-4/5/6 NOT closed; NOT exp∈C⁵; a₁=R/6 remains conditional (curved).
import QIQTH.ExpJet5BlkA
import QIQTH.ExpJet5BlkB
import QIQTH.ExpJet5BlkC
import QIQTH.ExpJet5RhoEq
import QIQTH.ExpJet5Phase5
import QIQTH.ExpJet5Phase5Gate
-- J4-651: J5-4 CLOSED — the quintilinear CLM packaging: ExpJet5D5CurveAbstract/CurveG
-- (order-4 curve multilinearity feeders), ExpJet5D5Rhs (source-term multilinearity +
-- 25-slot congruence), ExpJet5D5Val/ValG (matched-Q and genuine 5-linearity via
-- expJet5Fund_unique), ExpJet5D5 (★ expJetD5 5-fold nested CLM via mkContinuous from
-- expJet5ValG_norm_le + ★ expJetD5_two_pt_diff v-Lipschitz operator bound from the J5-3
-- crux + curved gate at curvedRNCMetric (-1)). J5-5/6 NOT closed; NOT exp∈C⁵;
-- a₁=R/6 remains conditional (curved).
import QIQTH.ExpJet5D5CurveAbstract
import QIQTH.ExpJet5D5CurveG
import QIQTH.ExpJet5D5Rhs
import QIQTH.ExpJet5D5Val
import QIQTH.ExpJet5D5ValG
import QIQTH.ExpJet5D5
-- J4-652: J5-5 prerequisite layer (⚠ SCOPING: J5-5 = a multi-brick order-5 REMAINDER
-- tower mirroring J4-5a..f, NOT one brick — expMap_fderiv3_hasFDerivAt consumed the
-- remainder chain, not expJetD4_two_pt_diff): ExpJet5Prereq — D⁴F second-order Taylor
-- (given D⁵F-Lipschitz), full S₅ argument symmetry of D⁵F (four adjacent transpositions,
-- _de = twice-nested compL lift, genuinely new), curved gate. Remaining J5-5: order-5
-- residual + 3rd→4th SecondVar residual + Faà-di-Bruno O(m²) remainder (~2500-line
-- mirror) + fderiv4_hasFDerivAt + contDiffOn_five. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5Prereq
-- J4-653: J5-5 brick (a) — ExpJet5Residual: the order-5 remainder-route residual
-- S = Qw − Qv − R (Q = order-4 solutions, R = order-5 solution): the residual ODE
-- identity + the Grönwall endpoint bound (honest explicit ρ) + curved gate at
-- curvedRNCMetric (-1). Next feeder owed: expJet5_remainder_quadratic_bound(_unif)
-- (the Faà-di-Bruno quadratic cancellation). NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5Residual
-- J4-654: J5-5 FdB feeder PREFIX — ExpJet5RemHelpers: generic multilinear CLM-application
-- norm bounds (clmApply1-4; 5 re-exported from Phase2) + the abstract Block-0 telescoping
-- bound remBlk0_bound (numerically self-checked 1.8e-15) + the VALIDATED 15-block census
-- of the 51-term Θ₅ remainder (1 top + 6×(2+1+1) + 3×(2+2) + 4×(3+1) + Block0; totals
-- reproduce 51). Remaining: top/cross block lemmas + assembly + _P/_unif + gate.
-- NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemHelpers
-- J4-655: FdB block-shape BODY — the four abstract telescope bounds (remBlk0 style,
-- hypotheses-only, no fderiv atoms): remBlkTop_bound (22-term D⁴F/D⁵F pure FdB, 4
-- symmetry hyps), remBlk211_bound (14-term, two first-var slots), remBlk22_bound
-- (10-term, new at order 5), remBlk31_bound (8-term); all numeric-derived (residuals
-- ≤3.3e-16). Assembly (15-block instantiation + Σ ⟹ expJet5_remainder_quadratic_bound)
-- still owed. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemBlkTop
import QIQTH.ExpJet5RemBlkCross
-- J4-656: FdB abstract ASSEMBLY CORE — ExpJet5RemainderA (remMaster_identity: the 81-term
-- abstract master reassembly (dw−dv)qw + (Θ₄w−Θ₄v−Θ₅v) = Σ 15 block-LHS over opaque CLM
-- atoms, 18 symmetry reconciliations, numeric residual 1.8e-14) + ExpJet5RemainderB
-- (remAssembly: the full abstract quadratic bound ‖head‖ ≤ Cfull·nr² chaining the 15
-- banked block bounds). The CONCRETE expJet5_remainder_quadratic_bound instantiation hit
-- an elaboration-cost wall (21-atom set cascade, >25.6M hb) — per-family split owed.
-- NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemainderA
import QIQTH.ExpJet5RemainderB
-- J4-657: the CONCRETE Jet₅ Faà-di-Bruno quadratic remainder LANDED —
-- expJet5_remainder_quadratic_bound (ExpJet5Remainder): the geometric instantiation of
-- remMaster_identity + remAssembly at fderivⁿ(geodesicField) along the tube, with the 15
-- block bounds fed by ExpJet5Prereq Taylor/S₅ symmetry + Lipschitz/value feeders.
-- _P/_unif packaging + curved gate owed; then (b) SecondVar, (d) fderiv4_hasFDerivAt,
-- (e) contDiffOn_five. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5Remainder
-- J4-658 (partial): DIRECTIONAL FdB block layer — remBlkTop/211/22/31_bound_dir
-- (ExpJet5RemDirTop/Cross): per-direction scale variants of the abstract block bounds
-- (Vh/Vk/Vl/Vm, Dh…, Fh…), required because the _P/_unif remainder forms (and the future
-- fderiv4 opNorm peel) need ‖h‖‖k‖‖l‖‖m‖-factored bounds the non-directional blocks
-- conflate. remBlk0_bound already directional-capable. remAssembly_dir + _P + (b)
-- SecondVar + directional uniform feeders + _unif + gate owed. NOT exp∈C⁵; a₁=R/6 cond.
import QIQTH.ExpJet5RemDirTop
import QIQTH.ExpJet5RemDirCross
-- J4-659 (partial): remAssembly_dir (ExpJet5RemAssemblyDir) — the DIRECTIONAL abstract
-- assembly: head ≤ (Σ 15 per-direction block constants)·nr² over ~62 directional scale
-- params, via remMaster_identity + Blk0 + the 4 _dir blocks; the ~130-term distribute
-- ring isolated in the pure-ℝ helper distrib15_nr (J4-650 pattern, first-try green).
-- _P wrapper owed (needs the factor_hklm ~130-monomial ring identity); then (b) SecondVar
-- + feeders + _unif + gate. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemAssemblyDir
-- J4-660: the _P layer LANDED — ExpJet5RemFactor (factor_hklm: the pure-ℝ identity
-- folding the 15 per-direction block constants into a collected 29-term C·‖h‖‖k‖‖l‖‖m‖,
-- sympy-generated, numeric residual exactly 0) + ExpJet5RemainderP
-- (★ expJet5_remainder_quadratic_bound_P: the concrete DIRECTIONAL wrapper — 57
-- directional feeders, 18 symmetry facts verbatim, closes via remAssembly_dir (62 scale
-- + 74 nonneg + 86 analytic + 32 symmetry args) + factor_hklm ⟹
-- ∃C≥0, ‖head‖ ≤ C·‖h‖‖k‖‖l‖‖m‖·‖r‖² on Icc). Gate deliberately deferred (cp466 vacuity
-- discipline). Owed: (b) SecondVar + directional uniform feeders + _unif + gate.
-- NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemFactor
import QIQTH.ExpJet5RemainderP
-- J4-661: brick (b) + the last missing uniform feeder — ExpJet4SecondVarResidual
-- (expJet4SecondVar_residual_Icc_unif: the m-uniform 3rd→4th-variation residual ≤
-- C₀·‖h‖‖k‖‖l‖·‖m‖², Grönwall + the m-uniform order-4 remainder source) +
-- ExpJet5UnifFeeders (expJet4Val_v_two_pt_Icc_unif: the r-uniform 4th-variation
-- two-point bound ≤ Ce·‖h‖‖k‖‖l‖‖m‖·‖r‖). AUDIT: all 57 _P feeders now uniformly
-- dischargeable — _unif is pure assembly. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet4SecondVarResidual
import QIQTH.ExpJet5UnifFeeders
-- J4-662: ★ the _unif layer LANDED — expJet5_remainder_quadratic_bound_unif
-- (ExpJet5RemainderUnif, 860 lines): the r-UNIFORM directional order-5 quadratic
-- remainder — ONE C₀ ≥ 0 chosen before r bounds the Jet₅ residual head by
-- C₀·‖h‖‖k‖‖l‖‖m‖·‖r‖² at the GENUINE expJet{2,3,4}Curve variations (uniform Kstar via
-- expJet_fderiv_tube_bddAbove_unif; constants hoisted before intro r; 57 feeders from
-- the uniform lemmas; _P's symmetry+remAssembly_dir+factor_hklm tail verbatim). The
-- brick-(d) consumer form. Gate deferred (cp466). Owed: (d) expMap_fderiv4_hasFDerivAt →
-- (e) contDiffOn_five → J5-6 weld. NOT exp∈C⁵; a₁=R/6 conditional.
import QIQTH.ExpJet5RemainderUnif
-- J4-663: ★★ J5-5 CLOSED — bricks (d)+(e): ExpMapFDeriv4 (expMap_fderiv4_hasFDerivAt —
-- the little-o assembly: the r-uniform Jet₅ source bound through the order-5 Grönwall,
-- peeled by opNorm bounds ⟹ ‖A_r‖ ≤ Mc·‖r‖² = o(‖r‖); derivative = expJetD5) and
-- ExpMapContDiffFive (★★ expMap_contDiffOn_five: exp_p ∈ C⁵ on the injectivity ball,
-- NO side hypotheses — (d) differentiability + expJetD5_two_pt_diff continuity via the
-- banked ExpJet5Phase1 reduction). Remaining: J5-6 chart weld (hch5) ⟹ K1. Even with
-- exp∈C⁵: NOT κ=1/6, NOT the parametrix, NOT a₁=R/6 (conditional).
import QIQTH.ExpMapFDeriv4
import QIQTH.ExpMapContDiffFive
-- J4-664: ★★★ J5-6 CLOSED — K1 LANDS (WhiteChartC5): uniformFlowExp_contDiffAt_five
-- (the C⁵ chart weld — expMap_contDiffOn_five transferred through the banked overlap
-- bridge, one-order-up mirror of the C⁴ weld; no boundary gap), white_chartC5_discharged
-- (= hch5 exactly), white_K1BudgetW_unconditional (hch5 discharged inline), and
-- ★ white_K1BudgetW_unconditional_curvedWitness — the ANTECEDENT-FREE k=1 t²-budget at
-- n=2, κ=−1, fat K=closedBall 0 2, off-centre q=(1,1), concrete Gaussian H-witness.
-- The ENTIRE Jet-5 campaign (J5-1…J5-6) is closed. a₁=R/6 still owes: Duhamel-split
-- integrability carry, fat-K carrier piles, capstone co-instantiation at the corrected
-- witness, prior labelled piles; R/6 remains a labelled CARRIER (whiteU1(0)=R/6).
import QIQTH.WhiteChartC5
-- J4-665: gap-(i) brick 1 — TruncHIntFromGeometry: the truncated Duhamel-split
-- integrability family with hEzero DISCHARGED FROM GEOMETRY (hEzeroE_concrete, 1≤n) on
-- the honest truncated route (IterConvIntegrableWOn; the non-truncated wide route is
-- firewalled by the affine obstruction), incl. the genuinely-curved specialization at
-- curvedRNCMetric κ<0 with Christoffel smoothness supplied. Remaining gap-(i) carries:
-- the satisfiable affine one-step bound + tripleHEmeas at the curved witness, then the
-- capstone Duhamel-slot threading. NOT a₁=R/6 (conditional; R/6 = carrier).
import QIQTH.TruncHIntFromGeometry
-- J4-666: gap-(i) bricks 2+3 — TruncHIntCarries: hAff (the truncated affine one-step
-- bound, from the banked curved dom-pkg hpkgBound at t':=τ) and tripleHEmeas (from
-- curved_hS1_at_gate) BOTH discharged from geometry at the SHARED curved constGate
-- (seed K={0}, the honest curved gauge) ⟹ curved_hIntOn_from_geometry_closed: the
-- truncated Duhamel integrability family with hEzero+hAff+hEmeas all supplied; honest
-- residue = c<δ₀ (arithmetic jet-reach) + hw/hu (genuine C^∞ inputs). +non-vacuity
-- (Ric(0)≠0). Brick 4 owed: the ~130-binder capstone rethread (leviSeries_summableW_le
-- → _trunc inside the wide capstone). NOT a₁=R/6 (conditional; R/6 = carrier).
import QIQTH.TruncHIntCarries
-- J4-667: gap-(i) brick 4 — ResidualAssemblyTrunc: the capstone Duhamel-slot rethread —
-- wide_a1_R6_of_residue_inf_hEboundW_discharged_trunc: hInt retyped to the TRUNCATED
-- IterConvIntegrableWOn (window = outer t) via the banked one-level-down trunc mirror
-- (single call swap; no body reconstruction). Gap-(i) residue: the gate-unification
-- brick (align the capstone's existential provider gate with the curved constGate) +
-- c<δ₀ + hw/hu. NOT a₁=R/6 (conditional; R/6 = carrier).
import QIQTH.ResidualAssemblyTrunc
-- J4-668: gap-(i) gate unification (CurvedCapstoneGateUnify) —
-- ★ curved_wide_a1_R6_trunc_hIntFed: the trunc a₁ capstone INSTANTIATED at the curved
-- witness with hInt AND hEboundW_le both fed from the ONE curved provider
-- (curvedRNC_heatOp_dom_pkg) at the explicit constGate (route A at the explicit-gate
-- capstone; the ∃-gate capstone is genuinely blocked: varying-radius flow-ball ≠
-- constGate, and integrability does not transport across gates). Discharged internally:
-- hInt, hEboundW_le, all geometry/gauge binders, hChr. Carried: c<δ₀, labelled hw/hu/hsrc,
-- and the five inner Duhamel arrows (hDuhamel/hInter/hDConv/hCH/hCConv). Genuinely
-- curved (Ric(0)=(n−1)κδ≠0). NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedCapstoneGateUnify
-- J4-669: arrow hCH DISCHARGED (CurvedCapstoneHCHFed) —
-- ★ curved_wide_a1_R6_trunc_hIntCHFed: the curved trunc capstone with hEboundW_le +
-- hInt + hCH all fed from geometry (hCH via hCH_discharge_from_geometry with all-banked
-- curved suppliers; openness reach folded: single antecedent c < min δ₀ c₀). Remaining
-- arrows: hDuhamel (delta-family wiring), hInter (BLOCKED at all-τ fixed-C vs affine —
-- the truncated-interchange variant owed), hDConv (delta-family), hCConv (facade C¹ vs
-- slot C² — the open L2/hD1 gap). + labelled hw/hu/hsrc. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedCapstoneHCHFed
-- J4-670: arrow hInter DISCHARGED (LeviInterchangeTrunc + CurvedCapstoneHCHInterFed) —
-- heatConv_leviSeries_interchange_trunc: the (0,T₀]-window Neumann interchange (the
-- port was MECHANICAL: every touched time < t ≤ T₀, so the affine bound fixes on the
-- window; consumes exactly the three data the curved closure already supplies).
-- ★ curved_wide_a1_R6_trunc_hIntCHInterFed: hEboundW_le+hInt+hCH+hInter all fed;
-- arrows left: hDuhamel → hDConv → hCConv. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.LeviInterchangeTrunc
import QIQTH.CurvedCapstoneHCHInterFed
-- J4-672: width-3/2 campaign brick 1 (CurvedIntrinsicWidth32) — VERDICT: the banked
-- width-2 curved bound is a CHART-TRANSFER ARTIFACT (intrinsic 3/2 × displacement 4/3
-- = ambient 2); width-4/3 is NOT pure-Gaussian-reachable (below the 3/2 floor — needs
-- the quadratic-prefactor parametrix estimate). Landed: curvedRNC_intrinsic_width32_defect
-- — the curved intrinsic (pullback-frame) width-3/2 per-q defect domination at
-- curvedRNCMetric κ<0, K={0} (+Ric≠0 non-vacuity). Brick 2 owed: width-parametric
-- transfer + (1+δ) shrunk-radius displacement ⟹ ambient constGate width-3/2 hEdom.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedIntrinsicWidth32
-- J4-673: width campaign brick 2 (WidthParametricGoodGate) — the two reusable
-- primitives: uniformFlowExp_hdisp_ball_delta (∀δ>0 ∃r>0: displacement ≤ (1+δ) —
-- modulus-of-continuity generalization of the 4/3 instance; gate stays inhabited) +
-- gatedWitnessN1_hEboundW_le_of_good_W (the width-parametric chart transfer, ambient
-- W_a exposed) + κ-parametric tower copies. ⚠ SCOPING TENSION recorded: J4-673 sweep
-- says the census tower is width-2-locked (no baseKernelW 3/2 consumer; pure-Gaussian
-- composite (3/2)(1+δ) > 3/2), vs J4-671's claim the delta/Duhamel suppliers need
-- width-3/2 (possibly as gaussDdim(3/2·τ) shapes the sweep missed) — RESOLVE FIRST.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WidthParametricGoodGate
-- J4-674: WIDTH VERDICT RESOLVED + compose adapter (WidthCompose32). Verdict (B):
-- J4-671 was RIGHT — hDConv/hDuhamel hAdom is HARDCODED width-3/2
-- ((A₀+A₁τ)·√(3/2)ⁿ·gaussDdim(3/2·τ)), the gauge hgate is HARDCODED width-4/3
-- QUADRATIC, gauge hAdomHeat/hAdom2 parametric; J4-673's "width-2-locked" was a
-- textual false negative (shapes spelled gaussDdim not baseKernelW). J4-672/673
-- producers vindicated. Landed: hAdom_width32_of_baseKernelW_global/_horizon — the
-- baseKernelW(3/2) → exact-hAdom-binder adapters; residual obstruction isolated to the
-- single input: a baseKernelW(3/2) domination of the witness kernel. Ranked next walls:
-- (1) hAdom-global width-3/2 witness domination; (2) (1+δ) ambient transfer; (3) the
-- width-4/3 quadratic hgate producer; (4) hDelta + diff-under-∫ families.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WidthCompose32
-- J4-675: route verdict + the curved 4/3-quad bridge (CurvedWidth43QuadBridge).
-- VERDICT (β): the pure-Gaussian (1+δ) ambient route is a DEAD END (absorption lemma
-- only widens narrow→wide; the (3/2)(1+δ) composite cannot descend to 3/2) — old walls
-- 1+2 RETIRED. The real route: width-4/3 QUADRATIC hgate ⟹ (banked m=0,1,2 absorptions,
-- 4/3<3/2) ⟹ width-3/2 pure hEdom. Landed: curvedRNC_hEdom_of_width43_quad — the
-- metric-agnostic bridge instantiated at curvedRNCMetric κ (+Ric≠0 gate), isolating the
-- SINGLE surviving wall = the curved on-gate width-4/3 quadratic carry hgate (deepest:
-- the curved width-1 in-chart quadratic parametrix residual → chartTransfer → bridge).
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedWidth43QuadBridge
-- J4-676: ★ THE WIDTH WALL EXTRACTED (WidthOneQuadResidual) — VERDICT: extraction, not
-- re-derivation (the engine's pre-absorption T1/T2/T3 sub-bounds ARE the width-1
-- polynomial forms; the wall was the final absorption collapsing them).
-- uniformResidual_quadPoly_bound_tau_width1: |parametrixResidualN 0| ≤
-- C·((r²/τ)²+r²/τ+1)·gaussDdim(τ) — the EXACT hchart shape chartTransfer_quad consumes;
-- METRIC-AGNOSTIC (extends the flat frontier too — the quadratic form was labelled
-- everywhere). Remaining: the gluing brick (curved uniformFlow instantiation + chart
-- transfer ⟹ the on-gate width-4/3 quadratic hgate). NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WidthOneQuadResidual
-- J4-677: ★★★ THE CURVED WIDTH-3/2 hEdom CLOSED FROM GEOMETRY (Width1QuadCutoff +
-- CurvedHgateGlue). Route deviation (honest): the N=0 star route cannot reach hgate
-- (the witness is the N=1 CUTOFF parametrix; the τ-free gate constant is unsatisfiable
-- for N=1 per Sol #15) — built the width-1 quadratic AFFINE cutoff N=1 residual
-- (cutoffResidualN1_uniformFlow_width1_quad_affine) and glued via the banked two-sided
-- (1/4) near-isometry into the AFFINE bridge: hgate_width43_quad_affine_flowball
-- (metric-agnostic, frontier leg zero via the c>b collar) ⟹
-- ★ curvedRNC_hgate_width43_quad_affine (the on-gate hgate PRODUCED, not carried) ⟹
-- ★ curvedRNC_hEdom_width32_from_geometry: |heatOp g^K| ≤ (E₀+E₁τ)·√(3/2)ⁿ·
-- gaussDdim(3/2·τ) with (a,b,c,S) ∃-produced. Carries: only hChr + hw (the standing
-- curved-tower pair). cp466: κ=−1,n=2,c=0 example elaborated; K={0} no frame collision.
-- Census: the hEdom/hAdom width slot for hDConv/hDuhamel is CLOSED (mod hChr/hw);
-- still owed: hDelta, diff-under-∫ families, hPd2conv, dataLevi, dataAmp,
-- E-combination integrabilities. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.Width1QuadCutoff
import QIQTH.CurvedHgateGlue
-- J4-678: hDelta scoped + the W1-agnostic hDConv reduction (HDConvFromBoundaryLim) —
-- hDConv_gatedWitnessN1_from_daLim_boundary: the concrete DifferentiableAt with the
-- singular hDelta slot internalised and reduced to {hDaLim, hBoundary} + the regular
-- families; introduces NO hAnear (the base-point Gaussian factorization is FALSE at the
-- concrete gate — the W1 chart-image wall: the witness Gaussian peaks at W₀z ≠ z).
-- KEY INTEL: hDConv_AT_GATE (HDConvGateThreading) is already W1-FREE for the
-- DifferentiableAt conclusion (only the loc-unif derivative limit needed, never the
-- boundary value) — the load-bearing path bypasses hBoundary entirely.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.HDConvFromBoundaryLim
-- J4-679: the W1-free hDConv slot certificate (CurvedHDConvSlotThreading) —
-- curvedHDConv_fed_slots_at_constGate: the three geometry-closable slots of
-- hDConv_AT_GATE certified at the curved witness from only hChr+hw (gauge pair,
-- width-3/2 hEdom, width-3/2 hAdom+hWDom) + Ric≠0 gate. HONEST VERDICT: the arrow does
-- NOT drop — residue = (W-census) ~40 analytic members with no curved supplier
-- (feeding would LENGTHEN the carry list) + (W-width/gate) the width-2 vs width-3/2
-- suppliers each ∃-pick their own gate radius — unification owed.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedHDConvSlotThreading
-- J4-680: ★★ THE WIDTH GATE-UNIFICATION LANDED (CurvedUnifiedGateBounds) —
-- curvedRNC_unified_gate_bounds: ONE gate (a,b,c) / one witness cW carrying all four
-- capstone binders: width-2 all-t' hpkgBound ∧ width-3/2 hEdom ∧ width-3/2 hAdom ∧
-- frozen hWDom. Verdict: all suppliers threshold-monotone, no hard radius fix; pkg =
-- width-widening of hEdom (gaussDdim_le_gaussDdim_chart @(3/2,2) + affine→(1+t'));
-- hAdom via GateSqControl at glue's NATIVE gate from the (1/4) near-isometry. The
-- J4-679 W-width/gate obstruction is REMOVED; the unified hpkgBound is literally the
-- constGate shape the CONSTRADIUS core consumes. cp466 clean (K={0}, Ric≠0).
-- Full capstone re-composition on top = next. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedUnifiedGateBounds
-- J4-681: ★★ THE UNIFIED-GATE CAPSTONE (CurvedCapstoneUnifiedGate) —
-- curved_wide_a1_R6_trunc_unifiedGate: the curved trunc a₁ capstone re-composed onto
-- the width-unified gate — fed slots (hInt/hEboundW_le/hCH/hInter) AND the width-3/2
-- hEdom/hAdom certificates all on ONE witness cW (defeq bridge: constGate unfolds to
-- the unified gate's flow-ball literally). Standing antecedents: κ<0, 1≤n, labelled
-- hw/hu/hsrc, T₀>0; inner: c<min δ₀ c₀ + the three arrows hDuhamel/hDConv/hCConv.
-- +Ric≠0 gate. HONEST RESIDUE now purely: three arrows + W-census + labelled inputs;
-- R/6 = labelled CARRIER. NOT a₁=R/6.
import QIQTH.CurvedCapstoneUnifiedGate
-- J4-682: the census-shrink certificate (CurvedCensusShrinkJ4682) —
-- curved_census_closed_bundle: 7 census members certified from {hChr,hw,hu} at the
-- unified gate (gauge×2, hEdom, hAdom, hWDom, hInnerCont, hFzero). ⚠ STRUCTURAL
-- FINDING: the K={0} seed DEGENERATES the measurability tier (witness z-slice a.e. 0
-- off origin — the T-REDUCED members close cheaply but emptily) and the SAME null
-- support PROVABLY blocks hmassone (curved_census_hmassone_blocked_at_singleton
-- derives False from gate-activation at K={0}). TRUE CENSUS WALL: (a) the mass-one /
-- nontrivial-K reformulation (center-only gauge without the singleton degeneracy);
-- (b) the T-NOSUPPLIER analytic core (hQ1, DCT triple, MemLapFull/AdjLo/ECombine,
-- dataLevi/dataAmp/hPd2conv). Net owed ≈31, of which ≈11 are one chart-IFT
-- strip-continuity interface away (but degenerate at K={0}). NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedCensusShrinkJ4682
-- J4-684: (hbound-fat) layer 4 WIDTH-2 face (CurvedA1CenterResidW2) — the center-gauge
-- width-2 τ-residual engines: uniformResidual(_Linear)_gaussian_bound_tau_width2_center
-- (|R₀| ≤ (C₀ + Cεu·ε₀/τ)·gaussDdim(2τ); ε₀ paid twice — T1 constant + T2 cross via the
-- per-q center deviation replacing hframeK; T3 verified frame-free) + fat-K curved
-- instantiations at K=closedBall 0 r (explicit ε₀=(|κ|/3)nr², coeff from layer 3) +
-- satisfiability. Closes the width-3/2→2 gap between banked J4-607 and the baseKernelW-2
-- consumer. Layer 5 owed: producer re-assembly (route (c) per-q frozen-Gaussian
-- re-basing per J4-608). NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedA1CenterResidW2
-- J4-685: layer-5 sub-brick + the ε₀/τ OBSTRUCTION VERDICT (CurvedA1ReBaseHBdomW2) —
-- PROVED: the ε₀/τ term of the width-2 center residual has NO uniform majorant on
-- (0,t'] (scalar + kernel forms; fires non-vacuously at fat curved K, ε₀=(|κ|/3)nr²>0)
-- ⟹ the all-τ width-2 bound at the vanVleck consumer is genuinely obstructed — NOT an
-- absorbable term. The banked all-τ resolution is the WHITENING route (J4-620…626,
-- white_hpkgBound_discharged) at the whitened witness + widened width whiteLam.
-- +honest τ-windowed partial + ε₀=0 shape-compat (interface real; ε₀ = sole obstruction).
-- Downstream fork: widen the D2 consumer to width-w (BridgeWidth [2,8]; whiteLam≤8 ⟺
-- nC₀²≤3 unproved) OR re-base gated_hBdom onto whiteGatedWitness. NOT a₁=R/6.
import QIQTH.CurvedA1ReBaseHBdomW2
-- J4-686: the whitened↔vanVleck reconciliation (WhiteHBdomReconcile) — route (β):
-- leviSeries_full_col_of_tail (★ the reusable WIDTH-W full-series column engine —
-- leviSeries = (tail) − E split; the width-2 leviSeries_dominatedW_le was the pin) +
-- white_leviSeries_full_col + ★ white_hBdom_col_discharged (the whitened column hBdom
-- at fat K, NO lam≤8 — R2 DISSOLVES for the hBdom, surviving only as the frozen-G₈
-- comparison artifact; nC₀²≤3 is opaque-C₀-UNDECIDED in-repo, not a dimensional
-- theorem) + width verdict + cp466 gate (n=2, κ=−1, K=closedBall 0 2). Downstream:
-- (i) whitened re-base of the hInnerCont builder / all-rows engine; (ii) the S1
-- tripleHEmeas carry; (iii) prior piles. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WhiteHBdomReconcile
-- J4-687: the ALL-ROWS whitened hBdom (WhiteHBdomAllRows) — verdict: the column
-- restriction was COSMETIC (every helper already general-endpoint; the whitened
-- one-step supply is full-matrix, no per-row re-whitening). Landed: the row-generalized
-- tail ladder + leviSeries_full_row_of_tail (★ the width-w FULL-ROW engine) +
-- ★ white_hBdom_discharged: ∀ z y, |leviSeries(whiteDefectKernel)| ≤ C_L·G_{lam·s}(z−y)
-- at fat K, modulo the single S1 input, NO lam≤8. +cp466 gate (n=2, κ=−1, fat K).
-- Downstream: (a) the builder-side witness+width re-base (curved_hInnerCont_of_
-- dominations pinned at vanVleck/width-2); (b) the S1 tripleHEmeas carry; (c) prior
-- piles. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WhiteHBdomAllRows
-- J4-688: the builder-side re-base (CurvedA1HContDomGen + WhiteHInnerCont) — verdict:
-- the hContDom→hInnerCont chain is WITNESS-GENERIC (the DCT engine was already
-- abstract-F; the domination builder abstract-A,B) and only WIDTH-hardcoded ⟹ pure
-- abstraction replay: hContDom_of_gaussDom_gen + hInnerCont_of_dominations_generic
-- (any positive widths wA/wB, prefactor Cpre) subsume the pinned vanVleck builder;
-- white_hInnerCont_of_dominations = the whitened instantiation (B-slot discharged
-- internally from white_hBdom_discharged given S1; width lam, no lam≤8) modulo
-- {S1 tripleHEmeas, the whitened VALUE domination hWdom (not banked in any shape —
-- future brick from the whitened cutoff structure), hmeas, hcont}. +cp466 gate.
-- NOT a₁=R/6 (R/6 = carrier).
import QIQTH.CurvedA1HContDomGen
import QIQTH.WhiteHInnerCont
-- J4-689: hWdom PROVED (WhiteWitnessValueDom) — white_witness_value_dom: the whitened
-- VALUE-kernel Gaussian domination |whiteGatedWitness| ≤ Cpre·gaussDdim(wA·τ)(p−q) at
-- the concrete whiteFlowGate (wA = nC₀²+1; cutoff clamp + determinant control + the
-- banked near-isometry width transfer) + cp466 gate (n=2, κ=−1, fat K). The (b′) carry
-- is now a proved lemma; residual = the GATE-HANDLE wire: white_hBdom_discharged returns
-- its gate ∃-opaquely and the value bound is genuinely FALSE at an arbitrary gate ⟹ a
-- CO-EMITTING discharger (one shared gate emitting both slots) is the one remaining
-- wire. Carries otherwise unchanged {S1, hmeas, hcont}. NOT a₁=R/6 (R/6 = carrier).
import QIQTH.WhiteWitnessValueDom
-- J4-690: ★★ THE CO-EMITTING GATE DISCHARGER (WhiteGatePackageCombined) — verdict:
-- both banked constructions are radius-monotone flow-ball builds ⟹ co-emit at the
-- shared c* = min(δ₀, Rf, r₀/(CE+1))/2. white_gate_package_combined (ONE gate: the
-- all-τ defect package [width lam=whiteLam] ∧ the value domination [width wA=nC₀²+1])
-- + white_hBdom_combined (the re-threaded all-rows Levi hBdom at that gate) +
-- ★ white_hInnerCont_combined — hWdom DISCHARGED; carries now exactly
-- {S1 tripleHEmeas, hmeas, hcont}. +cp466 gate (n=2, κ=−1, fat K). Remaining:
-- those three carries + the K1TransportBudget/capstone piles. NOT a₁=R/6
-- (R/6 = carrier; flat tower only).
import QIQTH.WhiteGatePackageCombined
-- J4-691: S1 DISCHARGED (WhiteHInnerContFinal) — the whitened tripleHEmeas was already
-- banked unconditionally (white_tripleHEmeas_uniform, Route-B/E3d — the vanVleck
-- analogue was witness-specific and NOT the source); the obstruction was radius-matching,
-- solved by THREE-WAY co-instantiation (defect pkg + S1 + the radius-parametric value
-- domination white_witness_value_dom_at_radius) at c = min(δp,δS,δV)/2.
-- ★ white_hInnerCont_final: carries exactly {hmeas, hcont} — both GENUINE WALLS
-- (hmeas = the Levi z-slice a.e.-summability/convergence trio LeviSeriesLocalData/hFsum;
-- hcont = Levi time-continuity; open on the vanVleck side too). +cp466 gate.
-- NOT a₁=R/6 (R/6 = carrier; flat tower only).
import QIQTH.WhiteHInnerContFinal
-- J4-692: THE CONVERGENCE TRIO LANDED (WhiteLeviConvergenceTrio) — extraction verdict
-- CONFIRMED: white_leviSeries_zmeas (the whitened Levi z-slice AESM: termwise iterE
-- measurability + pointwise summability dominated everywhere by the banked colC series
-- via iterE_row_bound_w ⟹ leviSeries_stronglyMeasurable_of_termwise) +
-- white_witness_value_concrete_uniform (the radius-uniform witness measurability) ⟹
-- ★ white_hInnerCont_hmeas: hmeas DISCHARGED (four-way shared radius
-- c = min(δp,δS,δV,δW)/2); carries now {hcont} ONLY (the whitened Levi time-continuity
-- — the last carry; the Weierstrass route needs iterE_k time-continuity, not banked
-- composably). +cp466 gate. NOT a₁=R/6 (R/6 = carrier; flat tower only).
import QIQTH.WhiteLeviConvergenceTrio
-- J4-693: the hcont witness factor DISCHARGED (WhiteHcontWitnessFactor) —
-- whiteWitness_time_continuousAt: the witness factor s ↦ whiteGatedWitness(u−s) 0 z is
-- continuous for EVERY z (gated kernel = 0 or cutoff·√det·gaussDdim(u−s); only the
-- Gaussian is s-dependent) + leviTimeCont_of_jointStrip (extraction from the banked
-- joint strip shape) ⟹ ★ white_hInnerCont_leviJoint: the carry morphs {hcont} →
-- {hJoint = the Levi-slice JOINT continuity (hBcontEvery_of_carries shape)}, whose
-- residual = the whitened iterE termwise joint continuity (the M-test wall — open on
-- both witnesses; needs a width-generic LeviMTest replay: the pinned one is width-2).
-- +cp466 gate. NOT a₁=R/6 (R/6 = carrier; flat tower only).
import QIQTH.WhiteHcontWitnessFactor
