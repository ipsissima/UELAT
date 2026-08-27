(** UELATAuthoritativeV3.v -- canonical current-paper formalization surface.

    Governing manuscript:
      Proof-Carrying Analytic Approximation:
      Local-to-Global Evidence Transport at Encoding Cost
      arXiv:2506.22693 v3.

    This entry point intentionally excludes the withdrawn probes--models
    adjunction and other pre-v3 theorem surfaces.  Section 3 modules are
    exposed here only when they have been observed compiling under the pinned
    Rocq 9.2 current-paper build; unfinished strong Type-2/Hahn--Banach
    assembly remains outside this authoritative aggregate.
*)

From UELAT.V3 Require Export
  EvidenceSyntax
  Presentation
  Evidence
  MetricReflection
  EffectiveCompleteness
  RealizableMap
  GenericLift
  Composition

  CertificateEnrichment
  RepresentedSpace
  ComputableBanach
  EvidenceCategory
  StrictSlackSearch
  DyadicVanishing
  GenericSlackCertification
  SlackCollapse
  ProofRelevant
  EvidenceReindexing
  EvidenceTransport
  GrothendieckEvidence
  ResourceProfile

  LinearUniversality
  NormingPolar
  EffectiveClosedCompactness

  ProofDAG
  ProofDAGBuilder
  ProofDAGEncodingAppend
  PersistentGenealogy

  RationalSobolev
  RationalArbitraryMesh
  RationalMeshRefinement
  RationalCommonMesh
  RationalFiniteOperations
  RationalSobolevPresentation
  RationalSobolevCheckers
  RationalSobolevCompleteness
  RationalSobolevBooleanCheckers
  RationalHatPOU
  RationalIntervalCover
  RationalPOUAssignment
  RationalPOUConstruction
  RationalSynthesis
  RationalPUFEM
  LocalizedPUFEMCompiler
  LocalizedPUFEMEvidence
  SobolevPUFEMAnalyticInterface
  PUFEMCompiler
  WeightedSynthesisBudget
  RationalBitBudget
  GlobalCodeSize

  ScaleSensitivePUFEMAnalytic
  OrderNeutralDescent
  QuasiUniformGeometry
  DescentAssembly
  GeometricPrecisionSchedule
  H1H7Descent
  DescentCertificateSize
  FiniteCodeDescent
  EpsilonPrecision
  OrderNeutralEpsilonDescent
  H6EncodingRegime
  StandardRationalRegime
  StandardRationalH1H7
  ManuscriptH1H7
  Theorem74Manuscript

  ContextualChoice
  FiniteMeasureBoundary
  InformationBoundary
  ExtensionalSheaf.
