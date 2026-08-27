(** UELATAuthoritativeV3.v -- canonical current-paper formalization surface.

    Governing manuscript:
      Proof-Carrying Analytic Approximation:
      Local-to-Global Evidence Transport at Encoding Cost
      arXiv:2506.22693 v3.

    This entry point intentionally excludes the withdrawn probes--models
    adjunction and other pre-v3 theorem surfaces.  PARTIAL Section 3 interfaces
    may be added here only when their dependency path is explicit.
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
  ExtensionalSheaf.
