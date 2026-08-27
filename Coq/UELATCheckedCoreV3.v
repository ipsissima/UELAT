(** UELATCheckedCoreV3.v -- current-paper CHECKED-EXACT candidate surface.

    Governing manuscript:
      Proof-Carrying Analytic Approximation:
      Local-to-Global Evidence Transport at Encoding Cost
      arXiv:2506.22693 v3.

    This surface intentionally excludes the four current PARTIAL boundaries:
      - Lemma 3.1 constructive epsilon-Hahn--Banach existence;
      - full concrete Theorem 3.2 effective universality pipeline;
      - concrete external Sobolev instantiation of Theorem 5.6;
      - concrete external Sobolev instantiation of Theorem 7.2.

    Excluding a PARTIAL theorem is not a claim against it. It prevents an
    uncompleted research interface from blocking kernel validation of theorem
    statements that are already self-contained/conditional at their declared
    manuscript hypotheses.
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
  PUFEMCompiler
  WeightedSynthesisBudget
  RationalBitBudget
  GlobalCodeSize

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
  Proposition73CompilerBound
  StandardRationalRegime
  StandardRationalH1H7
  ManuscriptH1H7
  Theorem74Manuscript
  DescentFailureModes

  ContextualChoice
  FiniteMeasureBoundary
  InformationBoundary
  ExtensionalSheaf.
