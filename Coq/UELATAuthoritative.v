(** UELATAuthoritative.v -- staging entry point for the authoritative 35-page v3.

    Only modules already migrated to the current manuscript contract are
    exported here. Legacy v1/v2 modules and superseded-v3 wrappers are excluded.
    This surface is intentionally smaller than the final repository surface so
    CI can provide useful compiler feedback while migration continues.
*)

From UELAT.V3 Require Export
  CertificateEnrichment
  RepresentedSpace
  ComputableBanach
  BanachNormLemmas
  EvidenceCategory
  SlackCollapse
  StrictSlackSearch
  DyadicVanishing
  GenericSlackCertification
  ResourceProfile
  ProofDAG
  RationalSobolev
  RationalMeshRefinement
  RationalPUFEM
  RationalSynthesis
  PUFEMCompiler
  WeightedSynthesisBudget
  OrderNeutralDescent
  QuasiUniformGeometry
  DescentAssembly
  GeometricPrecisionSchedule
  H1H7Descent
  DescentCertificateSize
  FiniteCodeDescent
  EpsilonPrecision
  OrderNeutralEpsilonDescent
  ManuscriptH1H7
  Theorem74Manuscript.
