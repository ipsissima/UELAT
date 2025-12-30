(** UELAT.v — Main entry point for the UELAT formalization

    Universal Embedding and Linear Approximation Theorem (UELAT)
    Coq Formalization

    This module exports all components of the UELAT development.

    Main contributions:
    1. UELAT — Internal/external formulations with certificates
    2. Probes-Models Adjunction — Fibered adjunction (Theorem 3.3)
    3. CCP — Contextual Choice Principle (Section 4)
    4. Certificate Incompressibility — Lower bounds (Theorem 8.2)
    5. Effective Descent — Gluing with size bounds (Theorem 9.3)

    Reference: https://arxiv.org/abs/2506.22693
*)

(** * Utility Modules *)
From UELAT.Util Require Export
  Reals_ext
  Summation
  Entropy.

(** * Foundations *)
From UELAT.Foundations Require Export
  Certificate      (* Certificate type grammar - Appendix A *)
  ProbeTheory      (* Probe category definitions - Section 3.2 *)
  CCP.             (* Contextual Choice Principle - Section 4 *)

(** * Adjunction *)
From UELAT.Adjunction Require Export
  Probe            (* Category Probe *)
  Model            (* Category Model *)
  Functors         (* F and G functors *)
  Adjunction       (* Main adjunction theorem - Theorem 3.3 *)
  Reflection.      (* Reflection principle - Theorem 3.7 *)

(** * Approximation Theory *)
From UELAT.Approx Require Export
  Certificate      (* Bernstein certificate definitions *)
  Bernstein        (* Bernstein basis and operator *)
  Bernstein_Lipschitz  (* Main Lipschitz approximation theorem *)
  Spec             (* Problem specifications *)
  UELAT_Internal   (* Internal UELAT theorem - Theorem 5.1 *)
  UELAT_External   (* External/computable version - Section 6 *)
  Incompressibility  (* Certificate lower bounds - Theorem 8.2 *)
  EffectiveDescent.  (* Descent with size bounds - Theorem 9.3 *)

(** * Stability *)
From UELAT.Stability Require Export
  Modulus          (* Modulus of continuity *)
  UniformStability (* Certificate stability - Theorem 7.1 *)
  CertificateComposition.  (* Certificate algebra *)

(** * Examples *)
From UELAT.Examples Require Export
  ExpCert          (* exp(x) certificate *)
  FourierCert      (* Fourier sine series - Appendix C *)
  ChebyshevCert    (* Chebyshev polynomials - Section 2 *)
  SobolevCert.     (* Sobolev space examples *)

(** * Top-level Theorems *)

(** Re-export main theorems with descriptive names *)

(** Theorem 3.3: Probes-Models Adjunction F ⊣ G *)
Definition Adjunction_Theorem := UELAT_Adjunction.adjunction_bijection.

(** Theorem 5.1: Internal UELAT *)
Definition Internal_UELAT := UELAT_Internal.internal_UELAT.

(** Theorem 7.1: Certificate Stability *)
Definition Stability_Theorem := UELAT_UniformStability.uniform_certificate_stability.

(** Theorem 8.2: Certificate Incompressibility *)
Definition Incompressibility_Theorem := UELAT_Incompressibility.certificate_incompressibility.

(** Theorem 9.3: Effective Descent *)
Definition EffectiveDescent_Theorem := UELAT_EffectiveDescent.glued_cert_size_bound.

(** Main Bernstein Lipschitz approximation theorem *)
Definition Bernstein_Lipschitz_Theorem := Bernstein.bernstein_uniform_lipschitz.
