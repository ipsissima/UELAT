# CI for UELAT

This repository uses GitHub Actions to run Coq proofs and unit tests for Python and Julia.
The workflow runs on `ubuntu-latest` and performs:

- Coq build (via `.github/scripts/build_coq.sh`, which respects `Coq/_CoqProject`). Output goes to `.github/logs/coq-build.log`.
- A check for uses of `Axiom` or `Admitted` (via `.github/scripts/check_coq_no_admitted.sh`). Matches are saved to `.github/logs/coq_admitted_hits.txt`.
- Python unit tests (via `pytest`) that discover tests under `tests/`.
- Julia unit tests (`julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'`) which leverage the root `Project.toml` and `test/` directory.

## Run locally

Make helper scripts executable:
```bash
chmod +x .github/scripts/*.sh
```

Run Coq build:
```bash
bash .github/scripts/build_coq.sh
# logs are written to .github/logs/coq-build.log
```

Check for Axiom/Admitted:
```bash
bash .github/scripts/check_coq_no_admitted.sh
# matches (if any) are in .github/logs/coq_admitted_hits.txt
```

Run Python tests:
```bash
python -m pip install pytest
pytest
```

Run Julia tests:
```bash
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

## Debugging CI failures
If Coq build fails, download .github/logs/coq-build.log from the workflow artifacts.

If the admitted/axiom check fails, download .github/logs/coq_admitted_hits.txt.

For opam-related failures, ensure you have opam and Coq installed locally; the CI installs Coq via coq-community/setup-coq or opam.
