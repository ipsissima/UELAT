# CI for UELAT

This repository uses GitHub Actions to run Coq proofs and unit tests for Python and Julia.
The workflow runs on `ubuntu-latest` and performs:

- Coq build (via `.github/scripts/build_coq.sh`). Output goes to `.github/logs/coq-build.log`.
- A check for uses of `Axiom` or `Admitted` (via `.github/scripts/check_coq_no_admitted.sh`). Matches are saved to `.github/logs/coq_admitted_hits.txt`.
- Python unit tests (via pytest).
- Julia unit tests (`julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'`).

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
python -m pip install -r requirements.txt
pytest -q
```

Run Julia tests:
```bash
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

## Debugging CI failures
If Coq build fails, download .github/logs/coq-build.log from the workflow artifacts.

If the admitted/axiom check fails, download .github/logs/coq_admitted_hits.txt.

For opam-related failures, ensure you have opam and Coq installed locally; the CI installs Coq via coq-community/setup-coq or opam.
