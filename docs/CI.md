# Continuous Integration

This repository uses a GitHub Actions workflow to exercise the Coq proofs and the accompanying Python and Julia test suites.

## What runs in CI?

The workflow lives in [`.github/workflows/ci.yml`](../.github/workflows/ci.yml) and performs the following steps on Ubuntu:

1. Install Coq (via [`coq-community/setup-coq`](https://github.com/coq-community/setup-coq)) together with any opam dependencies.
2. Build all Coq sources by running [`.github/scripts/build_coq.sh`](../.github/scripts/build_coq.sh), capturing the compiler output in `coq-build.log` for later inspection.
3. Ensure no proof files contain `Admitted` or `Axiom` by running [`.github/scripts/check_coq_no_admitted.sh`](../.github/scripts/check_coq_no_admitted.sh).
4. Run the Python unit tests with `pytest` for Python 3.10 and 3.11.
5. Run the Julia test suite via `Pkg.test()` for Julia 1.9 and 1.10.
6. Cache opam, pip, and Julia package directories to speed up subsequent runs.
7. Upload `coq-build.log` as a workflow artifact whenever the Coq build fails.

## Reproducing locally

To reproduce the checks locally, install the required toolchains and run:

```sh
# Coq build and admitted check
bash .github/scripts/build_coq.sh
bash .github/scripts/check_coq_no_admitted.sh

# Python tests
python3 -m pip install -r requirements.txt  # or pip install pytest if no requirements.txt
pytest -q

# Julia tests
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

Adjust the Python and Julia versions locally to match those declared at the top of the workflow file.
