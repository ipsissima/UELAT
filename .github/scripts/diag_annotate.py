#!/usr/bin/env python3
"""Turn a Rocq build log into GitHub check-run annotations.

Why this exists: workflow *logs* are served from a blob host that some API
clients cannot reach, while check-run *annotations* are available straight
from the REST API. Routing the compiler output through annotations makes a
failing Rocq build diagnosable without log access.

Read-only with respect to the repository: it parses a log and prints
workflow commands. It changes no source and promotes no status.

Usage:
  diag_annotate.py <build.log> <coqdir> <order-file> <gate-file> <outdir>
"""

import os
import re
import sys

# Coq/Rocq error blocks look like:
#   File "./V3/Foo.v", line 84, characters 8-45:
#   Error: <possibly multi-line message>
BLOCK = re.compile(
    r'File "(?P<file>[^"]+)", line (?P<line>\d+), characters [^:]*:\s*\n'
    r'(?P<body>.*?)'
    r'(?=\nFile "|\nmake|\n\x1b|\Z)',
    re.DOTALL,
)

MAX_MSG = 1800


def esc_data(s: str) -> str:
    return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def esc_prop(s: str) -> str:
    return esc_data(s).replace(":", "%3A").replace(",", "%2C")


def main() -> int:
    log_path, coqdir, order_path, gate_path, outdir = sys.argv[1:6]

    with open(log_path, "r", errors="replace") as fh:
        log = fh.read()

    # Dependency-sorted file list from `coqdep -sort`.
    with open(order_path, "r", errors="replace") as fh:
        order = [t for t in fh.read().split() if t.endswith(".v")]
    order = [re.sub(r"^\./", "", p) for p in order]

    gate = set()
    if os.path.exists(gate_path):
        with open(gate_path, "r", errors="replace") as fh:
            for ln in fh:
                ln = ln.strip()
                if ln.startswith("V3/") and ln.endswith(".v"):
                    gate.add(ln)

    # A module is "compiled" iff its .vo landed on disk.
    def compiled(rel: str) -> bool:
        return os.path.exists(os.path.join(coqdir, rel[:-2] + ".vo"))

    # Collect the first Error block per file. Warnings are ignored: they do
    # not stop the build and would drown the signal.
    first_err = {}
    for m in BLOCK.finditer(log):
        body = m.group("body").strip()
        if not body.startswith("Error"):
            continue
        rel = re.sub(r"^\./", "", m.group("file"))
        if rel not in first_err:
            first_err[rel] = (int(m.group("line")), body)

    ordered_all = [p for p in order]
    failed = [p for p in ordered_all if not compiled(p)]
    # Direct failures: a file that did not compile AND produced its own
    # error. A file with no error of its own was blocked by a dependency.
    direct = [p for p in failed if p in first_err]
    blocked = [p for p in failed if p not in first_err]

    ok = len(ordered_all) - len(failed)
    print(
        "::notice title=Rocq build summary::"
        + esc_data(
            f"{ok}/{len(ordered_all)} modules compiled; "
            f"{len(direct)} direct failures; {len(blocked)} blocked by dependencies"
        )
    )

    def tag(p: str) -> str:
        return "GATE" if p in gate else "research"

    if direct:
        def oneline(body: str) -> str:
            parts = [s.strip() for s in body.splitlines() if s.strip()]
            return " | ".join(parts)[:190]

        lines = [
            f"{i + 1}. {p}:{first_err[p][0]} [{tag(p)}]  " + oneline(first_err[p][1])
            for i, p in enumerate(direct)
        ]
        print(
            "::notice title=Direct failures in dependency order::"
            + esc_data("\n".join(lines)[:MAX_MSG * 3])
        )

    if blocked:
        print(
            "::notice title=Blocked by dependencies::"
            + esc_data("\n".join(f"{p} [{tag(p)}]" for p in blocked)[:MAX_MSG * 2])
        )

    # One annotation per direct failure, chunked so no single step exceeds
    # the per-step annotation display limit.
    chunk, idx = [], 1
    for p in direct:
        line, body = first_err[p]
        cmd = (
            f"::error file=Coq/{p},line={line},"
            f"title={esc_prop(f'[{tag(p)}] {os.path.basename(p)}')}::"
            + esc_data(body[:MAX_MSG])
        )
        chunk.append(cmd)
        if len(chunk) == 8:
            with open(os.path.join(outdir, f"ann_{idx}.txt"), "w") as fh:
                fh.write("\n".join(chunk) + "\n")
            chunk, idx = [], idx + 1
    if chunk:
        with open(os.path.join(outdir, f"ann_{idx}.txt"), "w") as fh:
            fh.write("\n".join(chunk) + "\n")

    return 0


if __name__ == "__main__":
    sys.exit(main())
