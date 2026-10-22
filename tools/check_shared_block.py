#!/usr/bin/env python3
"""Check that the shared-definitions block of Challenge.lean is byte-identical to the block of
ArithmeticLorentz/Defs.lean.

The block runs from the line `-- BEGIN SHARED DEFINITIONS` to the line
`-- END SHARED DEFINITIONS`, both included. Each marker must occur exactly once, as a whole
line, in each file. No differences are allowed. Exit 0 if identical, 1 otherwise (with a diff).

Usage: python3 tools/check_shared_block.py [package-root]
"""
import difflib
import pathlib
import sys

BEGIN = b"-- BEGIN SHARED DEFINITIONS\n"
END = b"-- END SHARED DEFINITIONS\n"


def block(path: pathlib.Path) -> bytes:
    lines = path.read_bytes().splitlines(keepends=True)
    begins = [i for i, line in enumerate(lines) if line == BEGIN]
    ends = [i for i, line in enumerate(lines) if line == END]
    if len(begins) != 1 or len(ends) != 1 or begins[0] >= ends[0]:
        raise SystemExit(f"FAIL: {path}: expected exactly one BEGIN line before exactly one END "
                         f"line (found {len(begins)} BEGIN, {len(ends)} END)")
    return b"".join(lines[begins[0]:ends[0] + 1])


def main() -> int:
    root = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(__file__).resolve().parent.parent
    challenge = block(root / "Challenge.lean")
    defs = block(root / "ArithmeticLorentz" / "Defs.lean")
    if challenge == defs:
        n = challenge.count(b"\n")
        print(f"PASS: shared block identical in Challenge.lean and ArithmeticLorentz/Defs.lean "
              f"({n} lines, {len(challenge)} bytes)")
        return 0
    sys.stdout.writelines(difflib.unified_diff(
        defs.decode("utf-8", "replace").splitlines(keepends=True),
        challenge.decode("utf-8", "replace").splitlines(keepends=True),
        "ArithmeticLorentz/Defs.lean", "Challenge.lean"))
    print("FAIL: the shared blocks differ")
    return 1


if __name__ == "__main__":
    sys.exit(main())
