#!/usr/bin/env python3
"""Count gate (fails closed). Checks that
  (1) the theorems declared in namespace ArithmeticLorentz of Challenge.lean are exactly
      comparator.json's theorem_names, in order, and the same in Solution.lean;
  (2) the opening docstring states that count in words ("<Count> compared statements") and
      numbers the statements 1..N;
  (3) Challenge.lean has exactly one `sorry` per compared theorem and nothing else uses sorry;
  (4) Challenge.lean imports Mathlib only, and every .lean file starts with the module header;
  (5) Challenge.lean is within the registry caps (1,000 lines, 100 KiB);
  (6) formalization.yaml's alignment.statements list the same names, in order.
Exit 0 on PASS, 1 on any failure. Usage: python3 tools/check_count.py [package-root]
"""
import json
import pathlib
import re
import sys

WORDS = {1: "One", 2: "Two", 3: "Three", 4: "Four", 5: "Five", 6: "Six", 7: "Seven", 8: "Eight",
         9: "Nine", 10: "Ten", 11: "Eleven", 12: "Twelve", 13: "Thirteen", 14: "Fourteen",
         15: "Fifteen", 16: "Sixteen", 17: "Seventeen", 18: "Eighteen"}
HEADER = "module\npublic import Mathlib\n"
NS = "namespace ArithmeticLorentz"

root = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path(__file__).resolve().parent.parent
fails = []
ch = (root / "Challenge.lean").read_text()
so = (root / "Solution.lean").read_text()
names = json.loads((root / "comparator.json").read_text())["theorem_names"]


def declared(text):
    ns = text.split(NS, 1)
    return ["ArithmeticLorentz." + m for m in re.findall(r"^theorem (\S+)", ns[1], re.M)] if len(ns) == 2 else []


if declared(ch) != names:
    fails.append(f"Challenge compared theorems {declared(ch)} != comparator.json {names}")
if declared(so) != names:
    fails.append(f"Solution theorems {declared(so)} != comparator.json {names}")
doc = ch.split("-/", 1)[0]
word = WORDS.get(len(names), str(len(names)))
if f"{word} compared statements" not in doc:
    fails.append(f"opening docstring does not say '{word} compared statements'")
numbered = re.findall(r"^\s*(\d+)\. `(\w+)`", doc, re.M)
if [int(n) for n, _ in numbered] != list(range(1, len(names) + 1)) or \
        ["ArithmeticLorentz." + m for _, m in numbered] != names:
    fails.append(f"opening docstring numbers {numbered} do not match comparator.json")
ns = ch.split(NS, 1)
nsorry = len(re.findall(r"\bsorry\b", ns[1] if len(ns) == 2 else ""))
if nsorry != len(names) or len(re.findall(r"\bsorry\b", ns[0])) != 0:
    fails.append(f"sorry count {nsorry} in the statements (expected {len(names)}) or sorry before them")
imports = re.findall(r"^(?:public )?import (\S+)", ch, re.M)
if imports != ["Mathlib"]:
    fails.append(f"Challenge imports {imports}, expected Mathlib only")
for f in sorted(root.glob("**/*.lean")):
    if ".lake" in f.parts or "notes" in f.parts:
        continue
    t = f.read_text()
    if not t.startswith(HEADER) or "\n@[expose] public section\n" not in t.split("/-", 1)[0] + "\n":
        fails.append(f"{f.relative_to(root)}: module header")
    if f.name != "Challenge.lean" and re.search(r"\bsorry\b|native_decide|^axiom ", t, re.M):
        fails.append(f"{f.relative_to(root)}: sorry / native_decide / axiom")
nl, nb = ch.count("\n"), len(ch.encode())
if nl > 1000 or nb > 100 * 1024:
    fails.append(f"Challenge.lean over cap: {nl} lines, {nb} bytes")
yaml_names = re.findall(r'^\s*lean: "([^"]+)"', (root / "formalization.yaml").read_text(), re.M) \
    if (root / "formalization.yaml").exists() else None
if yaml_names is not None and yaml_names != names:
    fails.append(f"formalization.yaml alignment {yaml_names} != comparator.json")
if fails:
    print("FAIL:\n  " + "\n  ".join(fails))
    sys.exit(1)
print(f"PASS: {len(names)} compared statements; Challenge.lean {nl} lines, {nb} bytes; headers OK")
