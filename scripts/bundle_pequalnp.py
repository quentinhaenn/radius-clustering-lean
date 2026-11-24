#!/usr/bin/env python3
"""Bundle the proof of `PEqualNP.Outside.L_clust_npc` into the one file pequalnp's format asks for.

Follows the imports from `ClustNP.NPC` through `RadiusClustering/` and `pequalnp-bridge/ClustNP/`,
concatenates the modules in dependency order, each in its own `section`, inside
`namespace PEqualNP.Outside.L_clust_npc`, and puts the final theorem after it.
Usage: scripts/bundle_pequalnp.py OUT.lean
"""
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ROOTS = {"RadiusClustering": REPO / "RadiusClustering", "ClustNP": REPO / "pequalnp-bridge" / "ClustNP"}
NS = "PEqualNP.Outside.L_clust_npc"
FINAL = "/-- The candidate statement for pequalnp"


def path_of(mod: str) -> Path | None:
    head, *rest = mod.split(".")
    if head not in ROOTS:
        return None
    return ROOTS[head].joinpath(*rest).with_suffix(".lean")


order: list[str] = []
external: list[str] = []


def visit(mod: str, seen: set[str]) -> None:
    if mod in seen:
        return
    seen.add(mod)
    for line in path_of(mod).read_text().splitlines():
        m = re.match(r"^import (\S+)$", line)
        if not m:
            continue
        dep = m.group(1)
        if path_of(dep) is None:
            if dep not in external:
                external.append(dep)
        else:
            visit(dep, seen)
    order.append(mod)


visit("ClustNP.NPC", set())

body: list[str] = []
final = ""
for mod in order:
    text = "\n".join(l for l in path_of(mod).read_text().splitlines() if not l.startswith("import "))
    if mod == "ClustNP.NPC":
        text, final = text.split(FINAL)
        final = FINAL + final
    sec = "M_" + mod.replace(".", "_")
    body.append(f"section {sec}\n{text.strip()}\n\nend {sec}\n")

# `RadiusClustering.PEqualNP` would repeat `PEqualNP` inside the outer namespace.
body = [b.replace("RadiusClustering.PEqualNP", "RadiusClustering.Clust") for b in body]
final = final.replace("RadiusClustering.PEqualNP", "RadiusClustering.Clust")
final = final.replace("ClustNP.clustLang_npComplete", f"{NS}.ClustNP.clustLang_npComplete")
final = final.replace("RadiusClustering.Clust.clustLang_eq_inline",
                      f"{NS}.RadiusClustering.Clust.clustLang_eq_inline")



def strip_comments(src: str) -> str:
    """Drop `--` and (nested) `/- -/` comments; the sources have no string literals once the
    notations are gone."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if src.startswith("--", i):
            while i < len(src) and src[i] != "\n":
                i += 1
            continue
        out.append(src[i]); i += 1
    return "".join(out)


def plain(src: str) -> str:
    """pequalnp's plain-file rules: no notation, no option but the four limits, no comment."""
    src = "\n".join(l for l in src.splitlines()
                    if not l.startswith("local notation") and "set_option linter" not in l)
    src = re.sub(r"\(Dg (\w+'?)\)", r"(List.flatMap (fun d => [true, d]) \1)", src)
    src = re.sub(r"\bCPTs\b",
                 "(ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x))", src)
    src = strip_comments(src)
    src = "\n".join(l.rstrip() for l in src.splitlines())
    return re.sub(r"\n{3,}", "\n\n", src)


body = [plain(b) for b in body]
final = plain(final)
header = "\n".join(f"import {m}" for m in external)
out = f"""{header}

namespace {NS}

{chr(10).join(body)}
end {NS}

{final.strip()}
"""
Path(sys.argv[1]).write_text(out)
print(f"{len(order)} modules, {len(out.splitlines())} lines, imports: {external}")
