#!/usr/bin/env python3
"""Prune ubiquitous dead private Mathlib imports injected by Fast Shake (e2d63d2539).

Root cause
----------
In Lean `v4.37.0-rc1`, `Lake/CLI/Shake.lean` unconditionally preserves every module in
`transDepsOrig` that called `Lean.recordExtraRevUseOfCurrentModule` as a private
`import`.  Four Mathlib tactic registries call `recordExtraRevUseOfCurrentModule`:

  1. `Mathlib/Tactic/Positivity/Core.lean`        (`@[positivity]`)
  2. `Mathlib/Tactic/NormNum/Core.lean`           (`@[norm_num]`)
  3. `Mathlib/Tactic/Inclusion/Core/DiscrTreeExt.lean` (`@[inclusion_*]`, `@[hypothesis_*]`)
  4. `Mathlib/Tactic/Echelon/Core.lean`           (`@[bareiss_ext]`)

Because files originally imported all of `Mathlib`, commit `e2d63d2539` left the
maximal-leaf antichain of those registries (plus linter/simp-set leaves) in up to 99.9%
of files (~2.43M lines across 62k files), pulling ~3,134-3,364 Mathlib `.olean` modules
into every `lean` process.

Tiers
-----
  - `core-32` : 32 imports present in >= 97% of files (~1.99M lines)
  - `top-34`  : `core-32` + `Height.NumberField` (3,153 transitive mods) & `UpperHalfPlane.Basic`
  - `ext-47`  : `top-34` + 13 remaining Fast-Shake tactic/linter/simp-set leaves (~2.43M lines, default)
  - `all-48`  : `ext-47` + `Mathlib.Tactic.TypeStar` (only when body uses neither `Type*` nor `Sort*`)
  - `custom`  : module names loaded from `--custom-imports <file>`

Safety & verification
---------------------
  - Only private `import` lines in the file header are candidates; `public import`,
    `import all`, and `meta import` lines are never removed.
  - `PROTECTED_LIBS` (`Main`, `Challenge`) are skipped by default, and the six frozen
    Comparator challenge files are never modified even with `--include-protected`.
  - Because `e2d63d2539` transitively dropped smaller private Mathlib imports covered by
    heavy leaves (such as `Height.NumberField` or `Volume.Basic`), `--verify` compiles
    each candidate with `lean` (using `lakefile.toml` options) and guarantees 0 errors
    (and 0 new warnings with `--check-warnings`).  On failure it tries:
      1. Targeted replacement of missing named symbols from `.lake/packages/mathlib`.
      2. Closure-size-ordered binary-search (`ddmin`) restoration of the minimal subset.
      3. Unchanged fallback if verification still fails.

Usage
-----
    python3 scripts/prune_mathlib_imports.py --dry-run
    python3 scripts/prune_mathlib_imports.py --dir src/Formalism --tier ext-47 \\
        --verify --check-warnings --jobs 4 --apply
    python3 scripts/prune_mathlib_imports.py --paths src/Foo.lean \\
        --verify --out-dir out/ --apply
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

# ---------------------------------------------------------------------------
# Candidate catalog: (module_name, approx_transitive_mathlib_mods, category, guard_regex)

TIER_CORE_32 = [
    ("Mathlib.Algebra.Order.Floor.Extended", 787, "positivity_ext", None),
    ("Mathlib.Algebra.Order.Interval.Basic", 477, "positivity_ext", None),
    ("Mathlib.Combinatorics.Enumerative.DyckWord", 641, "positivity_ext", None),
    ("Mathlib.Combinatorics.SimpleGraph.Triangle.Removal", 1754, "positivity_ext", None),
    ("Mathlib.Data.NNRat.Floor", 482, "norm_num_ext", None),
    ("Mathlib.Geometry.Euclidean.Volume.Basic", 2500, "positivity_ext", None),
    ("Mathlib.NumberTheory.Height.Projectivization", 1738, "positivity_ext", None),
    ("Mathlib.NumberTheory.LucasLehmer", 2554, "positivity_ext", None),
    ("Mathlib.NumberTheory.SelbergSieve", 838, "positivity_ext", None),
    ("Mathlib.RingTheory.Radical.NatInt", 1053, "positivity_ext", None),
    ("Mathlib.Tactic.Echelon.Zsqrtd", 1048, "echelon_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.Core.Core", 132, "inclusion_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit", 131, "inclusion_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp", 1207, "inclusion_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses", 453, "inclusion_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic", 330, "inclusion_ext", None),
    ("Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses", 328, "inclusion_ext", None),
    ("Mathlib.Tactic.NormNum.Irrational", 1801, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.IsCoprime", 564, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.IsSquare", 420, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.LegendreSymbol", 2552, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.ModEq", 353, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.NatFib", 553, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.NatLog", 419, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.NatSqrt", 418, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.Ordinal", 562, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.Prime", 223, "norm_num_ext", None),
    ("Mathlib.Tactic.NormNum.RealSqrt", 1160, "norm_num_ext", None),
    ("Mathlib.Algebra.Order.Floor.Semifield", 454, "norm_num_ext", None),
    ("Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp", 1824, "positivity_ext", None),
    ("Mathlib.NumberTheory.Chebyshev", 2493, "positivity_ext", None),
    ("Mathlib.Tactic.NormNum.Parity", 208, "norm_num_ext", None),
]

TIER_TOP_34_EXTRA = [
    ("Mathlib.NumberTheory.Height.NumberField", 3153, "positivity_ext", None),
    ("Mathlib.Analysis.Complex.UpperHalfPlane.Basic", 1525, "positivity_ext", None),
]

TIER_EXT_47_EXTRA = [
    ("Mathlib.Analysis.Normed.Algebra.GelfandRadius", 1682, "positivity_ext", None),
    ("Mathlib.Topology.Sheaves.Init", 2, "aesop_ruleset", None),
    ("Mathlib.Data.Nat.Choose.Multinomial", 900, "positivity_ext", None),
    ("Mathlib.Analysis.SpecialFunctions.Bernstein", 1500, "positivity_ext", None),
    ("Mathlib.Analysis.SpecialFunctions.Gamma.Basic", 1800, "positivity_ext", None),
    ("Mathlib.Tactic.ReduceModChar", 600, "tactic_ext", None),
    ("Mathlib.Tactic.Basify", 200, "tactic_ext", None),
    ("Mathlib.Tactic.Linter.Style", 50, "linter", None),
    ("Mathlib.Tactic.Polynomial.Basic", 500, "tactic_ext", None),
    ("Mathlib.Tactic.ENatToNat", 250, "tactic_ext", None),
    ("Mathlib.RingTheory.WittVector.IsPoly", 1606, "tactic_ext", None),
    ("Mathlib.Tactic.Linter.HaveILetI", 30, "linter", None),
    ("Std.Tactic.BVDecide.Normalize.Prop", 20, "tactic_ext", None),
]

TIER_ALL_48_EXTRA = [
    ("Mathlib.Tactic.TypeStar", 10, "syntax", r"\b(?:Type|Sort)\*"),
]

# Conservative keyword guards enabled only when --strict-static is requested.
STRICT_STATIC_GUARDS = {
    "Mathlib.Tactic.NormNum.Parity": (r"\bnorm_num\b", r"\b(?:Even|Odd)\b"),
    "Mathlib.Tactic.NormNum.Prime": (r"\bnorm_num\b", r"\b(?:Prime|minFac)\b"),
    "Mathlib.Tactic.NormNum.IsSquare": (r"\bnorm_num\b", r"\bIsSquare\b"),
    "Mathlib.Tactic.NormNum.IsCoprime": (r"\bnorm_num\b", r"\bIsCoprime\b"),
    "Mathlib.Tactic.NormNum.ModEq": (r"\bnorm_num\b", r"≡|ModEq"),
    "Mathlib.Tactic.NormNum.RealSqrt": (r"\bnorm_num\b", r"√|Real\.sqrt|NNReal\.sqrt"),
    "Mathlib.Tactic.NormNum.NatSqrt": (r"\bnorm_num\b", r"Nat\.sqrt"),
    "Mathlib.Tactic.NormNum.NatLog": (r"\bnorm_num\b", r"Nat\.log|Nat\.clog"),
    "Mathlib.Tactic.NormNum.NatFib": (r"\bnorm_num\b", r"Nat\.fib"),
    "Mathlib.Tactic.NormNum.Ordinal": (r"\bnorm_num\b", r"\bOrdinal\b"),
    "Mathlib.Tactic.NormNum.Irrational": (r"\bnorm_num\b", r"\bIrrational\b"),
    "Mathlib.Tactic.NormNum.LegendreSymbol": (r"\bnorm_num\b", r"legendreSym|jacobiSym"),
    "Mathlib.Algebra.Order.Floor.Semifield": (r"\bnorm_num\b", r"⌊|Nat\.floor"),
    "Mathlib.Data.NNRat.Floor": (r"\bnorm_num\b", r"⌈|Nat\.ceil"),
    "Mathlib.Analysis.Complex.UpperHalfPlane.Basic": (r"\bUpperHalfPlane\b",),
    "Mathlib.RingTheory.WittVector.IsPoly": (r"\bWittVector\b|\bghost_simps\b",),
    "Mathlib.Analysis.SpecialFunctions.Gamma.Basic": (r"\bGamma\b",),
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp": (r"\bsinh\b|\bcosh\b|\btanh\b",),
    "Mathlib.Tactic.ReduceModChar": (r"\breduce_mod_char\b",),
    "Mathlib.Tactic.Basify": (r"\bbasify\b",),
    "Mathlib.Tactic.ENatToNat": (r"\benat_to_nat\b",),
    "Mathlib.Tactic.Polynomial.Basic": (r"\bpolynomial\b",),
    "Mathlib.Topology.Sheaves.Init": (r"\baesop\b|\bRestrict\b",),
    "Mathlib.Tactic.TypeStar": (r"\b(?:Type|Sort)\*",),
}

PROTECTED_LIBS = frozenset({"Main", "Challenge"})

# The six frozen Comparator challenge files (.github/workflows/challenge-files.yml).
# Never modified even when --include-protected is passed.
FROZEN_CHALLENGE_FILES = frozenset({
    "src/Challenge.lean",
    "comparator.json",
    "export-targets.txt",
    "comparator/FormalConjecturesChallenge.lean",
    "comparator/formal-conjectures.json",
    "comparator/formal-conjectures-export-targets.txt",
})

MODULE_RE = re.compile(r"^module(?:\s*--.*)?$")
IMPORT_RE = re.compile(
    r"^((?:(?:public|private|meta)\s+)*)import\s+((?:all\s+)?)([^\s]+?)(?:\s*--.*)?$"
)
MISSING_ENV_RE = re.compile(r"The environment does not contain `([^`]+)`")
UNKNOWN_ID_RE = re.compile(r"unknown (?:identifier|constant) [`']([^`']+)[`']")


def load_module_list(path: str) -> list[str]:
    """Read newline-delimited module names or paths, ignoring blank lines and `#` comments."""
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            s = line.split("#", 1)[0].strip()
            if s:
                out.append(s)
    return out


def build_tier_catalog(tier: str, custom_imports_path: str | None = None):
    """Return ordered list of candidate tuples for `tier`."""
    if tier == "custom":
        if not custom_imports_path:
            raise ValueError("--custom-imports is required when --tier custom is selected")
        return [(m, 1000, "custom", None) for m in dict.fromkeys(load_module_list(custom_imports_path))]
    entries = list(TIER_CORE_32)
    if tier in ("top-34", "ext-47", "all-48"):
        entries.extend(TIER_TOP_34_EXTRA)
    if tier in ("ext-47", "all-48"):
        entries.extend(TIER_EXT_47_EXTRA)
    if tier == "all-48":
        entries.extend(TIER_ALL_48_EXTRA)
    return entries


def lib_of(mod: str) -> str:
    """Return the Lake library a module belongs to (mirrors lakefile.toml)."""
    if mod in ("Statements", "Main"):
        return "Main"
    if mod == "Challenge":
        return "Challenge"
    parts = mod.split(".")
    if parts[0] == "GroundTheory" and len(parts) > 1 and parts[1] in ("LocalFields", "GlobalFields"):
        return "GroundTheoryFields"
    return parts[0]


def norm_rel_path(root: str, path: str) -> str:
    return os.path.relpath(os.path.abspath(path), os.path.abspath(root)).replace(os.sep, "/")


def is_frozen_challenge_file(root: str, path: str) -> bool:
    return norm_rel_path(root, path) in FROZEN_CHALLENGE_FILES


def path_to_mod(root: str, path: str) -> str:
    src_root = os.path.join(os.path.abspath(root), "src")
    rel = os.path.relpath(os.path.abspath(path), src_root)
    if rel.endswith(".lean"):
        rel = rel[:-5]
    return rel.replace(os.sep, ".")


def split_header_body(text: str):
    """Split a Lean source file into `(header_lines, body_text, parsed_imports)`.

    `parsed_imports` is a list of `(line_idx, module_name, is_public, is_exotic)`.
    Handles standalone `--` comments, trailing `--` comments on `module`/`import` lines,
    and multi-line `/- ... -/` block comments in the header.
    """
    lines = text.splitlines(keepends=True)
    imports = []
    header_end = len(lines)
    in_block = 0
    for i, line in enumerate(lines):
        s = line.strip()
        if in_block > 0:
            in_block += s.count("/-") - s.count("-/")
            continue
        if s == "" or s.startswith("--") or MODULE_RE.match(s):
            continue
        if s.startswith("/-"):
            in_block += s.count("/-") - s.count("-/")
            continue
        m = IMPORT_RE.match(s)
        if m:
            mods = m.group(1).split()
            is_public = "public" in mods
            is_exotic = bool(m.group(2)) or ("meta" in mods)
            imports.append((i, m.group(3), is_public, is_exotic))
            continue
        header_end = i
        break
    return lines[:header_end], "".join(lines[header_end:]), imports


def load_exclude(path: str | None) -> set[str]:
    if not path:
        return set()
    return set(load_module_list(path))


# ---------------------------------------------------------------------------
# Mathlib import graph & lazy symbol lookup (for stats & smart repair)

class MathlibIndex:
    """Lazy Mathlib public-import closure & symbol index over `.lake/packages/mathlib`."""

    def __init__(self, root: str):
        self.mathlib_dir = os.path.join(root, ".lake", "packages", "mathlib")
        self._closure_size: dict[str, int] | None = None
        self._m_idx: dict[str, int] | None = None
        self._m_bits: dict[str, int] | None = None

    def available(self) -> bool:
        return os.path.isdir(os.path.join(self.mathlib_dir, "Mathlib"))

    def ensure_graph(self):
        if self._m_bits is not None:
            return
        mdeps: dict[str, list[str]] = {}
        mdir = os.path.join(self.mathlib_dir, "Mathlib")
        for r, _, files in os.walk(mdir):
            for f in files:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(r, f)
                mod = os.path.relpath(p, self.mathlib_dir)[:-5].replace(os.sep, ".")
                pubs = []
                with open(p, encoding="utf-8", errors="replace") as fh:
                    in_block = 0
                    is_module = False
                    for line in fh:
                        s = line.strip()
                        if in_block > 0:
                            in_block += s.count("/-") - s.count("-/")
                            continue
                        if s.startswith("/-"):
                            in_block += s.count("/-") - s.count("-/")
                            continue
                        if MODULE_RE.match(s):
                            is_module = True
                            continue
                        mm = IMPORT_RE.match(s)
                        if mm:
                            if (not is_module) or ("public" in mm.group(1).split()):
                                dep = mm.group(3)
                                if dep.startswith("Mathlib."):
                                    pubs.append(dep)
                        elif s and not s.startswith("--"):
                            break
                mdeps[mod] = pubs
        mdeps["Mathlib"] = list(mdeps.keys())
        m_list = sorted(mdeps.keys())
        m_idx = {m: i for i, m in enumerate(m_list)}
        m_bits: dict[str, int] = {}

        for start in m_list:
            if start in m_bits:
                continue
            stack = [(start, 0)]
            in_prog = set()
            while stack:
                node, phase = stack.pop()
                if node in m_bits:
                    continue
                if phase == 0:
                    if node in in_prog:
                        continue
                    in_prog.add(node)
                    stack.append((node, 1))
                    for d in mdeps.get(node, ()):
                        if d in m_idx and d not in m_bits and d not in in_prog:
                            stack.append((d, 0))
                else:
                    b = 1 << m_idx[node]
                    for d in mdeps.get(node, ()):
                        if d in m_bits:
                            b |= m_bits[d]
                    m_bits[node] = b
                    in_prog.discard(node)

        self._m_idx = m_idx
        self._m_bits = m_bits
        self._closure_size = {m: b.bit_count() for m, b in m_bits.items()}

    def closure_size(self, mod: str, fallback: int = 1000) -> int:
        if self._closure_size is not None and mod in self._closure_size:
            return self._closure_size[mod]
        return fallback

    def module_bits(self, mod: str) -> int:
        self.ensure_graph()
        return self._m_bits.get(mod, 0) if self._m_bits is not None else 0

    def find_defining_modules(self, ident: str, max_results: int = 5) -> list[str]:
        """Find small Mathlib modules declaring `ident` (supports dotted names)."""
        if not self.available():
            return []
        self.ensure_graph()
        short = ident.split(".")[-1]
        pat = (
            rf"\b(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)"
            rf"\s+(?:[A-Za-z0-9_']+\.)*{re.escape(short)}\b"
        )
        if "." in ident:
            full_pat = (
                rf"\b(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)"
                rf"\s+(?:[A-Za-z0-9_']+\.)*{re.escape(ident)}\b"
            )
            regexes = [full_pat, pat]
        else:
            regexes = [pat]

        mdir = os.path.join(self.mathlib_dir, "Mathlib")
        matches: list[str] = []
        rg_bin = shutil.which("rg")
        if rg_bin:
            for regex in regexes:
                proc = subprocess.run(
                    [rg_bin, "-l", "-e", regex, mdir],
                    capture_output=True, text=True, check=False,
                )
                for p in proc.stdout.splitlines():
                    if p.endswith(".lean"):
                        mod = os.path.relpath(p, self.mathlib_dir)[:-5].replace(os.sep, ".")
                        if mod not in matches:
                            matches.append(mod)
                if matches:
                    break
        else:
            for regex in regexes:
                rx = re.compile(regex)
                for r, _, files in os.walk(mdir):
                    for f in files:
                        if not f.endswith(".lean"):
                            continue
                        p = os.path.join(r, f)
                        with open(p, encoding="utf-8", errors="replace") as fh:
                            if rx.search(fh.read()):
                                mod = os.path.relpath(p, self.mathlib_dir)[:-5].replace(os.sep, ".")
                                if mod not in matches:
                                    matches.append(mod)
                if matches:
                    break

        matches.sort(key=lambda m: (self.closure_size(m, 9999), m))
        return matches[:max_results]


# ---------------------------------------------------------------------------
# Repo-wide public-cone Mathlib estimator (for --min-module-drop & stats)

def compute_repo_public_mathlib_bits(root: str, mindex: MathlibIndex):
    """Compute transitive public-import Mathlib bitsets for all local modules in `src/`."""
    mindex.ensure_graph()
    src_dir = os.path.join(root, "src")
    l_pub: dict[str, list[str]] = {}
    l_priv: dict[str, list[str]] = {}
    for r, _, files in os.walk(src_dir):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(r, f)
            mod = os.path.relpath(p, src_dir)[:-5].replace(os.sep, ".")
            pubs, privs = [], []
            with open(p, encoding="utf-8", errors="replace") as fh:
                in_block = 0
                for line in fh:
                    s = line.strip()
                    if in_block > 0:
                        in_block += s.count("/-") - s.count("-/")
                        continue
                    if s.startswith("/-"):
                        in_block += s.count("/-") - s.count("-/")
                        continue
                    if s == "" or s.startswith("--") or MODULE_RE.match(s):
                        continue
                    mm = IMPORT_RE.match(s)
                    if mm:
                        dep = mm.group(3)
                        if "public" in mm.group(1).split():
                            pubs.append(dep)
                        else:
                            privs.append(dep)
                    else:
                        break
            l_pub[mod] = pubs
            l_priv[mod] = privs

    pub_bits: dict[str, int] = {}
    for start in l_pub:
        if start in pub_bits:
            continue
        stack = [(start, 0)]
        in_prog = set()
        while stack:
            node, phase = stack.pop()
            if node in pub_bits:
                continue
            if phase == 0:
                if node in in_prog:
                    continue
                in_prog.add(node)
                stack.append((node, 1))
                for d in l_pub.get(node, ()):
                    if d in l_pub and d not in pub_bits and d not in in_prog:
                        stack.append((d, 0))
            else:
                b = 0
                for d in l_pub.get(node, ()):
                    if d in l_pub:
                        b |= pub_bits.get(d, 0)
                    else:
                        b |= mindex.module_bits(d)
                pub_bits[node] = b
                in_prog.discard(node)
    return l_pub, l_priv, pub_bits


def estimate_module_drop(mod: str, removed_mods, added_mods, l_priv, pub_bits, mindex: MathlibIndex):
    """Return `(before_mathlib_mods, after_mathlib_mods, drop)` for `mod`."""
    if mod not in pub_bits:
        return None, None, None
    base = pub_bits[mod]
    removed_set = set(removed_mods)
    priv_local = 0
    priv_m_orig = 0
    priv_m_new = 0
    for d in l_priv.get(mod, ()):
        if d in pub_bits:
            priv_local |= pub_bits[d]
        else:
            mb = mindex.module_bits(d)
            priv_m_orig |= mb
            if d not in removed_set:
                priv_m_new |= mb
    for d in added_mods:
        priv_m_new |= mindex.module_bits(d)
    before = (base | priv_local | priv_m_orig).bit_count()
    after = (base | priv_local | priv_m_new).bit_count()
    return before, after, before - after


# ---------------------------------------------------------------------------
# Pruning & Lean verification engine

def strip_clump_header_comments(body_text: str) -> str:
    """Remove `-- clump-header: ...` JSON lines so embedded old imports never trip static guards."""
    if "-- clump-header:" not in body_text:
        return body_text
    return "\n".join(
        l for l in body_text.splitlines() if not l.lstrip().startswith("-- clump-header:")
    )


def candidate_removals_for_file(text: str, catalog_map, strict_static: bool):
    """Return `(header_lines, body_text, removable_indices, removable_mods)` for a file."""
    header_lines, body_text, parsed_imports = split_header_body(text)
    scan_body = strip_clump_header_comments(body_text)
    removable_indices = []
    removable_mods = []
    for idx, mod, is_public, is_exotic in parsed_imports:
        if is_public or is_exotic:
            continue
        if mod not in catalog_map:
            continue
        _weight, _cat, mandatory_guard = catalog_map[mod]
        if mandatory_guard and re.search(mandatory_guard, scan_body):
            continue
        if strict_static and mod in STRICT_STATIC_GUARDS:
            pats = STRICT_STATIC_GUARDS[mod]
            if all(re.search(p, scan_body) for p in pats):
                continue
        removable_indices.append(idx)
        removable_mods.append(mod)
    return header_lines, body_text, removable_indices, removable_mods


def detect_newline(header_lines, body_text: str) -> str:
    for line in header_lines:
        if line.endswith("\r\n"):
            return "\r\n"
        if line.endswith("\n"):
            return "\n"
    return "\r\n" if "\r\n" in body_text else "\n"


def render_source(header_lines, body_text: str, drop_indices, extra_imports=()) -> str:
    """Render Lean source dropping `drop_indices` and inserting `extra_imports` cleanly."""
    drop_set = set(drop_indices)
    out_header = [l for i, l in enumerate(header_lines) if i not in drop_set]
    if extra_imports:
        nl = detect_newline(header_lines, body_text)
        insert_at = 0
        existing = set()
        for i, l in enumerate(out_header):
            s = l.strip()
            mm = IMPORT_RE.match(s)
            if MODULE_RE.match(s) or mm:
                insert_at = i + 1
            if mm:
                existing.add(mm.group(3))
        new_lines = [f"import {m}{nl}" for m in sorted(set(extra_imports)) if m not in existing]
        if new_lines and insert_at > 0 and not out_header[insert_at - 1].endswith(("\n", "\r\n")):
            out_header[insert_at - 1] += nl
        out_header = out_header[:insert_at] + new_lines + out_header[insert_at:]
    return "".join(out_header) + body_text


def get_lean_env(root: str) -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan_bin) and elan_bin not in env.get("PATH", "").split(os.pathsep):
        env["PATH"] = elan_bin + os.pathsep + env.get("PATH", "")
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=root, env=env, text=True
    ).strip()
    env["LEAN_PATH"] = lean_path
    return env


def build_lean_cmd(tmp_root: str, dst: str, mod_name: str) -> list[str]:
    """Construct the exact `lean` invocation matching `lakefile.toml` options."""
    cmd = [
        "lean",
        f"--root={tmp_root}",
        "-DautoImplicit=false",
        "-DrelaxedAutoImplicit=false",
        "-DmaxSynthPendingDepth=3",
        "-Dpp.unicode.fun=true",
        "-DmaxHeartbeats=4000000",
        "--tstack=400000",
    ]
    if lib_of(mod_name) == "GroundTheoryFields":
        cmd.append("-DsynthInstance.maxHeartbeats=400000")
    cmd.append(dst)
    return cmd


def run_lean_check(text: str, rel_path: str, mod_name: str, env, tmp_root: str):
    """Write `text` to `tmp_root/rel_path` and typecheck with `lakefile.toml` options."""
    dst = os.path.join(tmp_root, rel_path)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    with open(dst, "w", encoding="utf-8", newline="") as fh:
        fh.write(text)
    cmd = build_lean_cmd(tmp_root, dst, mod_name)
    t0 = time.monotonic()
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    dt = time.monotonic() - t0
    combined = (proc.stdout + "\n" + proc.stderr).strip()
    warnings = [l for l in combined.splitlines() if ": warning:" in l]
    errors = [l for l in combined.splitlines() if ": error" in l]
    return proc.returncode, dt, warnings, errors, combined


def verify_and_repair(
    orig_text: str,
    header_lines,
    body_text: str,
    removable_indices,
    removable_mods,
    rel_path: str,
    mod_name: str,
    env,
    mindex: MathlibIndex,
    catalog_map,
    check_warnings: bool,
    smart_replace: bool,
    max_restore: int,
    runner=None,
):
    """Verify pruned source; auto-repair via targeted replacement or ddmin binary search."""
    check_fn = runner if runner is not None else run_lean_check
    tmp_root = tempfile.mkdtemp(prefix="prune_mathlib_")
    lean_calls = 0
    dt_total = 0.0
    warn_before = None

    try:
        def ok_result(rc: int, warns) -> bool:
            if rc != 0:
                return False
            if check_warnings and warn_before is not None and len(warns) > warn_before:
                return False
            return True

        if check_warnings:
            rc0, dt0, w0, _, _ = check_fn(orig_text, rel_path, mod_name, env, tmp_root)
            lean_calls += 1
            dt_total += dt0
            if rc0 != 0:
                return {
                    "status": "unchanged",
                    "reason": "baseline_failed",
                    "final_text": orig_text,
                    "removed_mods": [],
                    "restored_mods": list(removable_mods),
                    "added_mods": [],
                    "lean_calls": lean_calls,
                    "dt_total": dt_total,
                    "warn_before": len(w0),
                    "warn_after": len(w0),
                }
            warn_before = len(w0)

        # Attempt 0: drop all candidate removable imports
        pruned_text = render_source(header_lines, body_text, removable_indices)
        rc, dt, warns, _errs, full_out = check_fn(pruned_text, rel_path, mod_name, env, tmp_root)
        lean_calls += 1
        dt_total += dt
        if ok_result(rc, warns):
            return {
                "status": "passed",
                "reason": "clean_full_prune",
                "final_text": pruned_text,
                "removed_mods": list(removable_mods),
                "restored_mods": [],
                "added_mods": [],
                "lean_calls": lean_calls,
                "dt_total": dt_total,
                "warn_before": warn_before,
                "warn_after": len(warns),
            }

        # Stage 1: Targeted tiny-import replacement for missing named symbols/fields
        if smart_replace and rc != 0 and mindex.available():
            missing_idents = []
            for rx in (MISSING_ENV_RE, UNKNOWN_ID_RE):
                for mm in rx.finditer(full_out):
                    ident = mm.group(1)
                    if ident not in missing_idents:
                        missing_idents.append(ident)
            if missing_idents and len(missing_idents) <= 4:
                candidate_adds = []
                for ident in missing_idents:
                    mods = mindex.find_defining_modules(ident, max_results=2)
                    if mods:
                        candidate_adds.append(mods[0])
                if candidate_adds:
                    repaired_text = render_source(
                        header_lines, body_text, removable_indices, extra_imports=candidate_adds
                    )
                    rc2, dt2, w2, _, _ = check_fn(repaired_text, rel_path, mod_name, env, tmp_root)
                    lean_calls += 1
                    dt_total += dt2
                    if ok_result(rc2, w2):
                        return {
                            "status": "repaired",
                            "reason": "smart_symbol_replace",
                            "final_text": repaired_text,
                            "removed_mods": list(removable_mods),
                            "restored_mods": [],
                            "added_mods": sorted(set(candidate_adds)),
                            "lean_calls": lean_calls,
                            "dt_total": dt_total,
                            "warn_before": warn_before,
                            "warn_after": len(w2),
                        }

        # Stage 2: Closure-size-ordered binary-search (ddmin) restoration over removed imports
        pairs = list(zip(removable_indices, removable_mods))
        pairs.sort(key=lambda im: (mindex.closure_size(im[1], catalog_map[im[1]][0]), im[1]))

        restored = []
        pool = list(pairs)

        def check_keep(keep_pairs):
            nonlocal lean_calls, dt_total
            keep_idx = {i for i, _ in keep_pairs}
            drop_idx = [i for i in removable_indices if i not in keep_idx]
            txt = render_source(header_lines, body_text, drop_idx)
            rci, dti, wi, _, _ = check_fn(txt, rel_path, mod_name, env, tmp_root)
            lean_calls += 1
            dt_total += dti
            return ok_result(rci, wi), txt, wi

        final_text = None
        final_warns = None
        while len(restored) < max_restore and pool:
            if not restored:
                ok_all, _, _ = check_keep(pool)
                if not ok_all:
                    break
            lo, hi = 0, len(pool)
            while hi - lo > 1:
                mid = (lo + hi) // 2
                ok_mid, _, _ = check_keep(restored + pool[:mid])
                if ok_mid:
                    hi = mid
                else:
                    lo = mid
            restored.append(pool[lo])
            pool = pool[:lo]
            ok_now, txt_now, w_now = check_keep(restored)
            if ok_now:
                final_text = txt_now
                final_warns = w_now
                break

        if final_text is not None and len(restored) < len(removable_indices):
            restored_set = {m for _, m in restored}
            return {
                "status": "repaired",
                "reason": "ddmin_restore",
                "final_text": final_text,
                "removed_mods": [m for m in removable_mods if m not in restored_set],
                "restored_mods": sorted(restored_set),
                "added_mods": [],
                "lean_calls": lean_calls,
                "dt_total": dt_total,
                "warn_before": warn_before,
                "warn_after": len(final_warns) if final_warns is not None else None,
            }

        return {
            "status": "unchanged",
            "reason": "repair_failed_or_full_restore",
            "final_text": orig_text,
            "removed_mods": [],
            "restored_mods": list(removable_mods),
            "added_mods": [],
            "lean_calls": lean_calls,
            "dt_total": dt_total,
            "warn_before": warn_before,
            "warn_after": warn_before,
        }
    finally:
        shutil.rmtree(tmp_root, ignore_errors=True)


# ---------------------------------------------------------------------------
# File discovery & CLI

def discover_files(args) -> list[str]:
    root = os.path.abspath(args.root)
    src_dir = os.path.join(root, "src")
    files = []
    if args.paths:
        for p in args.paths:
            ap = os.path.abspath(p) if os.path.isabs(p) else os.path.abspath(os.path.join(root, p))
            if os.path.isfile(ap) and ap.endswith(".lean"):
                files.append(ap)
    elif args.file_list:
        for s in load_module_list(args.file_list):
            if s.endswith(".lean"):
                p = os.path.join(root, s) if not os.path.isabs(s) else s
            else:
                p = os.path.join(src_dir, s.replace(".", os.sep) + ".lean")
            if os.path.isfile(p):
                files.append(p)
    else:
        if args.dir:
            walk_root = (
                os.path.abspath(args.dir)
                if os.path.isabs(args.dir)
                else os.path.abspath(os.path.join(root, args.dir))
            )
        else:
            walk_root = src_dir
        for r, _, fnames in os.walk(walk_root):
            for f in sorted(fnames):
                if f.endswith(".lean"):
                    files.append(os.path.join(r, f))
    return sorted(dict.fromkeys(files))


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Prune ubiquitous dead private Mathlib imports injected by Fast Shake (e2d63d2539)."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: current directory)")
    ap.add_argument("--paths", nargs="+", help="Explicit .lean file paths to process")
    ap.add_argument("--dir", help="Subdirectory under src/ to scan")
    ap.add_argument("--file-list", help="Text file listing module names or .lean paths (one per line)")
    ap.add_argument("--exclude", help="File of excluded module names or relative paths (one per line)")
    ap.add_argument(
        "--tier",
        choices=("core-32", "top-34", "ext-47", "all-48", "custom"),
        default="ext-47",
        help="Candidate ubiquitous import tier (default: ext-47)",
    )
    ap.add_argument(
        "--custom-imports",
        help="File listing custom candidate module names (required with --tier custom)",
    )
    ap.add_argument(
        "--strict-static",
        action="store_true",
        help="Apply conservative static keyword guards before pruning",
    )
    ap.add_argument(
        "--min-module-drop",
        type=int,
        default=0,
        help="Only modify files whose estimated transitive Mathlib closure drops by >= N modules",
    )
    ap.add_argument("--include-protected", action="store_true", help="Allow Main/Statements (never frozen challenge files)")
    ap.add_argument("--verify", action="store_true", help="Typecheck each modified file with `lean` and auto-repair")
    ap.add_argument("--check-warnings", action="store_true", help="With --verify, require 0 new warnings vs baseline")
    ap.add_argument("--no-smart-replace", action="store_true", help="Disable targeted symbol-lookup replacement in --verify")
    ap.add_argument("--max-restore", type=int, default=4, help="Max imports ddmin may restore per file (default: 4)")
    ap.add_argument("--jobs", type=int, default=1, help="Parallel verification workers (default: 1)")
    ap.add_argument("--dry-run", action="store_true", help="Compute stats only; do not write files (default if --apply omitted)")
    ap.add_argument("--apply", action="store_true", help="Write pruned files (in-place, or into --out-dir)")
    ap.add_argument("--out-dir", help="Write pruned files into this mirror root instead of modifying src/ in-place")
    ap.add_argument("--stats-closure", action="store_true", help="Compute exact transitive Mathlib module drop stats")
    ap.add_argument("--json-report", help="Optional path to write per-file JSON results")
    args = ap.parse_args(argv)

    if args.apply and args.dry_run:
        ap.error("Specify at most one of --apply and --dry-run")
    if args.tier == "custom" and not args.custom_imports:
        ap.error("--custom-imports is required when --tier custom is selected")
    if args.custom_imports and args.tier != "custom":
        ap.error("--custom-imports may only be used with --tier custom")
    if args.apply and not args.verify and not args.out_dir:
        print(
            "WARNING: --apply without --verify may expose transitive-carrier errors; "
            "pass --verify for guaranteed compile safety.",
            file=sys.stderr,
        )

    root = os.path.abspath(args.root)
    catalog = build_tier_catalog(args.tier, args.custom_imports)
    catalog_map = {m: (w, c, g) for m, w, c, g in catalog}
    excludes = load_exclude(args.exclude)
    files = discover_files(args)

    mindex = MathlibIndex(root)
    need_closure = args.stats_closure or args.min_module_drop > 0
    l_priv, pub_bits = {}, {}
    if need_closure:
        if not mindex.available():
            sys.exit("ERROR: .lake/packages/mathlib not found; cannot compute Mathlib closures")
        _, l_priv, pub_bits = compute_repo_public_mathlib_bits(root, mindex)
    elif args.verify and mindex.available():
        mindex.ensure_graph()

    lean_env = get_lean_env(root) if args.verify else None

    work_items = []
    skipped_protected = 0
    skipped_excluded = 0
    skipped_no_candidates = 0
    skipped_min_drop = 0

    for path in files:
        if is_frozen_challenge_file(root, path):
            skipped_protected += 1
            continue
        mod = path_to_mod(root, path)
        rel_repo = norm_rel_path(root, path)
        rel_src = os.path.relpath(path, os.path.join(root, "src")).replace(os.sep, "/")
        if (not args.include_protected) and lib_of(mod) in PROTECTED_LIBS:
            skipped_protected += 1
            continue
        if mod in excludes or rel_src in excludes or rel_repo in excludes:
            skipped_excluded += 1
            continue
        with open(path, encoding="utf-8", newline="") as fh:
            text = fh.read()
        header_lines, body_text, rem_idx, rem_mods = candidate_removals_for_file(
            text, catalog_map, args.strict_static
        )
        if not rem_idx:
            skipped_no_candidates += 1
            continue
        before_m, after_m, drop_m = (None, None, None)
        if need_closure:
            before_m, after_m, drop_m = estimate_module_drop(mod, rem_mods, (), l_priv, pub_bits, mindex)
            if drop_m is not None and drop_m < args.min_module_drop:
                skipped_min_drop += 1
                continue
        work_items.append((path, rel_src, mod, text, header_lines, body_text, rem_idx, rem_mods, before_m, after_m, drop_m))

    records = []

    def process_item(item):
        path, rel_src, mod, text, header_lines, body_text, rem_idx, rem_mods, before_m, after_m, drop_m = item
        if args.verify:
            vres = verify_and_repair(
                orig_text=text,
                header_lines=header_lines,
                body_text=body_text,
                removable_indices=rem_idx,
                removable_mods=rem_mods,
                rel_path=rel_src,
                mod_name=mod,
                env=lean_env,
                mindex=mindex,
                catalog_map=catalog_map,
                check_warnings=args.check_warnings,
                smart_replace=not args.no_smart_replace,
                max_restore=args.max_restore,
            )
            final_text = vres["final_text"]
            removed = vres["removed_mods"]
            restored = vres["restored_mods"]
            added = vres["added_mods"]
            status = vres["status"]
            reason = vres["reason"]
            lean_calls = vres["lean_calls"]
            dt_total = round(vres["dt_total"], 2)
            warn_b = vres["warn_before"]
            warn_a = vres["warn_after"]
        else:
            final_text = render_source(header_lines, body_text, rem_idx)
            removed = rem_mods
            restored = []
            added = []
            status = "dry_run" if not args.apply else "applied_unverified"
            reason = "static"
            lean_calls = 0
            dt_total = 0.0
            warn_b = None
            warn_a = None

        if need_closure and status in ("passed", "repaired"):
            before_m, after_m, drop_m = estimate_module_drop(mod, removed, added, l_priv, pub_bits, mindex)

        if args.apply and status != "unchanged":
            if args.out_dir:
                dst = os.path.join(os.path.abspath(args.out_dir), rel_src)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
            else:
                dst = path
            with open(dst, "w", encoding="utf-8", newline="") as fh:
                fh.write(final_text)

        return {
            "module": mod,
            "path": norm_rel_path(root, path),
            "status": status,
            "reason": reason,
            "removed_count": len(removed),
            "restored_count": len(restored),
            "added_count": len(added),
            "removed": removed,
            "restored": restored,
            "added": added,
            "mathlib_before": before_m,
            "mathlib_after": after_m,
            "mathlib_drop": drop_m,
            "lean_calls": lean_calls,
            "verify_sec": dt_total,
            "warn_before": warn_b,
            "warn_after": warn_a,
        }

    if args.verify and args.jobs > 1:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            records = list(ex.map(process_item, work_items))
    else:
        records = [process_item(item) for item in work_items]

    modified = [r for r in records if r["status"] != "unchanged"]
    passed = sum(r["status"] == "passed" for r in records)
    repaired = sum(r["status"] == "repaired" for r in records)
    unchanged = sum(r["status"] == "unchanged" for r in records)
    total_removed = sum(r["removed_count"] for r in modified)
    total_added = sum(r["added_count"] for r in modified)

    print(f"=== prune_mathlib_imports.py ({args.tier}, mode={'apply' if args.apply else 'dry-run'}, verify={args.verify}) ===")
    print(f"Files discovered:          {len(files)}")
    print(f"  Skipped (protected):     {skipped_protected}")
    print(f"  Skipped (excluded):      {skipped_excluded}")
    print(f"  Skipped (no candidates): {skipped_no_candidates}")
    if args.min_module_drop > 0:
        print(f"  Skipped (drop < {args.min_module_drop}):  {skipped_min_drop}")
    print(f"Files processed:           {len(records)}")
    if args.verify:
        print(f"  Passed (full prune):     {passed}")
        print(f"  Repaired (minimal):      {repaired}")
        print(f"  Unchanged (fallback):    {unchanged}")
        print(f"  Total Lean calls:        {sum(r['lean_calls'] for r in records)}")
    print(f"Net import lines removed:  {total_removed - total_added} (-{total_removed} / +{total_added})")
    if need_closure and modified:
        drops = [r["mathlib_drop"] for r in modified if r["mathlib_drop"] is not None]
        if drops:
            sd = sorted(drops)
            print(
                f"Est. Mathlib mods dropped: mean={sum(drops)/len(drops):.1f}, "
                f"median={sd[len(sd)//2]}, max={sd[-1]}, sum={sum(drops)}"
            )

    if args.json_report:
        with open(args.json_report, "w", encoding="utf-8") as fh:
            json.dump(records, fh, indent=2)
        print(f"Wrote JSON report to {args.json_report}")


if __name__ == "__main__":
    main()
