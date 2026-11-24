#!/usr/bin/env python3
"""Privatize Lean 4 `module` imports and clump-internal declarations safely.

Implements three empirically verified Lean `v4.37.0-rc1` `module`-system passes:

  Rule A — Pure-theorem `public import` -> private `import`
    If module B exports only plain `theorem`/`lemma` declarations (no public
    `def`/`abbrev`/`structure`/`class`/`inductive`/`instance`/`opaque`/`axiom`,
    no syntax/macros/notations/`export`, and no propagating global attributes
    such as `@[simp]`/`@[ext]`/`attribute [instance]`), then `public import B`
    in A can be demoted to private `import B` provided:
      1. Nothing in A's public surface (declaration signatures, exposed `def`
         bodies, `variable`/`open`/`attribute`/`export`) mentions a declaration
         of B.
      2. No downstream module D reaching A relies on B's declarations solely
         through edge (A, B) without its own direct import of B.
      3. Transitive `public import`s of B are preserved:
         - `--mode strict` (default): demote only when every remaining public
           import of B is already in A's remaining public transitive closure
           (zero new imports added).
         - `--mode promote`: demote all safe pure-theorem edges and promote the
           minimal missing non-pure/external `public import`s into A so neither
           A nor any downstream module loses type/def/instance/Mathlib access.

  Rule B — Clump-internal absorbed member privatization (`scripts/clump.py`)
    A clump file C contains absorbed members M_1 .. M_{k-1} followed by root
    M_k = C, each bracketed by `-- ===== clump member:` and `-- clump-header:`.
    An absorbed member M_i can be privatized (`@[expose] public section` /
    `public section` -> `section`) when:
      - Subcase B1: M_i was NOT reachable via `public import` from M_k in the
        recorded pre-clump headers (semantically private pre-`#324`), OR
      - Subcase B2: M_i has no global side effects (instances, structures,
        notations, macros, exports, non-local attributes, `@[simp]`/...), is
        not referenced in the public surface of any later public member M_j of
        C, and is not referenced by any external file D importing C.
        Absorbed members with `def`s containing `by` blocks alongside `unfold`
        are skipped conservatively because Lean 4.37's `abstractProofs`
        hoisting differs between `@[expose] public` and private `def`s.
    Any clump-header `public import X` lifted solely by privatized B1 members
    (or covered by remaining public members' transitive public closure) is
    safely demoted to private `import X`.  With `--clump-demote-lifted`,
    B2-lifted external `public import`s are also demoted (use with `--verify`).

  Rule C — Drop redundant `@[expose]` on pure-theorem modules
    On modules whose public surface contains only `theorem`/`lemma`
    declarations, `@[expose] public section` -> `public section` is a
    semantics-preserving hygiene cleanup (theorem bodies are always private
    under `module`; `.olean` bytes are unchanged).

Safety invariants:
  - Never modifies `PROTECTED_LIBS = {"Main", "Challenge"}` (`Main`,
    `Statements`, `Challenge`), Comparator challenge files, or `exotic` modules
    (`import all` / `meta import`).
  - Preserves trailing `--` comments on `import` lines (matching `#542`) and
    `scripts/clump.py` seams / `-- clump-header:` JSON (`unclump` remains valid).
  - Stdlib-only Python 3, deterministic output, `--dry-run` by default.

Usage:
  privatize_imports.py [--root .] [--rules abc] [--mode strict|promote]
                       [--dry-run | --apply | --out-dir DIR]
                       [--dir PREFIX ...] [--files FILE ...]
                       [--exclude FILE] [--stats] [--verify] [--json OUT.json]
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys
import tempfile
import time

PROTECTED_LIBS = frozenset({"Main", "Challenge"})
# Unconditionally frozen Comparator challenge files (mirrors .github/workflows/challenge-files.yml).
FROZEN_CHALLENGE_FILES = frozenset({
    "src/Challenge.lean",
    "comparator.json",
    "export-targets.txt",
    "comparator/FormalConjecturesChallenge.lean",
    "comparator/formal-conjectures.json",
    "comparator/formal-conjectures-export-targets.txt",
})
PROTECTED_PATHS = FROZEN_CHALLENGE_FILES | frozenset({
    "src/Main.lean",
    "src/Statements.lean",
})

SEAM_BEGIN = "-- ===== clump member: "
SEAM_END = "-- ===== end clump member: "
HEADER_TAG = "-- clump-header: "
AUTO = " -- clump:auto"

IMPORT_CODE_RE = re.compile(
    r"^((?:(?:public|private|meta)\s+)*)import\s+((?:all\s+)?)(\S+)\s*$"
)
SECTION_RE = re.compile(
    r"^(?:@\[([^\]]*)\]\s*)?((?:(?:public|private|noncomputable|meta)\s+)*)section(?:\s+([^\s-]\S*))?\s*(?:--.*)?$"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)\s*(?:--.*)?$")
END_RE = re.compile(r"^end(?:\s+([^\s-]\S*))?\s*(?:--.*)?$")
MUTUAL_RE = re.compile(r"^mutual\s*(?:--.*)?$")

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"((?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped|local|meta)\s+)*)"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|irreducible_def)"
    r"\s+([^\s:({\[=]+)"
)
ANON_INST_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped|local|meta)\s+)*"
    r"instance\b"
)
SIDE_EFFECT_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped|local|meta)\s+)*"
    r"(?:instance|structure|class|inductive|notation|macro|macro_rules|syntax|elab|elab_rules|"
    r"declare_syntax_cat|infix|infixl|infixr|prefix|postfix|export|initialize|"
    r"register_simp_attr|declare_aesop_rule_sets|coercion|coe)\b"
)
PRIVATE_PREFIX_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*private\b")
GLOBAL_ATTR_CMD_RE = re.compile(r"^attribute\s+\[(?!local\b)")
ATTR_LINE_RE = re.compile(r"^@\[([^\]]+)\]")
SAFE_ATTRS = frozenset({"expose", "deprecated", "nolint", "no_expose"})
EXPLICIT_PUB_DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*public\s+(?!section\b|import\b)")
BY_WORD_RE = re.compile(r"\bby\b")
EXPOSE_PUB_SEC_PREFIX_RE = re.compile(r"^@\[expose\]\s+public\s+section\b")
ANY_PUB_SEC_PREFIX_RE = re.compile(r"^(?:@\[expose\]\s+)?public\s+section\b")

IDENT_RE = re.compile(r"[A-Za-z_À-ɏ][\w'!?À-ɏ]*")
OPEN_BRACKETS = "({[⦃⟨"
CLOSE_BRACKETS = ")}]⦄⟩"

LEAN_DEFAULT_ARGS = [
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-DmaxSynthPendingDepth=3",
    "-Dpp.unicode.fun=true",
    "-DmaxHeartbeats=4000000",
    "--tstack=400000",
]


def lib_of(mod):
    if mod in ("Statements", "Main"):
        return "Main"
    if mod == "Challenge":
        return "Challenge"
    parts = mod.split(".")
    if parts[0] == "GroundTheory" and len(parts) > 1 and parts[1] in ("LocalFields", "GlobalFields"):
        return "GroundTheoryFields"
    return parts[0]


def split_line_comment(line):
    """Split line into (code_part, trailing_comment_with_leading_ws)."""
    idx = line.find("--")
    if idx < 0:
        return line, ""
    if '"' not in line[:idx]:
        code = line[:idx].rstrip(" \t")
        return code, line[len(code):]
    in_str = False
    esc = False
    for i, c in enumerate(line):
        if esc:
            esc = False
            continue
        if c == "\\" and in_str:
            esc = True
            continue
        if c == '"':
            in_str = not in_str
            continue
        if not in_str and c == "-" and i + 1 < len(line) and line[i + 1] == "-":
            code = line[:i].rstrip(" \t")
            return code, line[len(code):]
    return line, ""


def strip_line_comment(line):
    """Strip `-- ...` outside string literals."""
    code, _ = split_line_comment(line)
    return code


def find_top_level_assign(line, depth):
    """Return (index_of_top_level_assign_or_-1, new_bracket_depth) on comment-stripped line."""
    in_str = False
    esc = False
    n = len(line)
    i = 0
    while i < n:
        c = line[i]
        if esc:
            esc = False
            i += 1
            continue
        if c == "\\" and in_str:
            esc = True
            i += 1
            continue
        if c == '"':
            in_str = not in_str
            i += 1
            continue
        if not in_str:
            if c in OPEN_BRACKETS:
                depth += 1
            elif c in CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif depth == 0 and c == ":" and i + 1 < n and line[i + 1] == "=":
                return i, depth
        i += 1
    return -1, depth


def parse_header_imports(lines):
    """Parse Lean `module` import header.

    Returns (imports, body_start_idx, exotic) where imports is a list of
    (line_idx, mod_name, is_pub, is_priv_kw, comment_suffix).
    """
    imports = []
    exotic = False
    body_start = len(lines)
    for i, l in enumerate(lines):
        if l.startswith(SEAM_BEGIN) or l.startswith("-- This file was produced by scripts/clump.py"):
            body_start = i
            break
        code, comment = split_line_comment(l)
        s = code.strip()
        if s == "" or s == "module":
            continue
        m = IMPORT_CODE_RE.match(s)
        if m:
            kws = m.group(1).split()
            if m.group(2) or "meta" in kws:
                exotic = True
            imports.append((i, m.group(3), "public" in kws, "private" in kws, comment))
            continue
        body_start = i
        break
    return imports, body_start, exotic


def parse_header_string_imports(hdr_text):
    """Parse imports from a clump-header JSON `h` string into ([(mod_name, is_pub)], exotic)."""
    out = []
    exotic = False
    for l in hdr_text.split("\n"):
        s = strip_line_comment(l).strip()
        if not s or s == "module":
            continue
        m = IMPORT_CODE_RE.match(s)
        if m:
            kws = m.group(1).split()
            if m.group(2) or "meta" in kws:
                exotic = True
            out.append((m.group(3), "public" in kws))
    return out, exotic


def analyze_block(lines, collect_idents=True):
    """Analyze a Lean module body (or clump member body) for visibility and symbols."""
    stack = []  # (kind, name, in_pub, in_expose)
    in_pub = False
    in_expose = False
    cdepth = 0

    decls = set()
    has_non_thm = False
    has_global_side_effect = False
    has_def = False
    has_expose_pub_sec = False
    has_pub_sec = False
    has_explicit_pub_decl = False
    def_has_by = False
    block_has_unfold = False

    all_idents = set(IDENT_RE.findall("\n".join(lines))) if collect_idents else None
    pub_surface_idents = set() if collect_idents else None

    # Declaration body tracking: None | "thm_sig" | "thm_body" | "pub_all" | "def_sig" | "def_body"
    mode = None
    bdepth = 0

    for raw in lines:
        if cdepth > 0:
            cdepth = max(0, cdepth + raw.count("/-") - raw.count("-/"))
            continue
        if raw.startswith("/-"):
            cdepth = max(0, raw.count("/-") - raw.count("-/"))
            continue

        code = strip_line_comment(raw)
        if not code.strip():
            continue

        is_col0 = code[0] not in (" ", "\t")

        if not block_has_unfold and "unfold" in code:
            block_has_unfold = True

        if is_col0:
            mode = None
            bdepth = 0

            ms = SECTION_RE.match(code)
            if ms:
                attrs_s, mods_s, sname = ms.group(1) or "", ms.group(2) or "", ms.group(3)
                mods_l = mods_s.split()
                stack.append(("section", sname, in_pub, in_expose))
                if "public" in mods_l:
                    in_pub = True
                    has_pub_sec = True
                    if "expose" in [a.strip() for a in attrs_s.split(",")]:
                        in_expose = True
                        has_expose_pub_sec = True
                elif "private" in mods_l:
                    in_pub = False
                    in_expose = False
                cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))
                continue

            mn = NAMESPACE_RE.match(code)
            if mn:
                stack.append(("namespace", mn.group(1), in_pub, in_expose))
                cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))
                continue

            if MUTUAL_RE.match(code):
                stack.append(("mutual", None, in_pub, in_expose))
                cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))
                continue

            me = END_RE.match(code)
            if me:
                if stack:
                    _, _, in_pub, in_expose = stack.pop()
                cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))
                continue

            ma = ATTR_LINE_RE.match(code)
            if ma and in_pub:
                for a in ma.group(1).split(","):
                    an = a.strip().split()[0] if a.strip() else ""
                    if an and an not in SAFE_ATTRS:
                        has_global_side_effect = True
                        has_non_thm = True

            if GLOBAL_ATTR_CMD_RE.match(code):
                has_global_side_effect = True
                has_non_thm = True
                if in_pub and collect_idents:
                    pub_surface_idents.update(IDENT_RE.findall(code))
                cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))
                continue

            if EXPLICIT_PUB_DECL_RE.match(code):
                has_explicit_pub_decl = True

            if SIDE_EFFECT_RE.match(code) or ANON_INST_RE.match(code):
                is_priv = bool(PRIVATE_PREFIX_RE.match(code))
                if not is_priv and (in_pub or bool(EXPLICIT_PUB_DECL_RE.match(code)) or
                                    code.startswith(("notation", "macro", "syntax", "elab",
                                                     "declare_syntax_cat", "infix", "prefix",
                                                     "postfix", "export", "initialize",
                                                     "register_simp_attr", "declare_aesop_rule_sets"))):
                    has_global_side_effect = True
                    has_non_thm = True

            md = DECL_RE.match(code)
            if md:
                mod_words = md.group(1).split()
                kind = md.group(2)
                raw_name = md.group(3)
                is_priv = "private" in mod_words
                is_pub_decl = (in_pub or "public" in mod_words) and not is_priv

                if raw_name not in ("where", ":=") and is_pub_decl:
                    short = raw_name.rsplit(".", 1)[-1]
                    decls.add(short)
                if kind not in ("theorem", "lemma") and is_pub_decl:
                    has_non_thm = True
                    if kind in ("def", "abbrev", "opaque", "axiom", "irreducible_def"):
                        has_def = True

                if is_pub_decl:
                    if kind in ("theorem", "lemma"):
                        assign_i, bdepth = find_top_level_assign(code[md.end():], 0)
                        if assign_i >= 0:
                            if collect_idents:
                                pub_surface_idents.update(IDENT_RE.findall(code[:md.end() + assign_i]))
                            mode = "thm_body"
                        else:
                            if collect_idents:
                                pub_surface_idents.update(IDENT_RE.findall(code))
                            mode = "thm_sig"
                    elif kind == "def" and not in_expose:
                        assign_i, bdepth = find_top_level_assign(code[md.end():], 0)
                        if assign_i >= 0:
                            if collect_idents:
                                pub_surface_idents.update(IDENT_RE.findall(code[:md.end() + assign_i]))
                            mode = "def_body"
                            if BY_WORD_RE.search(code[md.end() + assign_i:]):
                                def_has_by = True
                        else:
                            if collect_idents:
                                pub_surface_idents.update(IDENT_RE.findall(code))
                            mode = "def_sig"
                    else:
                        if collect_idents:
                            pub_surface_idents.update(IDENT_RE.findall(code))
                        mode = "pub_all"
                        if kind in ("def", "abbrev") and BY_WORD_RE.search(code):
                            def_has_by = True
                else:
                    mode = "thm_body"
            else:
                if in_pub:
                    mode = "pub_all"
                    if collect_idents:
                        pub_surface_idents.update(IDENT_RE.findall(code))
                else:
                    mode = "thm_body"
        else:
            if mode == "thm_sig":
                stripped = code.lstrip()
                if bdepth == 0 and stripped.startswith("| "):
                    mode = "thm_body"
                else:
                    assign_i, bdepth = find_top_level_assign(code, bdepth)
                    if assign_i >= 0:
                        if collect_idents:
                            pub_surface_idents.update(IDENT_RE.findall(code[:assign_i]))
                        mode = "thm_body"
                    elif collect_idents:
                        pub_surface_idents.update(IDENT_RE.findall(code))
            elif mode == "def_sig":
                assign_i, bdepth = find_top_level_assign(code, bdepth)
                if assign_i >= 0:
                    if collect_idents:
                        pub_surface_idents.update(IDENT_RE.findall(code[:assign_i]))
                    mode = "def_body"
                    if BY_WORD_RE.search(code[assign_i:]):
                        def_has_by = True
                elif collect_idents:
                    pub_surface_idents.update(IDENT_RE.findall(code))
            elif mode == "pub_all":
                if collect_idents:
                    pub_surface_idents.update(IDENT_RE.findall(code))
                if has_def and not def_has_by and BY_WORD_RE.search(code):
                    def_has_by = True
            elif mode == "def_body":
                if not def_has_by and BY_WORD_RE.search(code):
                    def_has_by = True

        cdepth = max(0, cdepth + code.count("/-") - code.count("-/"))

    return {
        "decls": decls,
        "has_non_thm": has_non_thm,
        "has_global_side_effect": has_global_side_effect,
        "has_def": has_def,
        "has_def_by_unfold_risk": has_def and def_has_by and block_has_unfold,
        "has_expose_pub_sec": has_expose_pub_sec,
        "has_pub_sec": has_pub_sec,
        "has_explicit_pub_decl": has_explicit_pub_decl,
        "all_idents": all_idents,
        "pub_surface_idents": pub_surface_idents,
    }


def split_clump_members(lines):
    """Split clump file lines into list of member dicts, or None if not a clump."""
    seams = [i for i, l in enumerate(lines) if l.startswith(SEAM_BEGIN)]
    if not seams:
        return None
    members = []
    for idx, si in enumerate(seams):
        if si + 2 >= len(lines) or not lines[si + 1].startswith(HEADER_TAG):
            return None
        info = json.loads(lines[si + 1][len(HEADER_TAG):])
        name = info["m"]
        end_marker = SEAM_END + name + " ====="
        end_idx = None
        limit = seams[idx + 1] if idx + 1 < len(seams) else len(lines)
        for k in range(si + 2, limit):
            if lines[k] == end_marker:
                end_idx = k
                break
        if end_idx is None:
            return None
        body_start = si + 3 if lines[si + 2] == "section" + AUTO else si + 2
        members.append({
            "name": name,
            "info": info,
            "seam_start": si,
            "body_start": body_start,
            "seam_end": end_idx,
        })
    return members


def read_exclude(path):
    if not path or not os.path.exists(path):
        return frozenset()
    with open(path, encoding="utf-8") as f:
        return frozenset(l.split("#")[0].strip() for l in f if l.split("#")[0].strip())


def list_lean_files(root):
    """List `src/**/*.lean` paths via `git ls-files`, falling back to `os.walk` if not a git repo."""
    if os.path.exists(os.path.join(root, ".git")):
        res = subprocess.run(
            ["git", "-C", root, "ls-files", "-z", "src/*.lean"],
            capture_output=True,
        )
        if res.returncode == 0:
            return sorted(p for p in res.stdout.decode().split("\0") if p)
    src_dir = os.path.join(root, "src")
    if not os.path.isdir(src_dir):
        return []
    found = []
    for dirpath, _, filenames in os.walk(src_dir):
        for fn in filenames:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), root).replace(os.sep, "/")
                found.append(rel)
    return sorted(found)


def build_plan(root, rules, mode, exclude, clump_pure_only=False, clump_demote_lifted=False, verbose=False):
    """Run two-pass static analysis across all repo files and compute safe transformations."""
    t0 = time.monotonic()
    paths = list_lean_files(root)
    mod_list = sorted(p[len("src/"):-len(".lean")].replace("/", ".") for p in paths)
    mod_idx = {m: i for i, m in enumerate(mod_list)}
    path_of = {m: "src/" + "/".join(m.split(".")) + ".lean" for m in mod_list}
    n_mods = len(mod_list)

    pub_imps = [[] for _ in range(n_mods)]
    priv_imps = [[] for _ in range(n_mods)]
    exotic_flag = [False] * n_mods
    protected_flag = [
        lib_of(m) in PROTECTED_LIBS or path_of[m] in PROTECTED_PATHS or m in exclude
        for m in mod_list
    ]
    is_clump = [False] * n_mods
    has_expose_pub = [False] * n_mods

    mod_decls = [set() for _ in range(n_mods)]
    mod_has_non_thm = [False] * n_mods
    mod_has_global_se = [False] * n_mods
    clump_meta = {}

    for u, m in enumerate(mod_list):
        full_p = os.path.join(root, path_of[m])
        with open(full_p, encoding="utf-8") as f:
            text = f.read()
        lines = text.split("\n")
        imps, body_start, exotic = parse_header_imports(lines)
        exotic_flag[u] = exotic
        for _, tgt, is_pub, _, _ in imps:
            if is_pub:
                pub_imps[u].append(tgt)
            else:
                priv_imps[u].append(tgt)

        members = split_clump_members(lines) if SEAM_BEGIN in text else None
        if members:
            is_clump[u] = True
            mem_names = {mem["name"] for mem in members}
            mem_infos = []
            for idx, mem in enumerate(members):
                seg = lines[mem["body_start"]:mem["seam_end"]]
                res = analyze_block(seg, collect_idents=True)
                orig_imps, mem_exotic = parse_header_string_imports(mem["info"]["h"])
                if mem_exotic:
                    exotic_flag[u] = True
                mem_infos.append({
                    "idx": idx,
                    "name": mem["name"],
                    "orig_pub_imps": [x for x, p in orig_imps if p],
                    "orig_priv_imps": [x for x, p in orig_imps if not p],
                    "decls": res["decls"],
                    "has_non_thm": res["has_non_thm"],
                    "has_global_side_effect": res["has_global_side_effect"],
                    "has_def": res["has_def"],
                    "has_def_by_unfold_risk": res["has_def_by_unfold_risk"],
                    "has_expose_pub_sec": res["has_expose_pub_sec"],
                    "has_pub_sec": res["has_pub_sec"],
                    "has_explicit_pub_decl": res["has_explicit_pub_decl"],
                    "pub_surface_idents": res["pub_surface_idents"],
                })
            by_name = {mi["name"]: mi for mi in mem_infos}
            root_name = mem_infos[-1]["name"]
            pub_reach = {root_name}
            q = [root_name]
            while q:
                cur = q.pop()
                for tgt in by_name[cur]["orig_pub_imps"]:
                    if tgt in mem_names and tgt not in pub_reach:
                        pub_reach.add(tgt)
                        q.append(tgt)
            for mi in mem_infos:
                mi["is_b1"] = mi["name"] not in pub_reach

            k_mems = len(mem_infos)
            must_pub = [False] * k_mems
            must_pub[-1] = True
            for i in range(k_mems - 1):
                mi = mem_infos[i]
                if mi["has_explicit_pub_decl"]:
                    must_pub[i] = True
                if mi["has_global_side_effect"]:
                    must_pub[i] = True
                if mi["has_def_by_unfold_risk"]:
                    must_pub[i] = True
                if clump_pure_only and mi["has_non_thm"]:
                    must_pub[i] = True

            changed = True
            while changed:
                changed = False
                for j in range(k_mems):
                    if not must_pub[j]:
                        continue
                    psurf = mem_infos[j]["pub_surface_idents"]
                    for i in range(j):
                        if not must_pub[i] and mem_infos[i]["decls"] and not mem_infos[i]["decls"].isdisjoint(psurf):
                            must_pub[i] = True
                            changed = True

            for mi in mem_infos:
                mi["intra_can_privatize"] = (not must_pub[mi["idx"]]) and mi["has_pub_sec"]
                mi["pub_deps_on_earlier"] = [
                    i for i in range(mi["idx"])
                    if mem_infos[i]["decls"] and not mem_infos[i]["decls"].isdisjoint(mi["pub_surface_idents"])
                ]
                del mi["pub_surface_idents"]

            clump_meta[u] = {
                "members": mem_infos,
                "mem_names": mem_names,
            }
            for mi in mem_infos:
                mod_decls[u].update(mi["decls"])
                if mi["has_non_thm"]:
                    mod_has_non_thm[u] = True
                if mi["has_global_side_effect"]:
                    mod_has_global_se[u] = True
            has_expose_pub[u] = mem_infos[-1]["has_expose_pub_sec"]
        else:
            res = analyze_block(lines[body_start:], collect_idents=False)
            mod_decls[u] = res["decls"]
            mod_has_non_thm[u] = res["has_non_thm"]
            mod_has_global_se[u] = res["has_global_side_effect"]
            has_expose_pub[u] = res["has_expose_pub_sec"]

    t1 = time.monotonic()
    if verbose:
        print(f"[Pass 1] Parsed {n_mods:,} files ({len(clump_meta):,} clumps) in {t1 - t0:.1f}s", file=sys.stderr)

    # Topological order on all internal imports (pub + priv)
    indeg = [0] * n_mods
    rev_all = [[] for _ in range(n_mods)]
    dir_int_all = [set() for _ in range(n_mods)]
    for u in range(n_mods):
        for x in pub_imps[u] + priv_imps[u]:
            v = mod_idx.get(x)
            if v is not None and v not in dir_int_all[u]:
                dir_int_all[u].add(v)
                indeg[u] += 1
                rev_all[v].append(u)
    q = [u for u in range(n_mods) if indeg[u] == 0]
    topo = []
    while q:
        u = q.pop()
        topo.append(u)
        for v in rev_all[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    if len(topo) != n_mods:
        sys.exit("error: import graph has a cycle")

    ext_set = set()
    for u in range(n_mods):
        for x in pub_imps[u]:
            if x not in mod_idx:
                ext_set.add(x)
    ext_list = sorted(ext_set)
    ext_idx = {e: i for i, e in enumerate(ext_list)}

    orig_pub_int_cl = [0] * n_mods
    orig_pub_ext_cl = [0] * n_mods
    for u in topo:
        bi = 1 << u
        be = 0
        for x in pub_imps[u]:
            v = mod_idx.get(x)
            if v is not None:
                bi |= orig_pub_int_cl[v]
                be |= orig_pub_ext_cl[v]
            else:
                be |= 1 << ext_idx[x]
        orig_pub_int_cl[u] = bi
        orig_pub_ext_cl[u] = be

    # Bitset-indexed maps for Pass 2 downstream & public-surface reference checks
    pure_candidates = set()
    for u in range(n_mods):
        if exotic_flag[u] or protected_flag[u]:
            continue
        if is_clump[u]:
            root_mi = clump_meta[u]["members"][-1]
            if not root_mi["has_non_thm"] and not root_mi["has_global_side_effect"]:
                pure_candidates.add(u)
        else:
            if not mod_has_non_thm[u] and not mod_has_global_se[u]:
                pure_candidates.add(u)

    mod_owner_mask = collections.defaultdict(int)
    for u in pure_candidates:
        bit = 1 << u
        for d in mod_decls[u]:
            mod_owner_mask[d] |= bit

    clump_owner_mask = collections.defaultdict(int)
    clump_tok_mems = collections.defaultdict(list)
    b2_cand_count = 0
    for u, cm in clump_meta.items():
        if exotic_flag[u] or protected_flag[u]:
            continue
        bit = 1 << u
        for mi in cm["members"][:-1]:
            if mi["intra_can_privatize"] and not mi["is_b1"]:
                b2_cand_count += 1
                idx_m = mi["idx"]
                for d in mi["decls"]:
                    clump_owner_mask[d] |= bit
                    clump_tok_mems[(u, d)].append(idx_m)

    mod_users = collections.defaultdict(set)
    mod_pub_users = collections.defaultdict(set)
    b2_ext_used = set()

    for u, m in enumerate(mod_list):
        can_see = 0
        for v in dir_int_all[u]:
            can_see |= orig_pub_int_cl[v]
        can_see &= ~(1 << u)
        if can_see == 0:
            continue

        full_p = os.path.join(root, path_of[m])
        with open(full_p, encoding="utf-8") as f:
            lines = f.read().split("\n")
        _, body_start, _ = parse_header_imports(lines)
        res = analyze_block(lines[body_start:], collect_idents=True)
        all_id = res["all_idents"]
        pub_id = res["pub_surface_idents"]

        for tok in all_id:
            mm = mod_owner_mask.get(tok)
            if mm:
                hit = can_see & mm
                if hit:
                    in_pub_tok = tok in pub_id
                    while hit:
                        lsb = hit & -hit
                        owner_u = lsb.bit_length() - 1
                        mod_users[owner_u].add(u)
                        if in_pub_tok:
                            mod_pub_users[owner_u].add(u)
                        hit ^= lsb
            cm_mask = clump_owner_mask.get(tok)
            if cm_mask:
                hit = can_see & cm_mask
                while hit:
                    lsb = hit & -hit
                    clump_u = lsb.bit_length() - 1
                    for mem_idx in clump_tok_mems[(clump_u, tok)]:
                        b2_ext_used.add((clump_u, mem_idx))
                    hit ^= lsb

    t2 = time.monotonic()
    if verbose:
        print(f"[Pass 2] Downstream & public-surface symbol check done in {t2 - t1:.1f}s "
              f"(B2 candidates={b2_cand_count:,}, externally referenced={len(b2_ext_used):,})", file=sys.stderr)

    # Rule B: clump-internal absorbed member privatization
    clump_privatized_members = {}
    clump_demoted_imports = {}
    rule_b_stats = collections.Counter()

    if "b" in rules:
        for u, cm in clump_meta.items():
            if exotic_flag[u] or protected_flag[u]:
                continue
            mems = cm["members"]
            k = len(mems)
            must_pub = [False] * k
            must_pub[-1] = True
            for i in range(k - 1):
                mi = mems[i]
                if not mi["intra_can_privatize"]:
                    must_pub[i] = True
                elif (not mi["is_b1"]) and ((u, i) in b2_ext_used):
                    must_pub[i] = True
            changed = True
            while changed:
                changed = False
                for j in range(k):
                    if not must_pub[j]:
                        continue
                    for i in mems[j]["pub_deps_on_earlier"]:
                        if not must_pub[i]:
                            must_pub[i] = True
                            changed = True

            priv_idxs = {i for i in range(k - 1) if not must_pub[i]}
            if not priv_idxs:
                continue
            clump_privatized_members[u] = priv_idxs
            for i in priv_idxs:
                rule_b_stats["members_privatized"] += 1
                if mems[i]["is_b1"]:
                    rule_b_stats["members_b1"] += 1
                else:
                    rule_b_stats["members_b2"] += 1
                if mems[i]["has_def"]:
                    rule_b_stats["members_with_def"] += 1

            pub_mem_ext_pubs = set()
            for j in range(k):
                if must_pub[j]:
                    for tgt in mems[j]["orig_pub_imps"]:
                        if tgt not in cm["mem_names"]:
                            pub_mem_ext_pubs.add(tgt)
            rem_int_cl = 0
            rem_ext_cl = 0
            for tgt in pub_mem_ext_pubs:
                v = mod_idx.get(tgt)
                if v is not None:
                    rem_int_cl |= orig_pub_int_cl[v]
                    rem_ext_cl |= orig_pub_ext_cl[v]
                elif tgt in ext_idx:
                    rem_ext_cl |= 1 << ext_idx[tgt]

            b2_or_root_ext_pubs = set()
            for j in range(k):
                if not mems[j]["is_b1"]:
                    for tgt in mems[j]["orig_pub_imps"]:
                        if tgt not in cm["mem_names"]:
                            b2_or_root_ext_pubs.add(tgt)

            demoted = set()
            for tgt in pub_imps[u]:
                if tgt in pub_mem_ext_pubs:
                    continue
                v = mod_idx.get(tgt)
                is_covered = (
                    ((rem_int_cl >> v) & 1) if v is not None
                    else ((rem_ext_cl >> ext_idx[tgt]) & 1) if tgt in ext_idx else False
                )
                is_b1_only = tgt not in b2_or_root_ext_pubs
                if is_b1_only or is_covered or clump_demote_lifted:
                    demoted.add(tgt)
                    rule_b_stats["clump_pub_demoted"] += 1
                    if is_b1_only:
                        rule_b_stats["clump_pub_demoted_b1"] += 1
                    elif is_covered:
                        rule_b_stats["clump_pub_demoted_covered"] += 1
                    else:
                        rule_b_stats["clump_pub_demoted_lifted"] += 1
                    if v is not None:
                        rule_b_stats["clump_pub_demoted_internal"] += 1
                    else:
                        rule_b_stats["clump_pub_demoted_external"] += 1
            if demoted:
                clump_demoted_imports[u] = demoted

    # Effective `pure_safe` set after Rule B
    pure_safe = set()
    for u in range(n_mods):
        if exotic_flag[u] or protected_flag[u]:
            continue
        if is_clump[u]:
            priv_idxs = clump_privatized_members.get(u, set())
            mems = clump_meta[u]["members"]
            if all((not mi["has_non_thm"] and not mi["has_global_side_effect"])
                   for mi in mems if mi["idx"] not in priv_idxs):
                pure_safe.add(u)
        else:
            if not mod_has_non_thm[u] and not mod_has_global_se[u]:
                pure_safe.add(u)

    # Rule A: bottom-up pure-theorem `public import` -> private `import`
    work_pub = []
    work_priv = []
    for u in range(n_mods):
        b_dem = clump_demoted_imports.get(u, set())
        work_pub.append([x for x in pub_imps[u] if x not in b_dem])
        work_priv.append(list(priv_imps[u]) + [x for x in pub_imps[u] if x in b_dem])

    def reaches(d, target):
        for x in dir_int_all[d]:
            if (orig_pub_int_cl[x] >> target) & 1:
                return True
        return False

    rule_a_demoted = {}
    rule_a_promoted = {}
    rule_a_stats = collections.Counter()

    new_pub_int_cl = [0] * n_mods
    new_pub_ext_cl = [0] * n_mods

    for u in topo:
        if "a" not in rules or exotic_flag[u] or protected_flag[u]:
            bi = 1 << u
            be = 0
            for x in work_pub[u]:
                v = mod_idx.get(x)
                if v is not None:
                    bi |= new_pub_int_cl[v]
                    be |= new_pub_ext_cl[v]
                elif x in ext_idx:
                    be |= 1 << ext_idx[x]
            new_pub_int_cl[u] = bi
            new_pub_ext_cl[u] = be
            continue

        cur_pubs = list(work_pub[u])
        demote_set = set()
        promote_list = []
        promote_set = set()

        eligible = []
        kept_pubs = []
        for x in cur_pubs:
            v = mod_idx.get(x)
            if v is None or v not in pure_safe:
                kept_pubs.append(x)
                continue
            rule_a_stats["candidates_pure_edges"] += 1
            if u in mod_pub_users.get(v, ()):
                rule_a_stats["blocked_pub_surface"] += 1
                kept_pubs.append(x)
                continue
            ds_blocked = False
            for d in mod_users.get(v, ()):
                if d == u or v in dir_int_all[d]:
                    continue
                if reaches(d, u):
                    ds_blocked = True
                    break
            if ds_blocked:
                rule_a_stats["blocked_downstream_user"] += 1
                kept_pubs.append(x)
                continue
            eligible.append((x, v))

        cov_i = 0
        cov_e = 0
        for x in kept_pubs:
            v = mod_idx.get(x)
            if v is not None:
                cov_i |= new_pub_int_cl[v]
                cov_e |= new_pub_ext_cl[v]
            elif x in ext_idx:
                cov_e |= 1 << ext_idx[x]

        if mode == "strict":
            rem = list(eligible)
            changed = True
            while changed:
                changed = False
                still_rem = []
                for idx_e, (x, v) in enumerate(rem):
                    ri = cov_i
                    re_b = cov_e
                    for idx_o, (_, vo) in enumerate(rem):
                        if idx_o != idx_e:
                            ri |= new_pub_int_cl[vo]
                            re_b |= new_pub_ext_cl[vo]
                    miss_i = (new_pub_int_cl[v] & ~(1 << v)) & ~ri
                    miss_e = new_pub_ext_cl[v] & ~re_b
                    if miss_i == 0 and miss_e == 0:
                        demote_set.add(x)
                        changed = True
                    else:
                        still_rem.append((x, v))
                rem = still_rem
            for x, v in rem:
                rule_a_stats["blocked_strict_transitive"] += 1
                kept_pubs.append(x)
                cov_i |= new_pub_int_cl[v]
                cov_e |= new_pub_ext_cl[v]
        else:
            for x, v in eligible:
                demote_set.add(x)
                for gx in work_pub[v]:
                    gv = mod_idx.get(gx)
                    if gv is not None:
                        if not ((cov_i >> gv) & 1):
                            if gx not in promote_set and gx not in kept_pubs:
                                promote_set.add(gx)
                                promote_list.append(gx)
                            cov_i |= new_pub_int_cl[gv]
                            cov_e |= new_pub_ext_cl[gv]
                    elif gx in ext_idx:
                        if not ((cov_e >> ext_idx[gx]) & 1):
                            if gx not in promote_set and gx not in kept_pubs:
                                promote_set.add(gx)
                                promote_list.append(gx)
                            cov_e |= 1 << ext_idx[gx]

        if demote_set:
            rule_a_demoted[u] = demote_set
            rule_a_stats["demoted_edges"] += len(demote_set)
            rule_a_stats["files_demoted"] += 1
        if promote_list:
            rule_a_promoted[u] = promote_list
            rule_a_stats["promoted_edges"] += len(promote_list)

        work_pub[u] = kept_pubs + promote_list
        work_priv[u] = [x for x in work_priv[u] if x not in promote_set] + [x for x in cur_pubs if x in demote_set]
        new_pub_int_cl[u] = cov_i | (1 << u)
        new_pub_ext_cl[u] = cov_e

    # Rule C: `@[expose] public section` -> `public section` on pure_safe files
    rule_c_files = set()
    if "c" in rules:
        for u in pure_safe:
            if has_expose_pub[u]:
                rule_c_files.add(u)

    def sim_loads(pub_lists, priv_lists):
        if n_mods == 0:
            return 0, 0, 0, 0
        cl = [0] * n_mods
        for u in topo:
            b = 1 << u
            for x in pub_lists[u]:
                v = mod_idx.get(x)
                if v is not None:
                    b |= cl[v]
            cl[u] = b
        tot = 0
        per_mod = []
        for u in topo:
            b = 0
            for x in pub_lists[u]:
                v = mod_idx.get(x)
                if v is not None:
                    b |= cl[v]
            for x in priv_lists[u]:
                v = mod_idx.get(x)
                if v is not None:
                    b |= cl[v]
            cnt = b.bit_count()
            tot += cnt
            per_mod.append(cnt)
        per_mod.sort()
        return tot, per_mod[n_mods // 2], per_mod[int(n_mods * 0.9)], per_mod[-1]

    before_loads = sim_loads(pub_imps, priv_imps)
    after_loads = sim_loads(work_pub, work_priv)

    t3 = time.monotonic()
    if verbose:
        print(f"[Plan] Finished in {t3 - t0:.1f}s total", file=sys.stderr)

    return {
        "mod_list": mod_list,
        "mod_idx": mod_idx,
        "path_of": path_of,
        "is_clump": is_clump,
        "pure_safe": pure_safe,
        "clump_meta": clump_meta,
        "clump_privatized_members": clump_privatized_members,
        "clump_demoted_imports": clump_demoted_imports,
        "rule_a_demoted": rule_a_demoted,
        "rule_a_promoted": rule_a_promoted,
        "rule_c_files": rule_c_files,
        "rule_a_stats": dict(rule_a_stats),
        "rule_b_stats": dict(rule_b_stats),
        "before_loads": before_loads,
        "after_loads": after_loads,
        "orig_pub_imps": pub_imps,
        "work_pub": work_pub,
        "work_priv": work_priv,
    }


def _rewrite_section_lines(lines, start, end, pattern, replacement):
    """Rewrite matching column-0 section headers in lines[start:end], skipping block comments."""
    count = 0
    cdepth = 0
    for li in range(start, end):
        l = lines[li]
        if cdepth > 0:
            cdepth = max(0, cdepth + l.count("/-") - l.count("-/"))
            continue
        if l.startswith("/-"):
            cdepth = max(0, l.count("/-") - l.count("-/"))
            continue
        if pattern.match(l):
            lines[li] = pattern.sub(replacement, l, count=1)
            count += 1
        cdepth = max(0, cdepth + l.count("/-") - l.count("-/"))
    return count


def transform_file_text(u, text, plan):
    """Apply planned Rule A / B / C edits to a single file's text.

    Returns (new_text, changed_bool, summary_dict).
    """
    b_priv_idxs = plan["clump_privatized_members"].get(u, set())
    b_dem_imps = plan["clump_demoted_imports"].get(u, set())
    a_dem_imps = plan["rule_a_demoted"].get(u, set())
    a_prom_imps = plan["rule_a_promoted"].get(u, [])
    do_rule_c = u in plan["rule_c_files"]

    all_demote = b_dem_imps | a_dem_imps
    if not b_priv_idxs and not all_demote and not a_prom_imps and not do_rule_c:
        return text, False, {}

    lines = text.split("\n")
    imps, body_start, _ = parse_header_imports(lines)

    existing_priv_idx = {}
    existing_pub_set = set()
    last_pub_idx = None
    module_idx = 0
    for i in range(body_start):
        if strip_line_comment(lines[i]).strip() == "module":
            module_idx = i
    for li, tgt, is_pub, _, _ in imps:
        if is_pub:
            existing_pub_set.add(tgt)
            if tgt not in all_demote:
                last_pub_idx = li
        else:
            existing_priv_idx[tgt] = li

    new_header_lines = list(lines[:body_start])
    demoted_done = 0
    for li, tgt, is_pub, _, comment in imps:
        if is_pub and tgt in all_demote:
            new_header_lines[li] = f"import {tgt}{comment}"
            demoted_done += 1

    to_insert = []
    promoted_done = 0
    for tgt in a_prom_imps:
        if tgt in existing_pub_set and tgt not in all_demote:
            continue
        if tgt in existing_priv_idx:
            li = existing_priv_idx[tgt]
            _, comment = split_line_comment(new_header_lines[li])
            new_header_lines[li] = f"public import {tgt}{comment}"
            promoted_done += 1
        else:
            to_insert.append(f"public import {tgt}")
            promoted_done += 1

    if to_insert:
        insert_at = (last_pub_idx + 1) if last_pub_idx is not None else (module_idx + 1)
        if last_pub_idx is None and insert_at < len(new_header_lines) and new_header_lines[insert_at].strip() == "":
            insert_at += 1
        new_header_lines[insert_at:insert_at] = to_insert

    body_lines = list(lines[body_start:])
    members = split_clump_members(body_lines) if plan["is_clump"][u] else None
    b_sections_privatized = 0
    c_exposes_dropped = 0

    if members:
        assert len(members) == len(plan["clump_meta"][u]["members"]), (
            f"clump member count mismatch in {plan['mod_list'][u]}"
        )
        root_idx = len(members) - 1
        for idx, mem in enumerate(members):
            if idx in b_priv_idxs:
                b_sections_privatized += _rewrite_section_lines(
                    body_lines, mem["body_start"], mem["seam_end"],
                    ANY_PUB_SEC_PREFIX_RE, "section",
                )
            elif idx == root_idx and do_rule_c:
                c_exposes_dropped += _rewrite_section_lines(
                    body_lines, mem["body_start"], mem["seam_end"],
                    EXPOSE_PUB_SEC_PREFIX_RE, "public section",
                )
    elif do_rule_c:
        c_exposes_dropped += _rewrite_section_lines(
            body_lines, 0, len(body_lines),
            EXPOSE_PUB_SEC_PREFIX_RE, "public section",
        )

    new_text = "\n".join(new_header_lines + body_lines)
    changed = new_text != text
    return new_text, changed, {
        "demoted": demoted_done,
        "promoted": promoted_done,
        "b_sections": b_sections_privatized,
        "c_exposes": c_exposes_dropped,
    }


def select_scope(plan, dirs, files):
    """Return sorted list of module indices matching `--dir` / `--files` (or all if neither given)."""
    n = len(plan["mod_list"])
    if not dirs and not files:
        return list(range(n))
    norm_dirs = [os.path.normpath(d).replace(os.sep, "/").rstrip("/") + "/" for d in (dirs or [])]
    norm_files = {os.path.normpath(f).replace(os.sep, "/") for f in (files or [])}
    out = []
    for u in range(n):
        p = plan["path_of"][plan["mod_list"][u]]
        if p in norm_files or any(p.startswith(d) for d in norm_dirs):
            out.append(u)
    return out


def _lean_base_env():
    env = os.environ.copy()
    elan_bin = os.path.expanduser("~/.elan/bin")
    if os.path.isdir(elan_bin):
        cur = env.get("PATH", "")
        if elan_bin not in cur.split(os.pathsep):
            env["PATH"] = elan_bin + (os.pathsep + cur if cur else "")
    return env


def verify_modules(root, plan, selected_us, out_dir=None, profile=False, timeout=120):
    """Compile before & after copies in scratch dir against read-only `.lake/build` LEAN_PATH."""
    lean_env = _lean_base_env()
    lp = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=root, env=lean_env, text=True
    ).strip()
    lean_env["LEAN_PATH"] = lp

    tmp_ctx = None
    if out_dir is None:
        tmp_ctx = tempfile.TemporaryDirectory(prefix="privatize_verify_")
        work_root = tmp_ctx.name
    else:
        work_root = out_dir
        os.makedirs(work_root, exist_ok=True)

    results = []
    after_root = os.path.join(work_root, "after")
    before_root = os.path.join(work_root, "before")
    os.makedirs(after_root, exist_ok=True)
    os.makedirs(before_root, exist_ok=True)

    # Note: Do NOT prepend `after_root` to LEAN_PATH when verifying a partial subset,
    # because Lean expects all modules under a top-level namespace directory (e.g. `Formalism/`)
    # to reside in the first LEAN_PATH entry containing that directory.

    def run_one(compile_root, mod_name, rel_path, text, env):
        dst = os.path.join(compile_root, rel_path)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "w", encoding="utf-8") as f:
            f.write(text)
        o = dst[:-len(".lean")] + ".olean"
        for ext in (".olean", ".olean.private", ".olean.server", ".ilean"):
            p = dst[:-len(".lean")] + ext
            if os.path.exists(p):
                os.remove(p)
        extra_args = list(LEAN_DEFAULT_ARGS)
        if lib_of(mod_name) == "GroundTheoryFields":
            extra_args.append("-DsynthInstance.maxHeartbeats=400000")
        cmd = ["lean", f"--root={compile_root}", "-o", o] + extra_args
        if profile:
            cmd.append("--profile")
        cmd.append(dst)
        if sys.platform == "darwin":
            cmd = ["/usr/bin/time", "-l"] + cmd
        t0 = time.monotonic()
        r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout)
        dt = time.monotonic() - t0
        combined = r.stdout + "\n" + r.stderr
        insns = None
        rss = None
        imp_ms = None
        m_ins = re.search(r"(\d+)\s+instructions retired", combined)
        if m_ins:
            insns = int(m_ins.group(1))
        m_rss = re.search(r"(\d+)\s+maximum resident set size", combined)
        if m_rss:
            rss = int(m_rss.group(1))
        m_imp = re.search(r"import\s+([\d.]+)(ms|s)", combined)
        if m_imp:
            val = float(m_imp.group(1))
            imp_ms = val if m_imp.group(2) == "ms" else val * 1000.0
        warns = [l for l in combined.splitlines() if ": warning:" in l]
        errs = [l for l in combined.splitlines() if ": error" in l]
        osz = os.path.getsize(o) if os.path.exists(o) else 0
        psz = os.path.getsize(o + ".private") if os.path.exists(o + ".private") else 0
        return {
            "rc": r.returncode,
            "wall_s": dt,
            "imp_ms": imp_ms,
            "insns": insns,
            "rss": rss,
            "olean": osz,
            "olean_priv": psz,
            "n_warns": len(warns),
            "errs": errs[:5],
        }

    selected_set = set(selected_us)
    mod_idx = plan["mod_idx"]
    indeg = {u: 0 for u in selected_set}
    rev = collections.defaultdict(list)
    for u in selected_set:
        for x in plan["orig_pub_imps"][u]:
            v = mod_idx.get(x)
            if v in selected_set:
                indeg[u] += 1
                rev[v].append(u)
    q = [u for u in selected_us if indeg[u] == 0]
    ordered = []
    while q:
        u = q.pop(0)
        ordered.append(u)
        for v in rev[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    for u in selected_us:
        if u not in ordered:
            ordered.append(u)

    for u in ordered:
        m = plan["mod_list"][u]
        rel = plan["path_of"][m][len("src/"):]
        with open(os.path.join(root, plan["path_of"][m]), encoding="utf-8") as f:
            orig = f.read()
        new_txt, changed, ch_info = transform_file_text(u, orig, plan)
        if not changed:
            continue
        b = run_one(before_root, m, rel, orig, lean_env)
        a = run_one(after_root, m, rel, new_txt, lean_env)
        results.append({
            "module": m,
            "is_clump": plan["is_clump"][u],
            "changes": ch_info,
            "before": b,
            "after": a,
        })
        new_warns = a["n_warns"] - b["n_warns"]
        status = "PASS" if (a["rc"] == 0 and new_warns <= 0) else "FAIL"
        d_ol = a["olean"] - b["olean"]
        pct_ol = (100.0 * d_ol / b["olean"]) if b["olean"] else 0.0
        ins_str = ""
        if b["insns"] and a["insns"]:
            d_ins = 100.0 * (a["insns"] - b["insns"]) / b["insns"]
            ins_str = f" insns:{b['insns']/1e9:.2f}B->{a['insns']/1e9:.2f}B({d_ins:+.1f}%)"
        print(f"  [{status}] {m}: olean {b['olean']:,}->{a['olean']:,} ({pct_ol:+.1f}%) "
              f"priv {b['olean_priv']:,}->{a['olean_priv']:,} "
              f"wall {b['wall_s']:.2f}s->{a['wall_s']:.2f}s "
              f"warns {b['n_warns']}->{a['n_warns']}{ins_str} {ch_info}", flush=True)
        if a["errs"]:
            for e in a["errs"][:3]:
                print(f"      ERR: {e[:160]}", flush=True)

    if tmp_ctx is not None:
        tmp_ctx.cleanup()
    return results


def print_stats(plan, rules, mode, selected_us):
    n_mods = len(plan["mod_list"])
    sel = set(selected_us)
    a_files = sum(1 for u in plan["rule_a_demoted"] if u in sel)
    a_dem = sum(len(v) for u, v in plan["rule_a_demoted"].items() if u in sel)
    a_prom = sum(len(v) for u, v in plan["rule_a_promoted"].items() if u in sel)
    b_files = sum(1 for u in plan["clump_privatized_members"] if u in sel)
    b_mems = sum(len(v) for u, v in plan["clump_privatized_members"].items() if u in sel)
    b_dem = sum(len(v) for u, v in plan["clump_demoted_imports"].items() if u in sel)
    c_files = sum(1 for u in plan["rule_c_files"] if u in sel)
    touched = len({u for u in sel if (
        u in plan["rule_a_demoted"] or u in plan["clump_privatized_members"]
        or u in plan["clump_demoted_imports"] or u in plan["rule_c_files"]
    )})

    b_tot, b_p50, b_p90, b_max = plan["before_loads"]
    a_tot, a_p50, a_p90, a_max = plan["after_loads"]
    mean_b = (b_tot / n_mods) if n_mods else 0.0
    mean_a = (a_tot / n_mods) if n_mods else 0.0
    pct = (100.0 * (a_tot - b_tot) / b_tot) if b_tot else 0.0

    print(f"=== privatize_imports.py stats (rules={rules}, mode={mode}) ===")
    print(f"Repo modules: {n_mods:,}  |  Scoped: {len(sel):,}  |  Pure-safe: {len(plan['pure_safe']):,}  |  Touched: {touched:,}")
    print(f"  Rule A (pure-thm public->private): files={a_files:,}, demoted={a_dem:,}, promoted={a_prom:,}")
    if plan["rule_a_stats"]:
        ra = plan["rule_a_stats"]
        print(f"    (repo-wide candidates={ra.get('candidates_pure_edges',0):,}, "
              f"blocked_pub_surface={ra.get('blocked_pub_surface',0):,}, "
              f"blocked_downstream={ra.get('blocked_downstream_user',0):,}, "
              f"blocked_strict_trans={ra.get('blocked_strict_transitive',0):,})")
    print(f"  Rule B (clump absorbed members):   clumps={b_files:,}, members_privatized={b_mems:,}, clump_pub_demoted={b_dem:,}")
    if plan["rule_b_stats"]:
        rb = plan["rule_b_stats"]
        print(f"    (repo-wide B1={rb.get('members_b1',0):,}, B2={rb.get('members_b2',0):,}, "
              f"with_def={rb.get('members_with_def',0):,}; "
              f"demoted: int={rb.get('clump_pub_demoted_internal',0):,}, ext={rb.get('clump_pub_demoted_external',0):,}, "
              f"b1_only={rb.get('clump_pub_demoted_b1',0):,}, covered={rb.get('clump_pub_demoted_covered',0):,}, "
              f"lifted={rb.get('clump_pub_demoted_lifted',0):,})")
    print(f"  Rule C (drop @[expose] pure-thm):  files={c_files:,}")
    print("  Internal .olean loads (repo-wide exact bitset):")
    print(f"    Before: {b_tot:>12,d}  (mean {mean_b:5.1f}, p50={b_p50}, p90={b_p90}, max={b_max})")
    print(f"    After:  {a_tot:>12,d}  (mean {mean_a:5.1f}, p50={a_p50}, p90={a_p90}, max={a_max})  [{pct:+.1f}%]")


def main(argv=None):
    ap = argparse.ArgumentParser(description="Privatize Lean 4 module imports & clump-internal members.")
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument("--rules", default="abc", help="Subset of 'a', 'b', 'c' or 'all' (default: abc)")
    ap.add_argument("--mode", choices=["strict", "promote"], default="strict",
                    help="Rule A transitive closure mode: strict (0 new imports, default) or promote (minimal non-pure lift)")
    ap.add_argument("--clump-pure-only", action="store_true",
                    help="In Rule B, only privatize pure-theorem absorbed clump members (skip def-bearing members)")
    ap.add_argument("--clump-demote-lifted", action="store_true",
                    help="In Rule B, also demote B2-lifted external public imports not covered by root (use with --verify)")
    ap.add_argument("--dir", action="append", help="Scope edits/verify to files under prefix (e.g. src/Formalism)")
    ap.add_argument("--files", nargs="+", help="Scope edits/verify to specific file paths")
    ap.add_argument("--exclude", default=os.path.join(os.path.dirname(__file__), "privatize-exclude.txt"),
                    help="Modules never to modify (one per line)")
    ap.add_argument("--dry-run", action="store_true", help="Compute plan without modifying files (default)")
    ap.add_argument("--apply", action="store_true", help="Apply edits in place under --root")
    ap.add_argument("--out-dir", help="Write transformed copies of scoped files into DIR instead of modifying --root")
    ap.add_argument("--stats", action="store_true", help="Print detailed summary statistics")
    ap.add_argument("--verify", action="store_true", help="Compile before/after copies via read-only lean & measure deltas")
    ap.add_argument("--profile", action="store_true", help="Pass --profile to lean during --verify")
    ap.add_argument("--timeout", type=int, default=120, help="Per-module timeout (s) for --verify")
    ap.add_argument("--json", dest="json_out", help="Write summary + verify results to JSON file")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args(argv)

    rules = "abc" if args.rules == "all" else args.rules.lower()
    if not rules or not set(rules) <= {"a", "b", "c"}:
        ap.error(f"invalid --rules {args.rules!r}: expected subset of 'a','b','c' or 'all'")
    if args.apply and args.out_dir:
        ap.error("--apply and --out-dir are mutually exclusive")
    if args.dry_run and (args.apply or args.out_dir):
        ap.error("--dry-run cannot be combined with --apply or --out-dir")

    exclude = read_exclude(args.exclude)
    plan = build_plan(
        args.root,
        rules=rules,
        mode=args.mode,
        exclude=exclude,
        clump_pure_only=args.clump_pure_only,
        clump_demote_lifted=args.clump_demote_lifted,
        verbose=args.verbose,
    )
    selected_us = select_scope(plan, args.dir, args.files)

    if args.stats or (not args.apply and not args.out_dir and not args.verify):
        print_stats(plan, rules, args.mode, selected_us)

    written = 0
    if args.apply or args.out_dir:
        for u in selected_us:
            m = plan["mod_list"][u]
            rel_path = plan["path_of"][m]
            src_path = os.path.join(args.root, rel_path)
            with open(src_path, encoding="utf-8") as f:
                orig = f.read()
            new_txt, changed, _ = transform_file_text(u, orig, plan)
            if not changed:
                continue
            dst_path = src_path if args.apply else os.path.join(args.out_dir, rel_path)
            os.makedirs(os.path.dirname(dst_path), exist_ok=True)
            with open(dst_path, "w", encoding="utf-8") as f:
                f.write(new_txt)
            written += 1
        print(f"Wrote {written:,} transformed files ({'in-place' if args.apply else args.out_dir})")

    verify_res = None
    if args.verify:
        print(f"\n=== Verifying {len(selected_us)} scoped modules ===")
        verify_res = verify_modules(
            args.root, plan, selected_us,
            out_dir=os.path.join(args.out_dir, "_verify") if args.out_dir else None,
            profile=args.profile,
            timeout=args.timeout,
        )
        n_pass = sum(1 for r in verify_res if r["after"]["rc"] == 0 and r["after"]["n_warns"] <= r["before"]["n_warns"])
        print(f"Verified: {n_pass}/{len(verify_res)} passed with 0 errors and 0 new warnings")

    if args.json_out:
        summary = {
            "rules": rules,
            "mode": args.mode,
            "n_mods": len(plan["mod_list"]),
            "pure_safe": len(plan["pure_safe"]),
            "rule_a_stats": plan["rule_a_stats"],
            "rule_b_stats": plan["rule_b_stats"],
            "rule_c_files": len(plan["rule_c_files"]),
            "before_loads": plan["before_loads"],
            "after_loads": plan["after_loads"],
            "verify": verify_res,
        }
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2)


if __name__ == "__main__":
    main()
