#!/usr/bin/env python3
"""Unit tests for scripts/prune_mathlib_imports.py; no Lean or network calls."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("prune_mathlib_imports.py")
spec = importlib.util.spec_from_file_location("prune_mathlib_imports", SCRIPT)
pmi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pmi)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="") as fh:
        fh.write(text)


def read_text(path: Path) -> str:
    with open(path, encoding="utf-8", newline="") as fh:
        return fh.read()


class TestHeaderParsing(unittest.TestCase):
    def test_visibility_exotic_and_trailing_comments(self):
        src = (
            "/-!\n"
            "Block comment before header\n"
            "-/\n"
            "module -- module comment\n"
            "\n"
            "-- standalone comment\n"
            "public import Mathlib.Combinatorics.Enumerative.DyckWord -- keep public\n"
            "import all Mathlib.NumberTheory.LucasLehmer -- keep import all\n"
            "meta import Mathlib.NumberTheory.SelbergSieve -- keep meta\n"
            "public meta import Mathlib.Data.NNRat.Floor\n"
            "private import Mathlib.Algebra.Order.Interval.Basic -- drop private\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord--tight comment\n"
            "import Mathlib.LinearAlgebra.Matrix.Defs -- keep non-candidate\n"
            "\n"
            "def foo : Nat := 1\n"
            "-- import Mathlib.NumberTheory.LucasLehmer\n"
        )
        header, body, parsed = pmi.split_header_body(src)
        self.assertEqual(len(parsed), 7)
        mods = [(m, pub, exo) for _, m, pub, exo in parsed]
        self.assertEqual(
            mods,
            [
                ("Mathlib.Combinatorics.Enumerative.DyckWord", True, False),
                ("Mathlib.NumberTheory.LucasLehmer", False, True),
                ("Mathlib.NumberTheory.SelbergSieve", False, True),
                ("Mathlib.Data.NNRat.Floor", True, True),
                ("Mathlib.Algebra.Order.Interval.Basic", False, False),
                ("Mathlib.Combinatorics.Enumerative.DyckWord", False, False),
                ("Mathlib.LinearAlgebra.Matrix.Defs", False, False),
            ],
        )
        self.assertTrue(body.startswith("def foo : Nat := 1"))

        cat = {m: (w, c, g) for m, w, c, g in pmi.build_tier_catalog("core-32")}
        _, _, rem_idx, rem_mods = pmi.candidate_removals_for_file(src, cat, strict_static=False)
        self.assertEqual(
            rem_mods,
            [
                "Mathlib.Algebra.Order.Interval.Basic",
                "Mathlib.Combinatorics.Enumerative.DyckWord",
            ],
        )
        out = pmi.render_source(header, body, rem_idx)
        self.assertIn("public import Mathlib.Combinatorics.Enumerative.DyckWord -- keep public", out)
        self.assertIn("import all Mathlib.NumberTheory.LucasLehmer -- keep import all", out)
        self.assertIn("meta import Mathlib.NumberTheory.SelbergSieve -- keep meta", out)
        self.assertIn("public meta import Mathlib.Data.NNRat.Floor", out)
        self.assertIn("import Mathlib.LinearAlgebra.Matrix.Defs -- keep non-candidate", out)
        self.assertNotIn("private import Mathlib.Algebra.Order.Interval.Basic", out)
        self.assertNotIn("DyckWord--tight comment", out)
        # Body comment mentioning import must be untouched
        self.assertIn("-- import Mathlib.NumberTheory.LucasLehmer", out)

    def test_crlf_and_blank_lines_preserved(self):
        src = (
            "module\r\n"
            "\r\n"
            "public import Foo.Bar\r\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\r\n"
            "\r\n"
            "def x := 0\r\n"
        )
        cat = {m: (w, c, g) for m, w, c, g in pmi.build_tier_catalog("core-32")}
        header, body, rem_idx, rem_mods = pmi.candidate_removals_for_file(src, cat, strict_static=False)
        self.assertEqual(rem_mods, ["Mathlib.Combinatorics.Enumerative.DyckWord"])
        rendered = pmi.render_source(header, body, rem_idx, extra_imports=["Mathlib.Topology.Instances.Matrix"])
        self.assertEqual(
            rendered,
            "module\r\n"
            "\r\n"
            "public import Foo.Bar\r\n"
            "import Mathlib.Topology.Instances.Matrix\r\n"
            "\r\n"
            "def x := 0\r\n",
        )

    def test_empty_and_no_module_files(self):
        cat = {m: (w, c, g) for m, w, c, g in pmi.build_tier_catalog("ext-47")}
        _, _, idx0, mods0 = pmi.candidate_removals_for_file("", cat, strict_static=False)
        self.assertEqual((idx0, mods0), ([], []))

        no_mod = (
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "import Mathlib.Data.Nat.Basic\n"
            "theorem t : True := trivial\n"
        )
        header, body, idx1, mods1 = pmi.candidate_removals_for_file(no_mod, cat, strict_static=False)
        self.assertEqual(mods1, ["Mathlib.Combinatorics.Enumerative.DyckWord"])
        out = pmi.render_source(header, body, idx1)
        self.assertEqual(out, "import Mathlib.Data.Nat.Basic\ntheorem t : True := trivial\n")


class TestTiersAndProtection(unittest.TestCase):
    def test_tier_sizes_and_custom_tier(self):
        self.assertEqual(len(pmi.build_tier_catalog("core-32")), 32)
        self.assertEqual(len(pmi.build_tier_catalog("top-34")), 34)
        self.assertEqual(len(pmi.build_tier_catalog("ext-47")), 47)
        self.assertEqual(len(pmi.build_tier_catalog("all-48")), 48)
        with self.assertRaises(ValueError):
            pmi.build_tier_catalog("custom", None)

        with tempfile.TemporaryDirectory() as td:
            cf = Path(td) / "custom.txt"
            write_text(cf, "# comment\nMathlib.Foo\n\nMathlib.Bar # inline\nMathlib.Foo\n")
            cat = pmi.build_tier_catalog("custom", str(cf))
            self.assertEqual([m for m, *_ in cat], ["Mathlib.Foo", "Mathlib.Bar"])

    def test_type_star_guard_and_strict_static_ignores_clump_headers(self):
        cat48 = {m: (w, c, g) for m, w, c, g in pmi.build_tier_catalog("all-48")}
        uses_typestar = (
            "module\n"
            "import Mathlib.Tactic.TypeStar\n"
            "import Mathlib.Tactic.NormNum.Parity\n"
            "def f (α : Type*) := α\n"
        )
        _, _, _, rem = pmi.candidate_removals_for_file(uses_typestar, cat48, strict_static=False)
        self.assertEqual(rem, ["Mathlib.Tactic.NormNum.Parity"])

        no_typestar = (
            "module\n"
            "import Mathlib.Tactic.TypeStar\n"
            "import Mathlib.Tactic.NormNum.Parity\n"
            "def f (α : Type) := α\n"
        )
        _, _, _, rem2 = pmi.candidate_removals_for_file(no_typestar, cat48, strict_static=False)
        self.assertEqual(rem2, ["Mathlib.Tactic.TypeStar", "Mathlib.Tactic.NormNum.Parity"])

        # Strict-static preserves NormNum.Parity when body has both norm_num & Even
        uses_parity = (
            "module\n"
            "import Mathlib.Tactic.NormNum.Parity\n"
            "theorem t : Even 2 := by norm_num\n"
        )
        _, _, _, rem3 = pmi.candidate_removals_for_file(uses_parity, cat48, strict_static=True)
        self.assertEqual(rem3, [])

        # Embedded clump-header comment mentioning UpperHalfPlane / Gamma must NOT trip strict-static
        clump_body = (
            "module\n"
            "import Mathlib.Analysis.Complex.UpperHalfPlane.Basic\n"
            "import Mathlib.Analysis.SpecialFunctions.Gamma.Basic\n"
            "-- clump-header: {\"m\":\"A.B\",\"h\":\"import Mathlib.Analysis.Complex.UpperHalfPlane.Basic\\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\"}\n"
            "theorem ok : True := trivial\n"
        )
        _, _, _, rem4 = pmi.candidate_removals_for_file(clump_body, cat48, strict_static=True)
        self.assertEqual(
            rem4,
            [
                "Mathlib.Analysis.Complex.UpperHalfPlane.Basic",
                "Mathlib.Analysis.SpecialFunctions.Gamma.Basic",
            ],
        )

    def test_lib_of_and_ground_theory_fields_lean_cmd(self):
        self.assertEqual(pmi.lib_of("Main"), "Main")
        self.assertEqual(pmi.lib_of("Statements"), "Main")
        self.assertEqual(pmi.lib_of("Challenge"), "Challenge")
        self.assertEqual(pmi.lib_of("GroundTheory.LocalFields.Foo"), "GroundTheoryFields")
        self.assertEqual(pmi.lib_of("GroundTheory.GlobalFields.Adele.Topology"), "GroundTheoryFields")
        self.assertEqual(pmi.lib_of("GroundTheory.AutomorphicForms.AdelicGLn"), "GroundTheory")

        cmd_normal = pmi.build_lean_cmd("/tmp/r", "/tmp/r/A.lean", "Formalism.A")
        self.assertIn("-Dpp.unicode.fun=true", cmd_normal)
        self.assertNotIn("-DsynthInstance.maxHeartbeats=400000", cmd_normal)
        cmd_gtf = pmi.build_lean_cmd("/tmp/r", "/tmp/r/A.lean", "GroundTheory.GlobalFields.A")
        self.assertIn("-Dpp.unicode.fun=true", cmd_gtf)
        self.assertIn("-DsynthInstance.maxHeartbeats=400000", cmd_gtf)

    def test_frozen_challenge_files_always_protected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for rel in pmi.FROZEN_CHALLENGE_FILES:
                self.assertTrue(pmi.is_frozen_challenge_file(str(root), str(root / rel)))
            self.assertFalse(pmi.is_frozen_challenge_file(str(root), str(root / "src/Formalism/X.lean")))


class TestVerifyAndRepair(unittest.TestCase):
    def _prep(self, text: str, tier: str = "ext-47"):
        cat = {m: (w, c, g) for m, w, c, g in pmi.build_tier_catalog(tier)}
        header, body, rem_idx, rem_mods = pmi.candidate_removals_for_file(text, cat, strict_static=False)
        return cat, header, body, rem_idx, rem_mods

    def test_clean_full_prune(self):
        src = (
            "module\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "import Mathlib.NumberTheory.LucasLehmer\n"
            "theorem ok : True := trivial\n"
        )
        cat, header, body, rem_idx, rem_mods = self._prep(src)
        with tempfile.TemporaryDirectory() as td:
            mindex = pmi.MathlibIndex(td)
            runner = lambda text, rel, mod, env, tmp: (0, 0.01, [], [], "")
            res = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=True, smart_replace=True, max_restore=4, runner=runner,
            )
            self.assertEqual(res["status"], "passed")
            self.assertEqual(res["reason"], "clean_full_prune")
            self.assertEqual(res["removed_mods"], rem_mods)
            self.assertEqual(res["restored_mods"], [])
            self.assertEqual(res["lean_calls"], 2)  # baseline + pruned

    def test_smart_symbol_replace_picks_smallest_defining_module(self):
        src = (
            "module\n"
            "import Mathlib.Geometry.Euclidean.Volume.Basic\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "theorem ok : True := trivial\n"
        )
        cat, header, body, rem_idx, rem_mods = self._prep(src)
        with tempfile.TemporaryDirectory() as td:
            # Create a tiny fake Mathlib tree where two modules define `Continuous.dotProduct`,
            # one tiny (1 mod) and one larger (3 mods).
            mdir = Path(td) / ".lake" / "packages" / "mathlib" / "Mathlib"
            write_text(mdir / "BaseA.lean", "module\n")
            write_text(mdir / "BaseB.lean", "module\npublic import Mathlib.BaseA\n")
            write_text(
                mdir / "Big.lean",
                "module\npublic import Mathlib.BaseB\nprotected theorem Continuous.dotProduct : True := trivial\n",
            )
            write_text(
                mdir / "Small.lean",
                "module\nprotected theorem Continuous.dotProduct : True := trivial\n",
            )
            mindex = pmi.MathlibIndex(td)

            def fake_runner(text, rel, mod, env, tmp):
                if (
                    "import Mathlib.Small" in text
                    or "import Mathlib.Geometry.Euclidean.Volume.Basic" in text
                ):
                    return (0, 0.01, [], [], "")
                err = "Foo.lean:10:5: error: The environment does not contain `Continuous.dotProduct`"
                return (1, 0.01, [], [err], err)

            res = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=True, smart_replace=True, max_restore=4, runner=fake_runner,
            )
            self.assertEqual(res["status"], "repaired")
            self.assertEqual(res["reason"], "smart_symbol_replace")
            self.assertEqual(res["added_mods"], ["Mathlib.Small"])
            self.assertEqual(res["restored_mods"], [])
            self.assertIn("import Mathlib.Small", res["final_text"])
            self.assertNotIn("Volume.Basic", res["final_text"])

    def test_ddmin_restore_prefers_smaller_closure_and_handles_multi_restore(self):
        src = (
            "module\n"
            "import Mathlib.NumberTheory.Height.NumberField\n"
            "import Mathlib.Tactic.NormNum.Parity\n"
            "import Mathlib.Tactic.NormNum.Prime\n"
            "import Mathlib.Geometry.Euclidean.Volume.Basic\n"
            "theorem ok : True := trivial\n"
        )
        cat, header, body, rem_idx, rem_mods = self._prep(src)
        with tempfile.TemporaryDirectory() as td:
            mindex = pmi.MathlibIndex(td)

            # Case 1: either NormNum.Parity (208m) OR Height.NumberField (3153m) fixes it -> must pick Parity!
            def runner_either(text, rel, mod, env, tmp):
                if "NormNum.Parity" in text or "Height.NumberField" in text:
                    return (0, 0.01, [], [], "")
                return (1, 0.01, [], ["error: synthInstanceFailed"], "error: synthInstanceFailed")

            res1 = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=False, smart_replace=False, max_restore=4, runner=runner_either,
            )
            self.assertEqual(res1["status"], "repaired")
            self.assertEqual(res1["reason"], "ddmin_restore")
            self.assertEqual(res1["restored_mods"], ["Mathlib.Tactic.NormNum.Parity"])
            self.assertEqual(len(res1["removed_mods"]), 3)

            # Case 2: BOTH NormNum.Parity AND NormNum.Prime are required
            def runner_both(text, rel, mod, env, tmp):
                if "NormNum.Parity" in text and "NormNum.Prime" in text:
                    return (0, 0.01, [], [], "")
                return (1, 0.01, [], ["error: failed"], "error: failed")

            res2 = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=False, smart_replace=False, max_restore=4, runner=runner_both,
            )
            self.assertEqual(res2["status"], "repaired")
            self.assertEqual(
                res2["restored_mods"],
                ["Mathlib.Tactic.NormNum.Parity", "Mathlib.Tactic.NormNum.Prime"],
            )
            self.assertEqual(len(res2["removed_mods"]), 2)

    def test_warning_regression_and_unchanged_fallbacks(self):
        src = (
            "module\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "import Mathlib.Tactic.NormNum.Parity\n"
            "theorem ok : True := trivial\n"
        )
        cat, header, body, rem_idx, rem_mods = self._prep(src)
        with tempfile.TemporaryDirectory() as td:
            mindex = pmi.MathlibIndex(td)

            # Removing NormNum.Parity introduces an extra warning -> must restore Parity, drop DyckWord
            def runner_warn(text, rel, mod, env, tmp):
                warns = ["Foo.lean:1:1: warning: existing"]
                if "NormNum.Parity" not in text:
                    warns.append("Foo.lean:2:1: warning: new")
                return (0, 0.01, warns, [], "\n".join(warns))

            res_w = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=True, smart_replace=False, max_restore=4, runner=runner_warn,
            )
            self.assertEqual(res_w["status"], "repaired")
            self.assertEqual(res_w["restored_mods"], ["Mathlib.Tactic.NormNum.Parity"])
            self.assertEqual(res_w["removed_mods"], ["Mathlib.Combinatorics.Enumerative.DyckWord"])
            self.assertEqual((res_w["warn_before"], res_w["warn_after"]), (1, 1))

            # Baseline failure -> unchanged immediately
            runner_fail = lambda text, rel, mod, env, tmp: (1, 0.01, [], ["error"], "error")
            res_f = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=True, smart_replace=False, max_restore=4, runner=runner_fail,
            )
            self.assertEqual(res_f["status"], "unchanged")
            self.assertEqual(res_f["reason"], "baseline_failed")
            self.assertEqual(res_f["final_text"], src)

            # All candidate imports required -> unchanged fallback (no point rewriting if 0 removed)
            def runner_need_all(text, rel, mod, env, tmp):
                if "DyckWord" in text and "NormNum.Parity" in text:
                    return (0, 0.01, [], [], "")
                return (1, 0.01, [], ["error"], "error")

            res_all = pmi.verify_and_repair(
                src, header, body, rem_idx, rem_mods, "Foo.lean", "Foo",
                {}, mindex, cat, check_warnings=False, smart_replace=False, max_restore=4, runner=runner_need_all,
            )
            self.assertEqual(res_all["status"], "unchanged")
            self.assertEqual(res_all["reason"], "repair_failed_or_full_restore")
            self.assertEqual(res_all["final_text"], src)


class TestCLI(unittest.TestCase):
    def _make_repo(self, td: str) -> Path:
        root = Path(td)
        write_text(
            root / "src" / "Formalism" / "A.lean",
            "module\n"
            "public import Mathlib.LinearAlgebra.Matrix.Defs\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "import Mathlib.NumberTheory.Height.NumberField\n"
            "def a := 1\n",
        )
        write_text(
            root / "src" / "Formalism" / "B.lean",
            "module\n"
            "import Mathlib.Combinatorics.Enumerative.DyckWord\n"
            "def b := 2\n",
        )
        write_text(
            root / "src" / "Formalism" / "Clean.lean",
            "module\n"
            "public import Mathlib.LinearAlgebra.Matrix.Defs\n"
            "def c := 3\n",
        )
        write_text(
            root / "src" / "Main.lean",
            "module\nimport Mathlib.Combinatorics.Enumerative.DyckWord\ndef m := 0\n",
        )
        write_text(
            root / "src" / "Challenge.lean",
            "module\nimport Mathlib.Combinatorics.Enumerative.DyckWord\ndef ch := 0\n",
        )
        write_text(
            root / "comparator" / "FormalConjecturesChallenge.lean",
            "module\nimport Mathlib.Combinatorics.Enumerative.DyckWord\ndef fc := 0\n",
        )
        return root

    def _run_cli(self, argv: list[str]) -> str:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(io.StringIO()):
            pmi.main(argv)
        return buf.getvalue()

    def test_dry_run_no_mutation_and_exclude(self):
        with tempfile.TemporaryDirectory() as td:
            root = self._make_repo(td)
            ex = root / "exclude.txt"
            write_text(ex, "Formalism.B\n")
            rep = root / "report.json"
            orig_a = read_text(root / "src" / "Formalism" / "A.lean")

            out = self._run_cli([
                "--root", str(root),
                "--tier", "ext-47",
                "--exclude", str(ex),
                "--dry-run",
                "--json-report", str(rep),
            ])
            self.assertIn("Files processed:           1", out)
            self.assertIn("Skipped (protected):     2", out)
            self.assertIn("Skipped (excluded):      1", out)
            self.assertIn("Skipped (no candidates): 1", out)
            self.assertEqual(read_text(root / "src" / "Formalism" / "A.lean"), orig_a)
            data = json.loads(read_text(rep))
            self.assertEqual(len(data), 1)
            self.assertEqual(data[0]["module"], "Formalism.A")
            self.assertEqual(data[0]["removed_count"], 2)

    def test_apply_idempotency_and_out_dir_and_frozen_protection(self):
        with tempfile.TemporaryDirectory() as td:
            root = self._make_repo(td)
            out_dir = root / "mirror"
            orig_a = read_text(root / "src" / "Formalism" / "A.lean")
            orig_ch = read_text(root / "src" / "Challenge.lean")
            orig_fc = read_text(root / "comparator" / "FormalConjecturesChallenge.lean")

            # 1. --out-dir writes mirror without mutating src/
            self._run_cli([
                "--root", str(root),
                "--tier", "core-32",
                "--out-dir", str(out_dir),
                "--apply",
            ])
            self.assertEqual(read_text(root / "src" / "Formalism" / "A.lean"), orig_a)
            mirror_a = read_text(out_dir / "Formalism" / "A.lean")
            self.assertNotIn("DyckWord", mirror_a)
            # core-32 must NOT drop Height.NumberField (rank #33)
            self.assertIn("Height.NumberField", mirror_a)

            # 2. Frozen challenge files stay untouched even with --paths and --include-protected
            self._run_cli([
                "--root", str(root),
                "--paths",
                str(root / "src" / "Challenge.lean"),
                str(root / "comparator" / "FormalConjecturesChallenge.lean"),
                "--include-protected",
                "--tier", "ext-47",
                "--apply",
            ])
            self.assertEqual(read_text(root / "src" / "Challenge.lean"), orig_ch)
            self.assertEqual(read_text(root / "comparator" / "FormalConjecturesChallenge.lean"), orig_fc)

            # 3. In-place --apply + strict idempotency on second run
            out1 = self._run_cli(["--root", str(root), "--tier", "ext-47", "--apply"])
            self.assertIn("Files processed:           2", out1)
            after_a = read_text(root / "src" / "Formalism" / "A.lean")
            self.assertNotIn("DyckWord", after_a)
            self.assertNotIn("Height.NumberField", after_a)
            self.assertIn("public import Mathlib.LinearAlgebra.Matrix.Defs", after_a)

            out2 = self._run_cli(["--root", str(root), "--tier", "ext-47", "--apply"])
            self.assertIn("Files processed:           0", out2)
            self.assertIn("Net import lines removed:  0 (-0 / +0)", out2)
            self.assertEqual(read_text(root / "src" / "Formalism" / "A.lean"), after_a)
            # Main.lean remained protected
            self.assertIn("DyckWord", read_text(root / "src" / "Main.lean"))

    def test_custom_tier_cli_and_arg_validation(self):
        with tempfile.TemporaryDirectory() as td:
            root = self._make_repo(td)
            custom_file = root / "custom.txt"
            write_text(custom_file, "# custom list\nMathlib.NumberTheory.Height.NumberField\n")
            out = self._run_cli([
                "--root", str(root),
                "--tier", "custom",
                "--custom-imports", str(custom_file),
                "--apply",
            ])
            self.assertIn("Files processed:           1", out)
            after_a = read_text(root / "src" / "Formalism" / "A.lean")
            self.assertIn("DyckWord", after_a)
            self.assertNotIn("Height.NumberField", after_a)

            with self.assertRaises(SystemExit):
                self._run_cli(["--root", str(root), "--dry-run", "--apply"])
            with self.assertRaises(SystemExit):
                self._run_cli(["--root", str(root), "--tier", "custom", "--dry-run"])
            with self.assertRaises(SystemExit):
                self._run_cli([
                    "--root", str(root),
                    "--tier", "core-32",
                    "--custom-imports", str(custom_file),
                    "--dry-run",
                ])

    def test_relative_dir_resolves_against_root(self):
        with tempfile.TemporaryDirectory() as td:
            root = self._make_repo(td)
            write_text(
                root / "src" / "Other" / "Z.lean",
                "module\nimport Mathlib.Combinatorics.Enumerative.DyckWord\ndef z := 9\n",
            )
            rep = root / "dir_report.json"
            out = self._run_cli([
                "--root", str(root),
                "--dir", "src/Formalism",
                "--tier", "ext-47",
                "--dry-run",
                "--json-report", str(rep),
            ])
            self.assertIn("Files discovered:          3", out)
            self.assertIn("Files processed:           2", out)
            mods = [r["module"] for r in json.loads(read_text(rep))]
            self.assertEqual(mods, ["Formalism.A", "Formalism.B"])


if __name__ == "__main__":
    unittest.main()
