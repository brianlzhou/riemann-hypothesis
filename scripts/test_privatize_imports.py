#!/usr/bin/env python3
"""Unit tests for `scripts/privatize_imports.py` (stdlib only, no Lean invocation)."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("privatize_imports.py")
spec = importlib.util.spec_from_file_location("privatize_imports", SCRIPT)
pi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pi)

CLUMP_SCRIPT = Path(__file__).with_name("clump.py")
clump_spec = importlib.util.spec_from_file_location("clump", CLUMP_SCRIPT)
clump = importlib.util.module_from_spec(clump_spec)
clump_spec.loader.exec_module(clump)


def write_tree(root, files):
    """Create `src/<rel>` files under `root` from dict `{rel_path: content}`."""
    root = Path(root)
    for rel, content in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")


def make_clump(header_lines, members):
    """Build a clump file matching `scripts/clump.py` seam format.

    `members` is a list of `(mod_name, orig_header_str, body_str)`.
    """
    out = ["module", ""] + list(header_lines) + [
        "",
        "-- This file was produced by scripts/clump.py from the modules listed below.",
        "-- Members: " + ", ".join(m for m, _, _ in members),
        "",
    ]
    for name, orig_hdr, body in members:
        info = {"m": name, "h": orig_hdr}
        out.append(pi.SEAM_BEGIN + name + " =====")
        out.append(pi.HEADER_TAG + json.dumps(info))
        out.append("section" + pi.AUTO)
        out.append(body.rstrip("\n"))
        out.append("end" + pi.AUTO)
        out.append("end" + pi.AUTO)
        out.append(pi.SEAM_END + name + " =====")
        out.append("")
    return "\n".join(out)


class TestHeaderParsing(unittest.TestCase):
    def test_trailing_and_standalone_comments(self):
        lines = [
            "module",
            "-- header note",
            "",
            "public import Foo.Bar  -- keep this comment",
            "public import Foo.Baz--no-space comment",
            "import Qux -- private comment",
            "private import Quux",
            "@[expose] public section",
        ]
        imps, body_start, exotic = pi.parse_header_imports(lines)
        self.assertFalse(exotic)
        self.assertEqual(body_start, 7)
        self.assertEqual(
            [(m, pub, c) for _, m, pub, _, c in imps],
            [
                ("Foo.Bar", True, "  -- keep this comment"),
                ("Foo.Baz", True, "--no-space comment"),
                ("Qux", False, " -- private comment"),
                ("Quux", False, ""),
            ],
        )

    def test_exotic_import_detection(self):
        for hdr in (
            ["module", "import all Foo.Bar", "public section"],
            ["module", "public meta import Foo.Bar", "public section"],
        ):
            _, _, exotic = pi.parse_header_imports(hdr)
            self.assertTrue(exotic, hdr)


class TestRuleAStrictVsPromote(unittest.TestCase):
    def test_strict_demotes_when_covered_and_blocks_when_uncovered(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/Defs.lean": (
                    "module\n\n@[expose] public section\n"
                    "def myVal : Nat := 1\n"
                ),
                "src/Pkg/Thm.lean": (
                    "module\n\npublic import Pkg.Defs\n\n@[expose] public section\n"
                    "theorem thm_val : myVal = 1 := rfl\n"
                ),
                # Covered: directly has `public import Pkg.Defs` too -> strict demotes Pkg.Thm!
                "src/Pkg/Covered.lean": (
                    "module\n\npublic import Pkg.Defs\npublic import Pkg.Thm  -- keep note\n\n"
                    "@[expose] public section\n"
                    "theorem cov : myVal = 1 := by exact thm_val\n"
                ),
                # Uncovered: relies on Pkg.Thm to re-export Pkg.Defs -> strict keeps, promote lifts Pkg.Defs!
                "src/Pkg/Uncovered.lean": (
                    "module\n\npublic import Pkg.Thm\n\n"
                    "@[expose] public section\n"
                    "theorem uncov : myVal = 1 := by exact thm_val\n"
                ),
            })

            strict = pi.build_plan(td, rules="a", mode="strict", exclude=frozenset())
            u_cov = strict["mod_idx"]["Pkg.Covered"]
            u_unc = strict["mod_idx"]["Pkg.Uncovered"]
            self.assertEqual(strict["rule_a_demoted"].get(u_cov), {"Pkg.Thm"})
            self.assertNotIn(u_unc, strict["rule_a_demoted"])
            self.assertEqual(strict["rule_a_promoted"], {})

            # Trailing comment preserved on demoted import
            orig_cov = (Path(td) / "src/Pkg/Covered.lean").read_text(encoding="utf-8")
            new_cov, changed, _ = pi.transform_file_text(u_cov, orig_cov, strict)
            self.assertTrue(changed)
            self.assertIn("import Pkg.Thm  -- keep note", new_cov)
            self.assertNotIn("public import Pkg.Thm", new_cov)

            # Promote mode demotes Pkg.Thm in Uncovered AND lifts `public import Pkg.Defs`
            prom = pi.build_plan(td, rules="a", mode="promote", exclude=frozenset())
            self.assertEqual(prom["rule_a_demoted"].get(u_unc), {"Pkg.Thm"})
            self.assertEqual(prom["rule_a_promoted"].get(u_unc), ["Pkg.Defs"])
            orig_unc = (Path(td) / "src/Pkg/Uncovered.lean").read_text(encoding="utf-8")
            new_unc, changed, info = pi.transform_file_text(u_unc, orig_unc, prom)
            self.assertTrue(changed)
            self.assertEqual(info["demoted"], 1)
            self.assertEqual(info["promoted"], 1)
            self.assertIn("public import Pkg.Defs", new_unc)
            self.assertIn("\nimport Pkg.Thm\n", new_unc)

    def test_promote_upgrades_existing_private_import_in_place(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/Defs.lean": "module\n\n@[expose] public section\ndef x : Nat := 0\n",
                "src/Pkg/Thm.lean": "module\n\npublic import Pkg.Defs\n\npublic section\ntheorem t : x = 0 := rfl\n",
                "src/Pkg/User.lean": (
                    "module\n\npublic import Pkg.Thm\nimport Pkg.Defs -- priv note\n\n"
                    "public section\ntheorem u : x = 0 := by exact t\n"
                ),
            })
            prom = pi.build_plan(td, rules="a", mode="promote", exclude=frozenset())
            u_user = prom["mod_idx"]["Pkg.User"]
            orig = (Path(td) / "src/Pkg/User.lean").read_text(encoding="utf-8")
            new_txt, changed, _ = pi.transform_file_text(u_user, orig, prom)
            self.assertTrue(changed)
            self.assertEqual(new_txt.count("Pkg.Defs"), 1)
            self.assertIn("public import Pkg.Defs -- priv note", new_txt)
            self.assertIn("import Pkg.Thm", new_txt)

    def test_strict_cascades_bottom_up(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/T0.lean": "module\n\npublic section\ntheorem t0 : True := trivial\n",
                "src/Pkg/T1.lean": "module\n\npublic import Pkg.T0\n\npublic section\ntheorem t1 : True := by exact t0\n",
                "src/Pkg/T2.lean": "module\n\npublic import Pkg.T1\n\npublic section\ntheorem t2 : True := by exact t1\n",
            })
            strict = pi.build_plan(td, rules="a", mode="strict", exclude=frozenset())
            # T1 demotes T0 first, so T1 has 0 remaining public imports -> T2 can also demote T1 strictly!
            self.assertEqual(strict["rule_a_demoted"].get(strict["mod_idx"]["Pkg.T1"]), {"Pkg.T0"})
            self.assertEqual(strict["rule_a_demoted"].get(strict["mod_idx"]["Pkg.T2"]), {"Pkg.T1"})


class TestRuleAGuards(unittest.TestCase):
    def test_public_surface_vs_proof_body_guard(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/B.lean": "module\n\npublic section\ntheorem b_ok : 1 + 1 = 2 := rfl\n",
                # Direct term-mode reference inside @[expose] def body -> MUST stay public
                "src/Pkg/ExposeDefRef.lean": (
                    "module\n\npublic import Pkg.B\n\n@[expose] public section\n"
                    "def pair : { n : Nat // n = 2 } := ⟨1 + 1, b_ok⟩\n"
                ),
                # Reference in theorem TYPE signature -> MUST stay public
                "src/Pkg/ThmSigRef.lean": (
                    "module\n\npublic import Pkg.B\n\npublic section\n"
                    "theorem sig_ref\n    (h : b_ok = b_ok) : True := by\n  trivial\n"
                ),
                # Reference ONLY in theorem proof body -> SAFE to demote
                "src/Pkg/ThmProofRef.lean": (
                    "module\n\npublic import Pkg.B\n\n@[expose] public section\n"
                    "theorem pf_ref\n    (n : Nat) : 1 + 1 = 2 := by\n  exact b_ok\n"
                ),
                # Reference in non-expose `public section` def body -> SAFE to demote
                "src/Pkg/OpaqueDefBodyRef.lean": (
                    "module\n\npublic import Pkg.B\n\npublic section\n"
                    "def opaque_pair : { n : Nat // n = 2 } :=\n  ⟨1 + 1, b_ok⟩\n"
                ),
            })
            plan = pi.build_plan(td, rules="a", mode="strict", exclude=frozenset())
            self.assertNotIn(plan["mod_idx"]["Pkg.ExposeDefRef"], plan["rule_a_demoted"])
            self.assertNotIn(plan["mod_idx"]["Pkg.ThmSigRef"], plan["rule_a_demoted"])
            self.assertEqual(plan["rule_a_demoted"].get(plan["mod_idx"]["Pkg.ThmProofRef"]), {"Pkg.B"})
            self.assertEqual(plan["rule_a_demoted"].get(plan["mod_idx"]["Pkg.OpaqueDefBodyRef"]), {"Pkg.B"})

    def test_global_side_effect_guard_vs_local_attributes(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/SimpMod.lean": "module\n\npublic section\n@[simp] theorem s1 : True := trivial\n",
                "src/Pkg/ExtMod.lean": "module\n\npublic section\n@[ext] theorem e1 : True := trivial\n",
                "src/Pkg/InstMod.lean": "module\n\npublic section\ninstance : Inhabited Unit := ⟨()⟩\n",
                "src/Pkg/StructMod.lean": "module\n\npublic section\nstructure Box where x : Nat\n",
                "src/Pkg/NotationMod.lean": "module\n\npublic section\nnotation \"MY_UNIT\" => ()\n",
                "src/Pkg/GlobalAttrMod.lean": (
                    "module\n\npublic section\ntheorem g1 : True := trivial\nattribute [simp] g1\n"
                ),
                "src/Pkg/LocalAttrMod.lean": (
                    "module\n\npublic section\n"
                    "attribute [local instance] instInhabitedNat\n"
                    "attribute [local simp] Nat.add_zero\n"
                    "@[deprecated, nolint] theorem loc1 : True := trivial\n"
                ),
                "src/Pkg/User.lean": (
                    "module\n\n"
                    "public import Pkg.SimpMod\n"
                    "public import Pkg.ExtMod\n"
                    "public import Pkg.InstMod\n"
                    "public import Pkg.StructMod\n"
                    "public import Pkg.NotationMod\n"
                    "public import Pkg.GlobalAttrMod\n"
                    "public import Pkg.LocalAttrMod\n\n"
                    "public section\ntheorem u : True := by exact loc1\n"
                ),
            })
            plan = pi.build_plan(td, rules="a", mode="strict", exclude=frozenset())
            for blocked in ("Pkg.SimpMod", "Pkg.ExtMod", "Pkg.InstMod", "Pkg.StructMod",
                            "Pkg.NotationMod", "Pkg.GlobalAttrMod"):
                self.assertNotIn(plan["mod_idx"][blocked], plan["pure_safe"], blocked)
            self.assertIn(plan["mod_idx"]["Pkg.LocalAttrMod"], plan["pure_safe"])
            self.assertEqual(
                plan["rule_a_demoted"].get(plan["mod_idx"]["Pkg.User"]),
                {"Pkg.LocalAttrMod"},
            )

    def test_downstream_direct_user_guard(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/B1.lean": "module\n\npublic section\ntheorem b1_thm : True := trivial\n",
                "src/Pkg/B2.lean": "module\n\npublic section\ntheorem b2_thm : True := trivial\n",
                "src/Pkg/A.lean": (
                    "module\n\npublic import Pkg.B1\npublic import Pkg.B2\n\n"
                    "public section\ntheorem a_thm : True := trivial\n"
                ),
                # D imports ONLY A, uses b1_thm transitively -> blocks demoting (A, B1)!
                # D directly imports B2 as well -> does NOT block demoting (A, B2)!
                "src/Pkg/D.lean": (
                    "module\n\nimport Pkg.A\nimport Pkg.B2\n\n"
                    "public section\ntheorem d_thm : True := by have _ := b1_thm; exact b2_thm\n"
                ),
            })
            plan = pi.build_plan(td, rules="a", mode="strict", exclude=frozenset())
            u_a = plan["mod_idx"]["Pkg.A"]
            self.assertEqual(plan["rule_a_demoted"].get(u_a), {"Pkg.B2"})


class TestRuleBClumps(unittest.TestCase):
    def test_clump_b1_and_b2_privatization_and_unclump_compat(self):
        with tempfile.TemporaryDirectory() as td:
            m_b1_hdr = "module\n\npublic import Pkg.ExtB1\n\n"
            m_b2_hdr = "module\n\npublic import Pkg.ExtB2\npublic import Pkg.ExtShared\n\n"
            m_root_hdr = (
                "module\n\nimport Pkg.M_B1\npublic import Pkg.M_B2\n"
                "public import Pkg.ExtShared\n\n"
            )
            clump_text = make_clump(
                [
                    "public import Pkg.ExtB1",
                    "public import Pkg.ExtB2",
                    "public import Pkg.ExtShared",
                ],
                [
                    ("Pkg.M_B1", m_b1_hdr,
                     "@[expose] public section\n/- @[expose] public section -/\ndef b1_helper : Nat := 1\ntheorem b1_pf : b1_helper = 1 := rfl\n"),
                    ("Pkg.M_B2", m_b2_hdr,
                     "public section\ndef b2_helper : Nat := 2\ntheorem b2_pf : b2_helper = 2 := rfl\n"),
                    ("Pkg.ClumpRoot", m_root_hdr,
                     "@[expose] public section\ntheorem root_thm : True := by have _ := b1_pf; have _ := b2_pf; trivial\n"),
                ],
            )
            write_tree(td, {
                "src/Pkg/ExtB1.lean": "module\n\n@[expose] public section\ndef e1 : Nat := 1\n",
                "src/Pkg/ExtB2.lean": "module\n\n@[expose] public section\ndef e2 : Nat := 2\n",
                "src/Pkg/ExtShared.lean": "module\n\n@[expose] public section\ndef es : Nat := 3\n",
                "src/Pkg/ClumpRoot.lean": clump_text,
            })

            # Default mode: both B1 and B2 members privatized; ExtB1 (B1-only) demoted; ExtB2 (uncovered B2-lifted) kept
            plan = pi.build_plan(td, rules="bc", mode="strict", exclude=frozenset())
            u_c = plan["mod_idx"]["Pkg.ClumpRoot"]
            self.assertEqual(plan["clump_privatized_members"].get(u_c), {0, 1})
            self.assertEqual(plan["clump_demoted_imports"].get(u_c), {"Pkg.ExtB1"})
            # Clump root is pure-theorem after Rule B privatizes def-bearing members -> pure_safe!
            self.assertIn(u_c, plan["pure_safe"])

            new_txt, changed, info = pi.transform_file_text(u_c, clump_text, plan)
            self.assertTrue(changed)
            self.assertEqual(info["b_sections"], 2)
            self.assertEqual(info["c_exposes"], 1)
            self.assertIn("\nimport Pkg.ExtB1\n", new_txt)
            self.assertIn("\npublic import Pkg.ExtB2\n", new_txt)
            self.assertIn("\npublic import Pkg.ExtShared\n", new_txt)
            # Block comment `@[expose] public section` must remain untouched!
            self.assertIn("/- @[expose] public section -/", new_txt)
            # `scripts/clump.py unclump_text` still parses the privatized clump cleanly!
            unclumped = clump.unclump_text(new_txt)
            self.assertEqual(set(unclumped.keys()), {"Pkg.M_B1", "Pkg.M_B2", "Pkg.ClumpRoot"})
            self.assertIn("\nsection\n", unclumped["Pkg.M_B1"])
            self.assertIn("\npublic section\n", unclumped["Pkg.ClumpRoot"])

            # With --clump-demote-lifted, ExtB2 is ALSO demoted!
            plan_lifted = pi.build_plan(
                td, rules="b", mode="strict", exclude=frozenset(), clump_demote_lifted=True
            )
            self.assertEqual(plan_lifted["clump_demoted_imports"].get(u_c), {"Pkg.ExtB1", "Pkg.ExtB2"})

            # With --clump-pure-only, def-bearing B1/B2 members are skipped!
            plan_pure = pi.build_plan(
                td, rules="b", mode="strict", exclude=frozenset(), clump_pure_only=True
            )
            self.assertNotIn(u_c, plan_pure["clump_privatized_members"])

    def test_clump_guards_pub_surface_external_user_and_unfold_risk(self):
        with tempfile.TemporaryDirectory() as td:
            clump_text = make_clump(
                ["public import Pkg.Ext"],
                [
                    # M0: referenced in root's public signature -> MUST stay public
                    ("Pkg.M0", "module\n\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ndef pub_ty : Nat := 0\n"),
                    # M1: referenced by external downstream file Pkg.Consumer -> MUST stay public
                    ("Pkg.M1", "module\n\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ntheorem ext_used_thm : True := trivial\n"),
                    # M2: has `def` with `by` + `unfold` (abstractProofs risk) -> MUST stay public
                    ("Pkg.M2", "module\n\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ndef risky : { n : Nat // n = 0 } := ⟨0, by rfl⟩\n"
                     "theorem use_risky : risky.1 = 0 := by unfold risky; rfl\n"),
                    # M3: clean private helper -> CAN be privatized
                    ("Pkg.M3", "module\n\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ntheorem safe_helper : True := trivial\n"),
                    ("Pkg.Root", "module\n\npublic import Pkg.M0\npublic import Pkg.M1\npublic import Pkg.M2\npublic import Pkg.M3\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ntheorem root_t : pub_ty = 0 := by have _ := safe_helper; rfl\n"),
                ],
            )
            write_tree(td, {
                "src/Pkg/Ext.lean": "module\n\n@[expose] public section\ndef ext_x : Nat := 0\n",
                "src/Pkg/Root.lean": clump_text,
                "src/Pkg/Consumer.lean": (
                    "module\n\nimport Pkg.Root\n\npublic section\n"
                    "theorem c : True := by exact ext_used_thm\n"
                ),
            })
            plan = pi.build_plan(td, rules="b", mode="strict", exclude=frozenset())
            u_r = plan["mod_idx"]["Pkg.Root"]
            # ONLY M3 (index 3) may be privatized!
            self.assertEqual(plan["clump_privatized_members"].get(u_r), {3})


class TestProtectionsAndCLI(unittest.TestCase):
    def test_protected_libs_exotic_and_exclude_untouched(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/Pure.lean": "module\n\n@[expose] public section\ntheorem p : True := trivial\n",
                "src/Main.lean": "module\n\npublic import Pkg.Pure\n\n@[expose] public section\ntheorem m : True := by exact p\n",
                "src/Statements.lean": "module\n\npublic import Pkg.Pure\n\n@[expose] public section\ntheorem s : True := by exact p\n",
                "src/Challenge.lean": "module\n\npublic import Pkg.Pure\n\n@[expose] public section\ntheorem ch : True := by exact p\n",
                "src/Pkg/Exotic.lean": "module\n\nimport all Pkg.Pure\n\n@[expose] public section\ntheorem ex : True := by exact p\n",
                "src/Pkg/Excluded.lean": "module\n\npublic import Pkg.Pure\n\n@[expose] public section\ntheorem exc : True := by exact p\n",
                "src/Pkg/Normal.lean": "module\n\npublic import Pkg.Pure\n\n@[expose] public section\ntheorem n : True := by exact p\n",
            })
            plan = pi.build_plan(td, rules="abc", mode="strict", exclude=frozenset({"Pkg.Excluded"}))
            for untouched in ("Main", "Statements", "Challenge", "Pkg.Exotic", "Pkg.Excluded"):
                u = plan["mod_idx"][untouched]
                self.assertNotIn(u, plan["rule_a_demoted"], untouched)
                self.assertNotIn(u, plan["rule_c_files"], untouched)
            u_norm = plan["mod_idx"]["Pkg.Normal"]
            self.assertEqual(plan["rule_a_demoted"].get(u_norm), {"Pkg.Pure"})
            self.assertIn(u_norm, plan["rule_c_files"])

    def test_dry_run_apply_idempotency_and_out_dir(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/Leaf.lean": "module\n\n@[expose] public section\ntheorem leaf : True := trivial\n",
                "src/Pkg/Mid.lean": (
                    "module\n\npublic import Pkg.Leaf\n\n@[expose] public section\n"
                    "theorem mid : True := by exact leaf\n"
                ),
            })
            before_leaf = (Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8")
            before_mid = (Path(td) / "src/Pkg/Mid.lean").read_text(encoding="utf-8")

            # 1. --dry-run does not modify files
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                pi.main(["--root", td, "--dry-run", "--stats", "--exclude", ""])
            self.assertEqual((Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8"), before_leaf)
            self.assertEqual((Path(td) / "src/Pkg/Mid.lean").read_text(encoding="utf-8"), before_mid)
            self.assertIn("Internal .olean loads", buf.getvalue())

            # 2. --out-dir writes transformed copies without mutating root
            out_dir = Path(td) / "out_copy"
            json_path = Path(td) / "report.json"
            with contextlib.redirect_stdout(io.StringIO()):
                pi.main(["--root", td, "--out-dir", str(out_dir), "--exclude", "", "--json", str(json_path)])
            self.assertEqual((Path(td) / "src/Pkg/Mid.lean").read_text(encoding="utf-8"), before_mid)
            self.assertIn("\nimport Pkg.Leaf\n", (out_dir / "src/Pkg/Mid.lean").read_text(encoding="utf-8"))
            self.assertIn("\npublic section\n", (out_dir / "src/Pkg/Leaf.lean").read_text(encoding="utf-8"))
            rep = json.loads(json_path.read_text(encoding="utf-8"))
            self.assertEqual(rep["n_mods"], 2)
            self.assertEqual(rep["rule_a_stats"]["demoted_edges"], 1)

            # 3. --apply mutates in place, and a second --apply is a strict no-op (idempotent!)
            buf1 = io.StringIO()
            with contextlib.redirect_stdout(buf1):
                pi.main(["--root", td, "--apply", "--exclude", ""])
            self.assertIn("Wrote 2 transformed files", buf1.getvalue())
            after_leaf = (Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8")
            after_mid = (Path(td) / "src/Pkg/Mid.lean").read_text(encoding="utf-8")
            self.assertIn("\nimport Pkg.Leaf\n", after_mid)
            self.assertNotIn("@[expose]", after_leaf)

            buf2 = io.StringIO()
            with contextlib.redirect_stdout(buf2):
                pi.main(["--root", td, "--apply", "--exclude", ""])
            self.assertIn("Wrote 0 transformed files", buf2.getvalue())
            self.assertEqual((Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8"), after_leaf)
            self.assertEqual((Path(td) / "src/Pkg/Mid.lean").read_text(encoding="utf-8"), after_mid)

    def test_clump_apply_idempotency(self):
        with tempfile.TemporaryDirectory() as td:
            clump_text = make_clump(
                ["public import Pkg.Ext"],
                [
                    ("Pkg.M0", "module\n\npublic import Pkg.Ext\n\n",
                     "@[expose] public section\ndef h : Nat := 1\ntheorem ht : h = 1 := rfl\n"),
                    ("Pkg.C", "module\n\nimport Pkg.M0\n\n",
                     "@[expose] public section\ntheorem ct : True := by have _ := ht; trivial\n"),
                ],
            )
            write_tree(td, {
                "src/Pkg/Ext.lean": "module\n\n@[expose] public section\ndef e : Nat := 0\n",
                "src/Pkg/C.lean": clump_text,
            })
            with contextlib.redirect_stdout(io.StringIO()):
                pi.main(["--root", td, "--apply", "--exclude", ""])
            after1 = (Path(td) / "src/Pkg/C.lean").read_text(encoding="utf-8")
            self.assertIn("\nimport Pkg.Ext\n", after1)
            self.assertIn("\nsection\ndef h : Nat := 1", after1)
            self.assertIn("\npublic section\ntheorem ct", after1)

            buf2 = io.StringIO()
            with contextlib.redirect_stdout(buf2):
                pi.main(["--root", td, "--apply", "--exclude", ""])
            self.assertIn("Wrote 0 transformed files", buf2.getvalue())
            self.assertEqual((Path(td) / "src/Pkg/C.lean").read_text(encoding="utf-8"), after1)

    def test_invalid_rules_and_mutual_exclusion(self):
        with self.assertRaises(SystemExit):
            with contextlib.redirect_stderr(io.StringIO()):
                pi.main(["--rules", "xyz"])
        with self.assertRaises(SystemExit):
            with contextlib.redirect_stderr(io.StringIO()):
                pi.main(["--apply", "--out-dir", "/tmp/nope"])
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/Leaf.lean": "module\n\n@[expose] public section\ntheorem leaf : True := trivial\n",
            })
            before = (Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8")
            for flags in (["--dry-run", "--apply"], ["--dry-run", "--out-dir", td]):
                with self.assertRaises(SystemExit):
                    with contextlib.redirect_stderr(io.StringIO()):
                        pi.main(["--root", td, "--exclude", ""] + flags)
            self.assertEqual((Path(td) / "src/Pkg/Leaf.lean").read_text(encoding="utf-8"), before)

    def test_frozen_challenge_files_and_select_scope_normpath(self):
        expected_frozen = {
            "src/Challenge.lean",
            "comparator.json",
            "export-targets.txt",
            "comparator/FormalConjecturesChallenge.lean",
            "comparator/formal-conjectures.json",
            "comparator/formal-conjectures-export-targets.txt",
        }
        self.assertEqual(pi.FROZEN_CHALLENGE_FILES, expected_frozen)
        self.assertTrue(expected_frozen <= pi.PROTECTED_PATHS)
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/A.lean": "module\n\npublic section\ntheorem a : True := trivial\n",
                "src/Pkg/B.lean": "module\n\npublic section\ntheorem b : True := trivial\n",
            })
            plan = pi.build_plan(td, rules="c", mode="strict", exclude=frozenset())
            sel = pi.select_scope(plan, None, ["./src/Pkg/A.lean"])
            self.assertEqual(sel, [plan["mod_idx"]["Pkg.A"]])
            sel_dir = pi.select_scope(plan, ["./src/Pkg"], None)
            self.assertEqual(sel_dir, [plan["mod_idx"]["Pkg.A"], plan["mod_idx"]["Pkg.B"]])

    def test_empty_repo_stats_no_crash(self):
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "src").mkdir()
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                pi.main(["--root", td, "--dry-run", "--stats", "--exclude", ""])
            self.assertIn("Repo modules: 0", buf.getvalue())

    def test_dir_and_files_scoping_preserves_repo_wide_safety(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/DirA/Pure.lean": "module\n\n@[expose] public section\ntheorem p_thm : True := trivial\n",
                "src/DirA/Mid.lean": (
                    "module\n\npublic import DirA.Pure\n\n@[expose] public section\n"
                    "theorem m_thm : True := by exact p_thm\n"
                ),
                # External directory DirB uses p_thm transitively through DirA.Mid!
                "src/DirB/Consumer.lean": (
                    "module\n\nimport DirA.Mid\n\n@[expose] public section\n"
                    "theorem c_thm : True := by exact p_thm\n"
                ),
            })
            # Scoping --dir src/DirA must still see DirB.Consumer and block demoting (Mid, Pure),
            # while ONLY writing files inside src/DirA (not DirB/Consumer)!
            with contextlib.redirect_stdout(io.StringIO()):
                pi.main(["--root", td, "--dir", "src/DirA", "--apply", "--exclude", ""])
            mid_txt = (Path(td) / "src/DirA/Mid.lean").read_text(encoding="utf-8")
            cons_txt = (Path(td) / "src/DirB/Consumer.lean").read_text(encoding="utf-8")
            self.assertIn("public import DirA.Pure", mid_txt)
            self.assertIn("@[expose] public section", cons_txt)
            # DirA/Pure got Rule C hygiene because it is inside --dir src/DirA
            pure_txt = (Path(td) / "src/DirA/Pure.lean").read_text(encoding="utf-8")
            self.assertNotIn("@[expose]", pure_txt)

    def test_rule_c_skips_def_bearing_files(self):
        with tempfile.TemporaryDirectory() as td:
            write_tree(td, {
                "src/Pkg/DefFile.lean": "module\n\n@[expose] public section\ndef f (n : Nat) : Nat := n\n",
                "src/Pkg/ThmFile.lean": "module\n\n@[expose] public section\ntheorem t : True := trivial\n",
            })
            plan = pi.build_plan(td, rules="c", mode="strict", exclude=frozenset())
            self.assertNotIn(plan["mod_idx"]["Pkg.DefFile"], plan["rule_c_files"])
            self.assertIn(plan["mod_idx"]["Pkg.ThmFile"], plan["rule_c_files"])

    def test_clump_section_end_balance_preserved(self):
        with tempfile.TemporaryDirectory() as td:
            body_m0 = "@[expose] public section Helper\ndef x : Nat := 1\ntheorem hx : x = 1 := rfl\nend Helper\n"
            body_root = "@[expose] public section\ntheorem root : True := by have _ := hx; trivial\n"
            clump_text = make_clump(
                [],
                [
                    ("Pkg.M0", "module\n\n", body_m0),
                    ("Pkg.Root", "module\n\nimport Pkg.M0\n\n", body_root),
                ],
            )
            write_tree(td, {"src/Pkg/Root.lean": clump_text})
            plan = pi.build_plan(td, rules="bc", mode="strict", exclude=frozenset())
            u = plan["mod_idx"]["Pkg.Root"]
            new_txt, changed, _ = pi.transform_file_text(u, clump_text, plan)
            self.assertTrue(changed)
            self.assertIn("\nsection Helper\n", new_txt)
            self.assertEqual(clump.open_scopes(clump_text), clump.open_scopes(new_txt))


if __name__ == "__main__":
    unittest.main()
