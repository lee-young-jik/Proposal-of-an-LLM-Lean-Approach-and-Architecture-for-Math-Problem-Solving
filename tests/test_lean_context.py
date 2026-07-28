from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from single_orchestrator.lean_context import available_modules, retrieve_lean_context


class LeanContextTest(unittest.TestCase):
    def test_retrieves_only_existing_import_candidates(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            (root / "MiniF2F").mkdir()
            (root / "MiniF2F" / "ProblemImports.lean").write_text("", encoding="utf-8")
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic").mkdir(
                parents=True
            )
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic" / "Linarith.lean").write_text(
                "", encoding="utf-8"
            )
            (root / ".lake" / "packages" / "mathlib" / "Mathlib" / "Tactic" / "NormNum.lean").write_text(
                "", encoding="utf-8"
            )
            available_modules.cache_clear()

            context = retrieve_lean_context(
                root,
                formal_statement="theorem target (x : ℝ) : x = x := by",
                informal="Use norm_num only if needed.",
                previous_feedback=(
                    "Generated Lean imports unavailable module "
                    "`Mathlib.Tactic.Nlinarith` in this local Lean/Mathlib environment."
                ),
            )

        self.assertIn("import MiniF2F.ProblemImports", context)
        self.assertIn("import Mathlib.Tactic.Linarith", context)
        self.assertIn("import Mathlib.Tactic.NormNum", context)
        self.assertIn("open scoped Real", context)
        self.assertIn("do not use", context)
        candidates = context.split("Unavailable imports already seen", 1)[0]
        self.assertNotIn("import Mathlib.Tactic.Nlinarith", candidates)
        self.assertIn("import Mathlib.Tactic.Nlinarith", context)


if __name__ == "__main__":
    unittest.main()
