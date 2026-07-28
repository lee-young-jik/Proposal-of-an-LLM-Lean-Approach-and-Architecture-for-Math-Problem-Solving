from __future__ import annotations

import unittest

from single_orchestrator.proof_audit import audit_lean_proof


class ProofAuditTests(unittest.TestCase):
    def test_accepts_exact_multiline_target(self) -> None:
        formal = """theorem sample (n : ℕ)
    (h : n = 1) : n = 1 := by"""
        source = f"""import Mathlib

{formal}
  exact h
"""
        result = audit_lean_proof(source, formal)
        self.assertTrue(result.success, result.rationale)

    def test_rejects_statement_mutation(self) -> None:
        formal = "theorem sample : 1 = 1 := by"
        source = """import Mathlib

theorem sample : True := by
  trivial
"""
        result = audit_lean_proof(source, formal)
        self.assertFalse(result.success)
        self.assertIn("differs", result.rationale)

    def test_rejects_extra_top_level_declaration(self) -> None:
        formal = "theorem sample : True := by"
        source = """import Mathlib

def helper : True := trivial

theorem sample : True := by
  exact helper
"""
        result = audit_lean_proof(source, formal)
        self.assertFalse(result.success)
        self.assertIn("extra top-level", result.rationale)

    def test_rejects_placeholder_escape(self) -> None:
        formal = "theorem sample : True := by"
        source = f"""{formal}
  sorry
"""
        result = audit_lean_proof(source, formal)
        self.assertFalse(result.success)
        self.assertIn("prohibited", result.rationale)


if __name__ == "__main__":
    unittest.main()
