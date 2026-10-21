"""Experimental, lane-local compiler feedback. No labels or stored solutions."""
import re
from .repair_context import diagnostics


def recovery_enabled(mode):
    import os
    return ((mode == 'dual' and os.getenv('DUAL_ARC_STAGNATION_RECOVERY', '0') == '1')
            or (mode in ('single', 'dual') and os.getenv('DUAL_ARC_COMPARISON_RECOVERY', '0') == '1'))


def recovery_feedback(history, task):
    own = [r for r in history if r.get('task') == task]
    if not own:
        return {}
    last_round = max(r.get('strategy_round', 0) for r in own)
    recent = [r for r in own if r.get('strategy_round', 0) == last_round]
    observations, signatures = [], []
    for r in recent:
        vr = r.get('verifier_result') or {}
        messages = [d['message'] for d in diagnostics(r.get('lean_error_log', ''))][:4]
        # Exact normalized headline, rather than a broad type-error category.
        keys = {re.sub(r'\?m\.\d+', '?m', m.splitlines()[0]).strip()
                for m in messages if m.strip()}
        signatures.append(keys if not vr.get('success') else set())
        observations.append({'trial': r.get('trial_index'),
            'verified': bool(vr.get('success')), 'compiler_diagnostics': messages,
            'repair_guidance': r.get('retry_plan', '')[:1800]})
    repeated = sorted(signatures[-1] & signatures[-2]) if len(signatures) >= 2 else []
    return {'task': task, 'previous_round': last_round,
        'previous_strategy': recent[-1].get('lean_strategy', ''),
        'previous_argument': recent[-1].get('informal', ''),
        'attempts': observations, 'repeated_diagnostic_headlines': repeated,
        'change_construction': bool(repeated),
        'caution': 'Diagnostics identify failures only; unreported steps are not certified. A failed proof never proves the opposite goal.'}


PLAN_RECOVERY = """Use construction_feedback as observed compiler evidence for this assigned lane. If change_construction is true, choose a materially different mathematical witness, representation, or proof decomposition that avoids the repeated bottleneck, and specify the concrete change in lean_strategy. Otherwise repair the observed obstruction while preserving useful work. Prefer constructions whose algebra, continuity and type obligations can be stated explicitly in Lean. Keep the assigned goal unchanged; never infer its negation from a compiler failure. No extra proof attempts are available."""

NATURAL_RECOVERY = """Develop the mathematical argument for the supplied lean_strategy, checking its mathematical validity independently. Use construction_feedback to avoid the recorded bottleneck; if change_construction is true, implement the revised construction instead of repeating the old argument. If the strategy is invalid, explain the precise obstruction and develop a valid argument for the same fixed goal. Compiler errors and the strategy are not mathematical premises. Return only the natural-language argument; no Lean code."""

SINGLE_PLAN_RECOVERY = """Use construction_feedback_by_task as observed compiler evidence from your own earlier attempts, separated by direction. Choose task according to the existing Single contract. For the direction you choose, if its feedback says change_construction, choose a materially different witness, representation, or proof decomposition to avoid that bottleneck. Otherwise repair the observed obstruction while preserving useful work. Compiler errors never establish the opposite mathematical claim. Return only task and lean_strategy as before. No extra attempts are available."""
