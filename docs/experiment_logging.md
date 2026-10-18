# Single / Dual 실험 로그와 분석

현재 `two_goal` 실행 경로는 실행 스크립트나 LangSmith 설정에 관계없이 로컬 감사 로그를 자동 저장한다. `v19-lean-strategy-only`에서는 Orchestrator가 `task`와 `lean_strategy`만 출력하고, Natural Agent는 문제와 선택된 골에서 독립적으로 자연어 증명을 만든다. Lean Generator에 두 결과를 함께 전달한다. Natural 입력에는 전략이나 이전 시도 메모리가 없다. Lean 재시도·Repair·라운드 예산은 유지한다. 별도의 유료 실험을 자동 시작하지 않는다.

## 저장 위치와 내용

각 모드의 출력 디렉터리 아래 `audit/<고유 run ID>/`를 만든다. 같은 폴더에서 다시 실행해도 감사 로그는 덮어쓰지 않는다.

| 파일 | 내용 |
| --- | --- |
| `manifest.json` | 문제 ID·자연어 문제·고정 골, Single/Dual, 메모리 조건, 반복 번호, 라운드·시도 한도, 모델별 라우팅, Python·패키지 버전, Lean 환경 파일과 소스 해시 |
| `events.jsonl` | 시간·일련번호·부모/자식 노드 ID가 있는 즉시 기록. 노드 입력/지시/파싱된 출력/원본 출력, 실제 API 요청·응답, 출력 거부·통신 오류와 재요청, Lean 전체 결과·오류·코드, 완료한 시도와 라운드 |
| `outcome.json` | 최종 Proved/Disproved/Unsolved 결과 또는 실행 오류/취소, 전체 경과 시간. 오류 실행을 Unsolved로 바꾸지 않음 |
| `trace.md` | 노드별 입출력과 오류를 읽는 로컬 보기. 상세 API 원문은 JSONL에 보존 |
| `source_snapshot/` | 핵심 실행 소스, 프롬프트, Lean toolchain·lake manifest 사본 |

CLI는 `invocation.json`에 사용 인수, 선택한 ID, 공개 데이터 파일 해시도 저장한다. 반복 실험 실행기는 `plan.json`, 작업별 `console.log`, `jobs.jsonl`을 추가한다. 실행 중에는 events.jsonl이 계속 저장되고, 정상 종료/예외 시 Markdown과 outcome을 생성한다. 강제 종료 등으로 outcome이 없으면 분석에서 incomplete로 표시한다. 디스크 기록은 flush/fsync하며, 로그 저장 실패도 숨기지 않는다.

API 요청의 모델·옵션·메시지와 응답의 provider·response ID·finish reason·usage·cost를 원형에 가깝게 보존한다. 출력 형식 때문에 거부된 응답도 사용량에 포함한다. API 키와 Authorization 헤더, .env 전체는 저장하지 않는다. 공급자가 사용량·비용을 제공하지 않으면 null로 두며 0으로 추정하지 않는다. Codex 등 사용량을 반환하지 않는 클라이언트도 동일하다. API 요청 옵션에 없는 샘플링 설정은 공급자 기본값이다. job 순서용 seed를 모델의 재현 가능한 sampling seed라고 부르지 않는다.

로그는 실행 전용 저장소다. 로그 ID, 비용, 평가 정답 등의 정보는 모델 프롬프트에 추가하지 않는다. 정답·인증 파일은 사후 분석에서만 읽는다.

## 반복 실행과 메모리 제거 실험

`run_logged_experiment.py`는 먼저 동일 문제 집합의 Single/Dual × 반복 × 메모리 조건 계획을 만든다. 기본 반복 수는 5이며 실행 순서는 고정 seed로 섞는다. 각 실행은 새 프로세스와 별도 verifier 파일을 사용한다. --run을 주기 전에는 유료 호출을 하지 않는다.

```bash
.venv/bin/python scripts/run_logged_experiment.py \
  --jsonl <공개 evaluator 형식 problems.jsonl> --split <split> \
  --ids <문제ID1> <문제ID2> \
  --project-root .datasets/miniF2F-lean4 \
  --config-env configs/two_goal_experiment.env \
  --repetitions 5 --memory-conditions full none \
  --output-dir .runs/<새 실험명>
```

실행하려면 새 출력 경로와 `--run`을 사용한다. config의 모델·제공자 선택을 따른다. 정답 필드가 들어 있는 JSONL은 실행기가 거부한다. 자연어·형식 골의 데이터 적합성은 기존 데이터셋 검수 절차를 따른다. 이 도구는 ground_truth 원본 JSONL을 evaluator 형식으로 변환하는 도구가 아니다.

- `full`: 다음 라운드 Orchestrator에 기존 compact 메모리 제공.
- `none`: Orchestrator에 이전 라운드 메모리를 주지 않음. 같은 라운드 안의 Lean→Repair→Lean 피드백은 유지.
- 직접 CLI 호출에서도 `DUAL_ARC_MEMORY_CONDITION=full|none`, `DUAL_ARC_EXPERIMENT_ID`, `DUAL_ARC_REPETITION`으로 조건을 기록할 수 있다.
- Single은 라운드마다 방향을 선택하고, Dual은 두 경로를 수행한다. 같은 라운드 한도는 같은 계산 예산을 뜻하지 않는다. 비용을 맞춘 추가 비교는 별도 설계해야 한다.

## 사후 분석

```bash
.venv/bin/python scripts/analyze_logged_experiment.py .runs/<실험명> \
  --labels new_data/prove_or_disprove/ground_truth_v1/labels.jsonl \
  --metadata new_data/prove_or_disprove/ground_truth_v1/problems.jsonl
```

`analysis/runs.jsonl`, `runs.csv`, `summary.json`, `README.md`를 만든다.

- 정답률, Prove/Disprove별 precision·recall·F1, 두 정답 × 세 출력의 confusion matrix, coverage. Unsolved는 판단 보류이며 False로 간주하지 않는다. recall에서 해당 클래스의 Unsolved는 놓친 정답으로 센다. precision 분모가 없으면 null이다.
- 완료 실행과 호출/형식/환경 오류·불완전 실행을 별도로 집계한다. 오류를 제외한 성능만 제시하지 말고 전체 실행 수와 오류 수도 같이 보고한다.
- 라운드·Lean 시도·빌드 수, 해결한 문제의 평균 라운드, 전체 경과 시간, 요청 수, 통신 오류·출력 거부 수, 토큰·비용과 정답 1개당 비용. 비용 총계의 reported_runs를 반드시 확인한다.
- 반복별 정답률과 표준편차. 충분한 반복이 있는 문제만 전체 파이프라인 Pass@1/5/10을 계산한다. 라운드별 3회 Lean 시도는 독립 반복이 아니다. Pass@k와 함께 eligible_problems를 보고한다.
- 동일 문제·동일 반복의 Single/Dual을 대응시킨 McNemar exact 양측 p값. 반복별로 계산하여 같은 문제의 반복을 독립 문제처럼 합치지 않는다.
- 문제 단위 cluster bootstrap 95% CI와 Dual−Single 정답률 차이. 반복 기록을 문제 안에 묶은 채 문제를 재표집한다. seed=42, 5,000회 percentile bootstrap이며 작은 표본에서는 탐색적 결과로 해석한다.
- 메모리 full−none의 문제 단위 대응 차이와 CI, 교재별 결과.
- 라운드별 실제 전략·Lean 전략과 전달된 메모리 그룹 수, 전략 원문의 정확한 반복 횟수. 단어가 바뀌었다는 것만으로 의미 있는 전략 개선이라고 판정하지 않는다.

같은 experiment/condition/problem/repetition/mode가 두 번 있으면 분석은 중단한다. 재실행 결과 중 좋은 것만 선택해 집계하지 않도록 새 experiment ID로 보관해야 한다. 주된 비교·예산·반복 횟수는 전체 실험 전에 고정한다. 메모리 ablation도 동일 문제·모델·시도 예산을 사용한다.

현재 교재 데이터에는 기존 인공 변형의 ‘오류 유형’ 라벨이 없다. 교재/분야별 분석과 Prove/Disprove별 분석은 가능하지만, 이를 양화사·정의역 등의 오류 유형별 성능이라고 부르면 안 된다. 그런 분석에는 독립적인 유형 주석이 추가로 필요하다.

## 검증

```bash
PYTHONPATH=src .venv/bin/python scripts/check_local_audit.py
PYTHONPATH=src .venv/bin/python scripts/check_parallel_goal_search.py
PYTHONPATH=src .venv/bin/python scripts/check_execution_contracts.py
```

로그 테스트는 유료 호출 없이 병렬 저장, 노드 연결, raw 출력, 형식 재요청과 비용, fatal 오류, 메모리 제거, 민감정보 제외, 통계 경계값을 확인한다. 이는 모델의 수학적 능력이나 실제 공급자의 안정성을 검증하는 실험과 구분한다.

통계 정의 참고: [McNemar 공식 문서](https://www.statsmodels.org/dev/generated/statsmodels.stats.contingency_tables.mcnemar.html), [분류 지표 공식 문서](https://scikit-learn.org/stable/modules/generated/sklearn.metrics.classification_report.html), [Pass@k 원 논문](https://arxiv.org/abs/2107.03374).

## 다음 실험의 모델 설정

`configs/two_goal_experiment.env` 기준으로 Single·Dual 모두 Orchestrator는 `openai/gpt-6-luna-pro`, Natural·Lean Generator·Repair는 `openai/gpt-6-luna`를 사용한다. 모든 요청은 `provider.only=["openai/flex"]`, `allow_fallbacks=false`, `require_parameters=true`로 Flex 경로를 고정한다. Worker의 reasoning effort는 `none`이며, Pro planner는 모델 별칭의 기본 Pro 동작을 유지한다.

`DUAL_ARC_MODEL_REASONING_EFFORTS`는 모델별 effort를, `DUAL_ARC_REASONING_EFFORT`는 선택적 공통 기본값을 지정한다. 실행기는 두 설정을 하위 프로세스에 전달하며, 실제 요청 옵션은 로컬 감사 로그에 저장한다. 기존 개별 `.runs/*/run.py`의 하드코딩된 모델 설정은 과거 실행의 재현 자료이며 자동으로 바꾸지 않는다.

공개 모델·엔드포인트 목록과 오프라인 요청 검사를 확인했다. 실제 유료 호출과 전체 실험은 아직 수행하지 않았다. 오프라인 검사는 `scripts/check_flex_model_setup.py`로 실행할 수 있다.

설정 근거: [OpenRouter Luna Pro](https://openrouter.ai/openai/gpt-6-luna-pro), [제공자 경로 지정](https://openrouter.ai/docs/guides/routing/provider-selection), [OpenAI Luna reasoning 옵션](https://developers.openai.com/api/docs/models/gpt-6-luna).


## Repair 출력과 Lean 검사 수정 (2026-10-16)

현재 버전은 `v20-bounded-repair`이다. Orchestrator의 Lean 전략 전담과 Natural Agent의 독립 증명 입력은 유지한다. 정상 Lean 전술인 `by assumption`과 `by exact False.elim ...`의 정규식 일괄 차단을 제거했다. 고정 목표·추가 선언·placeholder 검사, 실제 Lean 검증과 선언별 공리 의존성 검사는 유지한다.

Repair 출력은 기본 2,048토큰, 수정 지침 4,000자, 오류 요약 800자로 제한한다. 전체 노드 출력은 기본 16,384토큰 이내이다. Repair 요청에는 180초 HTTP 타임아웃을 적용한다. 길이 제한에 걸린 응답은 최대 3회의 출력 복구 예산 안에서 짧고 완전한 JSON으로 재생성하며, 잘린 긴 응답을 다음 프롬프트에 다시 넣지 않는다. 모두 실패하면 여전히 실행 오류로 기록하고 임의 수정 지침이나 정답으로 대체하지 않는다. 네트워크 복구 예산은 별도로 유지한다.

한 Dual 경로가 이미 Lean 검증에 성공했다면, 다른 경로에서 나중에 반환된 응답 오류는 중단으로 처리하여 검증된 결과를 버리지 않는다. 회귀 검사는 `scripts/check_bounded_repair.py`와 `scripts/check_parallel_goal_search.py`에서 확인한다.

## Shared Lean environment support (2026-10-16)

The new ten-problem baseline is frozen at `.runs/equal_prompt_unseen10_20261016/` (20 model-backed system executions). Its prompts, settings and source snapshot remain the evidence for those original results. Never replace them with development retest results.

`DUAL_ARC_LEAN_DECLARATIONS=1` in `configs/two_goal_experiment.env` enables common compiler-grounded API context. `lean_declarations.py` chooses a small declaration catalogue by the supplied goal's types, with no architecture condition and no use of labels or benchmark proofs. Planner, Lean Generator and Repair receive the same declarations for the same goal family; Natural receives neither the declarations nor an Orchestrator strategy. The current catalogue covers basis/submodule APIs and linear-map injectivity/surjectivity. It is not a general Mathlib search service.

Declarations come from actual `#check` commands under the verifier's prelude. Unresolved import-scope names are distinguished from available declarations; in particular, a missing unqualified name does not establish that the mathematical API is absent. Lean's `error(lean.unknownIdentifier):` diagnostic is recognized as an error, not a signature. The cache key includes prelude, symbols, schema, Lean toolchain, Lake manifest and Mathlib import artifact metadata. Cache creation is protected across threads/processes, and its Lean subprocess uses the project-wide verification lock. Context is present in the actual logged model inputs and the helper source is included in each audit snapshot.

The shared bare-omega guard now anchors to the end of a declaration (including the appended axiom query), rather than MULTILINE line endings. This permits local arithmetic `have ... := by omega` inside a longer nonlinear proof while retaining the existing whole-bare-proof resource guard. Actual Lean verification, fixed-target auditing and declaration-specific axiom checks remain required.

The common instruction templates and existing direction-assignment instructions are byte-for-byte unchanged. Models/effort, per-lane 3×3 budget, memory, output schemas, output caps and Repair timeout are unchanged. Input library facts are additional common system support and must be reported as such; they are not an architecture-only effect.

Validation: `scripts/check_shared_lean_support.py` uses real Lean for current signatures and valid/invalid proof checks, and verifies identical context for Single and both Dual goals with independent Natural inputs. Execution-contract, parallel-search and durable-audit checks also passed. Separate paired development retests are in `.runs/shared_backend_support_20261016/`; these selected cases do not replace the original ten-problem evaluation or constitute a held-out accuracy estimate.

## Source-grounded Repair context (2026-10-17)

`DUAL_ARC_REPAIR_CONTEXT=1` adds the same diagnostic support to Single and both Dual lanes. Common instructions in `goal_prompts.py`, model routes/effort, output contracts and per-lane 3×3 attempt budgets are unchanged. Set the flag to `0` to reproduce the control condition.

`repair_context.py` extracts at most six compiler errors and maps their file/line/column to seven-line windows of the actual compiled `formal_state`, including its prelude and theorem header. File mismatches and out-of-range locations receive no source window. Lean information/warning messages and Lake failure trailers are excluded. Raw compiler logs remain available; truncated diagnostic/window text and omitted diagnostic counts are bounded.

After the first failed attempt of a round, context also contains the actual tactic-body diff from the preceding attempt, the preceding Repair guidance and normalized exact-diagnostic repetition flags. These describe the current lane's consecutive attempts, not sibling or future attempts. A source window without a reported error is never treated as a verified subproof. The feature does not certify or automatically transplant partial proofs.

Repair receives this data after a failed verification. The next Generator receives the same data with the previous proof and Repair guidance. Natural remains independent; no additional model node, automatic retry, proof-verification attempt or budget transfer is introduced. Source snapshots and generation settings record the helper and feature flag.

`scripts/check_repair_context.py` checks source mapping against historical real Lean output, error severity filtering, bounded excerpts/diffs, repeated-error flags, Natural independence, equal Single/Dual support and the disabled condition. Execution-contract, parallel-search and audit checks also pass.

The controlled development rerun is `.runs/repair_context_ablation_20261017_v2/`: the same previously inspected ten cases, Single/Dual with support off/on (40 system executions), with actual library declarations enabled in every cell. One stochastic run per cell cannot establish general architectural superiority or an individual change's causal effect. Concurrent runs share the Lean build lock, so elapsed times include contention. Original ten-problem results remain unchanged. The initial `.runs/repair_context_ablation_20261017/` pilot was stopped and marked unscorable after a diagnostic-severity parsing bug was found; its logs are preserved and excluded from the controlled comparison.

### Common strategy-aware Repair: five-case development retest (2026-10-17)

Both Single and Dual now pass the active lane/round `lean_strategy` to Repair, matching the strategy supplied to Generator. The common Repair instruction prioritizes the fixed theorem and actual Lean diagnostics; both strategy and Natural argument remain tentative. Repair may retain a valid construction when the Natural argument is wrong, without rewriting the Natural input or changing the theorem. Natural receives no strategy. No cross-round candidate carryover was added.

Output contracts remain `v20-bounded-repair` (the API routing uses this version to preserve strict schemas and bounded outputs); source hashes, rendered instructions, and the `repair-strategy-five-20261017` experiment ID identify the updated input/instructions. `scripts/check_repair_context.py` checks common instructions and matching Generator/Repair strategy in both modes.

The five selected cases were previously inspected development cases, chosen for observed Repair conflicts/failures, not an unseen final evaluation. Historical comparison uses the matching five cases from `.runs/repair_context_ablation_20261017_v2/on`; stochastic regeneration prevents isolated causal attribution. Runs and protocol are in `.runs/repair_strategy_five_20261017/`. Models, common source/error context, and 3 rounds × 3 attempts per lane are unchanged.

### Guidance-only Repair (2026-10-17)

The active `two_goal` Single/Dual engine uses `v21-guidance-only-repair`: Repair returns only `retry_guidance` (maximum 4000 characters). It still reads the Orchestrator Lean strategy, tentative Natural argument, current code, and actual compiler diagnostics. The runtime rejects extra fields, including `lean_error_summary`. The shared planner memory omits error summaries even from imported historical records, as well as raw compiler logs and Repair guidance; prior strategies, independent Natural arguments and Lean code remain. Full compiler evidence stays in audit logs and the Generator/Repair retry path. No separate summarizer was introduced. Historical API contracts remain readable; current safeguards, output caps, timeout and recovery apply to v21.

The prior strategy-aware five-case retest was interrupted on user steering after three complete pairs; its partial results are preserved under `.runs/repair_strategy_five_20261017/` and are not merged into subsequent scores. Two active LangSmith roots were explicitly closed as interrupted. The fresh ten-case retest is `.runs/guidance_only_ten_20261017/`; it reuses all ten previously inspected development cases with identical current source/models/per-lane budgets for both structures, two pairs concurrently, and serialized Lean builds. Historical comparisons cannot isolate generation randomness or wall-time effects.
