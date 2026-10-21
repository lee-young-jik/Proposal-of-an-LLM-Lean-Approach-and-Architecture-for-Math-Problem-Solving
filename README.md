# Single & Dual · LLM–Lean

### Prove or Disprove: two search architectures, one Lean verification criterion

수학 명제의 성립 여부가 주어지지 않은 문제에서, 하나의 목표를 선택하는
**Single**과 두 목표를 동시에 탐색하는 **Dual**을 비교합니다.
현재 공개 버전은 **최종 분석 대상 137문제**를 기준으로 구성되어 있습니다.

[데이터셋](data/book137_posthoc_v1/README.md) ·
[실제 프롬프트](src/single_orchestrator/goal_prompts.py) ·
[실행 방법](docs/CURRENT_SETUP.md) ·
[실험 조건](REPRODUCIBILITY.md) ·
[결과](results/book137_pass5/README.md)

## 구조

<p align="center"><img src="docs/fig1_architecture_final.png" alt="Single and Dual architecture with Lean verification and memory" width="100%"></p>

| | Single | Dual |
|---|---|---|
| 목표 | 매 라운드 Prove 또는 Disprove 선택 | Prove와 Disprove를 병렬 탐색 |
| 전략 | 선택한 목표에 대한 전략 수립 | 각 목표에 대한 전략 수립 |
| 다음 라운드 | 자신의 이전 탐색 기록 활용 | 양쪽 경로의 이전 탐색 기록 활용 |
| 최종 판정 | Lean 검증으로 Proved / Disproved / Unsolved | 동일 |

Natural Agent가 자연어 풀이를 작성하고, Lean Generator가 전략과 풀이를
Lean 코드로 옮깁니다. 검증 실패 시 Repair Agent가 수정 지침을 제공합니다.
구체적인 입출력과 메모리 범위는 [구조 설명](docs/FINAL_PIPELINE.md)을 참고하세요.

## 데이터 · 137문제

| 교재 | Prove | Disprove | 합계 |
|---|---:|---:|---:|
| Book of Proof | 24 | 31 | 55 |
| Basic Analysis I | 2 | 11 | 13 |
| Linear Algebra Done Right | 6 | 20 | 26 |
| Exercises and Problems in Calculus | 8 | 13 | 21 |
| Abstract Algebra: Theory and Applications | 22 | 0 | 22 |
| **합계** | **62** | **75** | **137** |

- [모델 입력](data/book137_posthoc_v1/problems.jsonl): 문제, Lean 목표, 정의 및 import.
- [평가 정답](data/book137_posthoc_v1/labels.jsonl) / [참조 코드](data/book137_posthoc_v1/reference_answers.jsonl): 평가 전용. 모델 입력에 포함하지 않습니다.
- [ID·선정 기록](data/book137_posthoc_v1/selection.json) / [파일 해시](data/book137_posthoc_v1/manifest.json).

**분석 범위:** 결과를 확인한 뒤 선정한 부분집합이며, 두 문제에는 재실험 결과를
반영했습니다. 독립적으로 고정한 평가셋이 아닙니다. 선정·교체 기준은
[데이터 설명](data/book137_posthoc_v1/README.md)에 기록했습니다.
이전 데이터와 실험은 Git 이력에 남아 있습니다.

## Pass@5 결과

| 구조 | Proved | Disproved | Unsolved | 해결 합계 |
|---|---:|---:|---:|---:|
| Single | 50 | 56 | 31 | 106/137 |
| Dual | 52 | 57 | 28 | 109/137 |

각 구조의 성공 문제에서 정답 코드 대비 평균 길이 배수는 Single **3.18배**,
Dual **2.96배**였습니다. 해결 여부의 탐색적 McNemar 검정은 **p=0.25**입니다.
공통 성공 106문제의 평균 배수는 3.18/3.00이며, 차이의 95% 부트스트랩
신뢰구간은 −0.531~0.154입니다. 이 결과는 통계적 우위나 일반화 성능을
입증하지 않습니다. [수치 자료와 집계 기준](results/book137_pass5/README.md)을 제공합니다.

## 시작하기

Python 3.11 이상, Git, Elan/Lean을 사용합니다.

```bash
git clone https://github.com/lee-young-jik/Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving.git
cd Proposal-of-an-LLM-Lean-Approach-and-Architecture-for-Math-Problem-Solving
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements-tested.txt
python -m pip install -e .
python scripts/validate_release.py
```

위 검증은 모델을 호출하지 않습니다. Lean 환경 설치, API 설정, 계획 생성과
실행 방법은 [설치·실행 안내](docs/CURRENT_SETUP.md)에 있습니다.
실제 모델 실행은 유료 API를 사용하며 `--run`을 명시해야 합니다.

## 코드와 프롬프트

| 자료 | 위치 |
|---|---|
| 에이전트별 프롬프트 | [goal_prompts.py](src/single_orchestrator/goal_prompts.py) |
| Single/Dual 탐색 흐름 | [goal_search.py](src/single_orchestrator/goal_search.py) |
| 메모리 처리 | [planner_memory.py](src/single_orchestrator/planner_memory.py) |
| 모델·예산·제공자 설정 | [two_goal_experiment.env](configs/two_goal_experiment.env) |
| 반복 실행 | [run_logged_experiment.py](scripts/run_logged_experiment.py) |
| 새 실행의 사후 분석 | [analyze_logged_experiment.py](scripts/analyze_logged_experiment.py) |

```text
data/book137_posthoc_v1/  공개 입력 · 평가 정답 · 참조 코드
results/book137_pass5/    137문제의 최종 수치 결과
src/                     에이전트와 Lean 검증 구현
configs/                 실행 설정
scripts/                 실행 · 검증 · 분석 도구
docs/                    설치 방법과 구조 설명
```
