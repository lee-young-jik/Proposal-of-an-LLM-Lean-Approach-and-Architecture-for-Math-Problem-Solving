# 121문제 정답 및 Lean 인증 코드

전체 121문제의 확정 정답: **Proved 42개, Disproved 79개**.

- [labels.jsonl](labels.jsonl): 문제 ID, 참·거짓 정답, 설명, 전체 Lean 증명·반증 코드와 인증 해시.
- [pairs.jsonl](pairs.jsonl): 문제 입력, Prove/Disprove 골, 정답과 인증 코드를 한 레코드로 합친 파일.
- [certificates/](certificates/): 문제별 독립 Lean 인증 코드 121개.
- [Certificates.lean](Certificates.lean): 전체 인증 코드를 모은 Lean 모듈.
- [audit.json](audit.json), [certificate_audit.log](certificate_audit.log): 기존 전체 재컴파일 결과, 버전, 파일 해시 및 공리 검사 기록.
- [annotation_status.jsonl](annotation_status.jsonl): 문제별 정답 확정 현황.
- [manifest.json](manifest.json), [input_cleaning.json](input_cleaning.json): 원본 인증 데이터셋의 메타데이터 및 입력 정리 기록.

상위 [problems.jsonl](../problems.jsonl) 및 [labels.jsonl](../labels.jsonl)과 같은 121개 문제 ID와 정답을 사용합니다. 이 폴더의 정답·설명·인증 코드는 평가 모델의 입력으로 전달하지 마세요.

기존 인증 환경은 Lean 4.27.0, Mathlib 커밋 `a3a10db0e9d66acbebf76c5e6a135066525ac900`입니다. 해당 환경에서 `lake env lean /absolute/path/to/Certificates.lean`으로 전체 인증 모듈을 다시 검사할 수 있습니다. 기존 감사는 전체 121개 인증 코드의 컴파일 성공과 표준 공리 `propext`, `Classical.choice`, `Quot.sound`만의 사용을 확인했습니다. 이번 게시는 원본 인증 파일을 그대로 복사하고 문제 ID·정답·인증 코드 해시를 대조한 것으로, 새 Lean 실행이나 모델 호출을 수행한 것은 아닙니다.

원문 번역의 의미 검토와 Lean 커널 검증은 별개입니다. 정답 설명은 참고용이며 형식 목표에 대한 최종 근거는 인증 코드입니다.
