Judson 추상대수 29문제 · Prove / Disprove 골 58개

- goals.jsonl / goals.json: 문제별 두 골, 공통 Lean prelude, 원문 링크, 번역 결정.
- Goals.lean: 전체 골 정의와 29개 부정 동치 증명.
- ModelInputs.lean: 각 실제 모델 골을 개별 Prop로 검사하는 파일.
- problems/*.lean: 문제별 독립 골 파일 29개.
- problems.jsonl: 기존 CLI 형식의 공개 입력. 정리 헤더와 := by를 포함하며 증명 본문은 없음.
- source_review.json: 원문 소문항 범위와 형식화 결정.
- manifest.json / verification.log / model_inputs_verification.log: 검증 결과·버전·해시.

각 Disprove 골은 Prove 골 전체의 정확한 부정이다. 가정, 타입클래스 가정, 존재·전칭 양화사, 복합 결론을 모두 포함해 부정한다. Prove에 이미 부정이 있어도 이를 다시 부정하는 형태를 유지한다.

58개 골 타입 검사, 29개 Disprove ↔ ¬ Prove 동치, JSON에 저장한 실제 모델 입력의 별도 타입 검사를 완료했다. 검증 파일에는 sorry/admit/추가 axiom이 없다. 이 검사는 문제의 참·거짓 정답 증명이 아니다. 이후 29개 전체의 Prove 정답 코드가 별도 ../judson29_gold_v1/에서 Lean 인증과 전체 재컴파일을 통과했다. 기존 121개 원본은 유지하며, 통합한 150문제 입력은 ../book150_v1/에 있다.

표현 결정: 비영 수와 GL₂는 Units, 정수군은 가법군, 정수 원소 위수의 무한대는 orderOf=0, 내부직접곱은 교환 조건과 유일 인수분해로 표현한다. 제시된 구체적 행렬의 위수는 행렬 모노이드에서 표현한다. 소문항만 고른 4.5.33(a), 10.4.13(c,d)는 범위를 명시하고 공통 가정을 보존한다. 4.5.33의 두 위수 2 부분군은 서로 다른 것으로 해석했다. 정확한 번역 결정은 source_review.json을 참조한다. 이는 독립적인 의미 검토를 대신하지 않는다.

informal_prefix는 한국어 문제 요약이다. 정식 목표·모든 가정·구체적 행렬은 Lean 골이 기준이며 원문은 source_url에서 확인한다. 모델 입력에는 Dual 적합성 가설이나 기대 정답을 넣지 않았다.

고정된 Lean 프로젝트에서 공개 파일 검증:
cd .datasets/miniF2F-lean4
lake env lean ../../data/judson29_goals_v1/Goals.lean
lake env lean ../../data/judson29_goals_v1/ModelInputs.lean
lake env lean ../../data/judson29_gold_v1/Certificates.lean

공식 출처: https://judsonbooks.org/aata-files/aata-html/aata-toc.html
