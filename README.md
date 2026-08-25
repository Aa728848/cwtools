# CWTools Rust Core

This repository contains the Rust semantic core used by CWTools VS Code and other hosts.

## Crates

- syntax/domain/process: Paradox CST and editable domain
- cwt/rule-ir/rules-engine: CWT schema, compilation, completion, and validation
- scopes/docs/metadata: game scope and documentation catalogs
- workspace: deterministic resources, indexes, diagnostics, and incremental snapshots
- cache: bounded versioned cache envelopes
- game-core: all supported game profiles and localisation
- shader: Shader syntax, preprocessing, HLSL, include and runtime models
- semantic: graph, flow, and SQLite project knowledge

## Verify

Run the Rust workspace gates from this directory:

```sh
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

The cache crate uses bounded, versioned envelopes with source and rules fingerprints. A schema or fingerprint mismatch is a safe cache miss: discard the stale entry and rebuild the affected snapshot; never treat stale data as current. Incremental workspace changes must be compared with a clean full rebuild, including additions, edits, removals, renames, and overlay transitions.

This repository is the Rust core submodule. Commit core changes here first, then update the parent repository's submodule pointer.

## 中文

本仓库包含 CWTools VS Code 与其他宿主共用的 Rust 语义核心，包括 Paradox/CWT 解析、规则、作用域、workspace、增量快照、缓存、全部游戏 Profile、本地化、Shader 以及语义图/项目知识。

修改后运行 rustfmt、workspace 全测试和严格 clippy。缓存 schema 或 source/rules 指纹不匹配时必须安全失效并重建受影响快照，不能继续使用旧数据。增量 workspace 修改必须与干净全量构建对比，并覆盖新增、编辑、删除、重命名和 overlay 切换。根仓库通过 submodule 指针引用本仓库；请先在本仓库提交，再更新根指针。
