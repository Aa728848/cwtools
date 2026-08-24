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

```sh
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

## 中文

本仓库包含 CWTools VS Code 与其他宿主共用的 Rust 语义核心，包括 Paradox/CWT 解析、规则、作用域、workspace、增量快照、缓存、全部游戏 Profile、本地化、Shader 以及语义图/项目知识。

修改后运行 rustfmt、workspace 全测试和严格 clippy。根仓库通过 submodule 指针引用本仓库；请先在本仓库提交，再更新根指针。
