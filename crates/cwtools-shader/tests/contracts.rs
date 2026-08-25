use cwtools_shader::{
    hlsl::{self, HlslSymbolKind},
    preprocessor::{self, ConditionValue},
    project::{self, ShaderOrigin},
    runtime::{self, EffectReachability},
    syntax::{self, ShaderNodeKind},
};

#[test]
fn lossless_frontend_recovers_declarations_and_direct_includes() {
    let tree = syntax::parse(
        "gfx/FX/test.shader",
        r#"UnknownDialect Foo = { nested = { value = 1 } }
Includes = { "common.fxh" nested = { "not-direct.fxh" } }
Effect First { PixelShader = "Pixel" }
VertexShader = { MainCode Vertex [[ float4 main( { return 0; } ]] }
Effect Last { VertexShader = "Vertex" }
"#,
    );

    assert!(tree.is_lossless());
    assert_eq!(
        syntax::nodes_of_kind(&tree, ShaderNodeKind::IncludeFile)
            .iter()
            .filter_map(|node| node.name.as_deref())
            .collect::<Vec<_>>(),
        vec!["common.fxh"]
    );
    assert_eq!(
        syntax::nodes_of_kind(&tree, ShaderNodeKind::Effect)
            .iter()
            .filter_map(|node| node.name.as_deref())
            .collect::<Vec<_>>(),
        vec!["First", "Last"]
    );
}

#[test]
fn variants_macros_and_hlsl_symbols_are_preserved() {
    let (tree, preprocessor, analysis) = hlsl::analyze_text(
        "gfx/FX/shared.fxh",
        r"#if defined(PDX_OPENGL) && !defined(PDX_DIRECTX_11)
#define PLATFORM_VALUE 4
#endif
struct Light { float3 Color; };
float Shade(float x) { return x; }
float Shade(float3 x) { return x.x; }
",
    );

    assert!(tree.is_lossless());
    let opengl = preprocessor::default_platform_variants()
        .into_iter()
        .find(|variant| variant.name == "opengl")
        .expect("OpenGL platform variant");
    assert_eq!(
        preprocessor::evaluate(
            &opengl.environment,
            &preprocessor::parse_condition("defined(PDX_OPENGL)"),
        ),
        ConditionValue::ConditionTrue
    );
    assert!(
        preprocessor
            .macros
            .iter()
            .any(|item| item.name == "PLATFORM_VALUE")
    );
    assert!(
        analysis
            .symbols
            .iter()
            .any(|symbol| symbol.kind == HlslSymbolKind::StructSymbol && symbol.name == "Light")
    );
    assert_eq!(
        analysis
            .symbols
            .iter()
            .filter(|symbol| symbol.kind == HlslSymbolKind::FunctionSymbol && symbol.name == "Shade")
            .count(),
        2
    );
}

#[test]
fn compile_units_and_explicit_runtime_callers_are_deterministic() {
    let root = project::create_snapshot(
        ShaderOrigin::Workspace,
        "C:/mod/gfx/FX/main.shader",
        "gfx/FX/main.shader",
        r#"Includes = { "shared.fxh" }
Effect Example { }
"#,
    );
    let include = project::create_snapshot(
        ShaderOrigin::Workspace,
        "C:/mod/gfx/FX/shared.fxh",
        "gfx/FX/shared.fxh",
        "float4 SharedValue;",
    );

    let unit = project::build_compile_unit(&[root.clone(), include], &root);
    assert_eq!(unit.members.len(), 2);
    assert!(unit.problems.is_empty());

    let callers = [runtime::create_script_source(
        "C:/mod/interface/example.gfx",
        "interface/example.gfx",
        "mod",
        r#"spriteType = { shader = "Example" }"#,
    )];
    let model = runtime::build_model(None, &callers, vec![root]);
    let effect = runtime::effect_reachability(&model, "Example").expect("declared effect");
    assert!(matches!(
        effect.reachability,
        EffectReachability::DataExplicit { .. }
    ));
    assert_eq!(runtime::callers_of(&model, "Example").len(), 1);
}
