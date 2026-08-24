use cwtools_docs::{parse_docs_bytes, parse_modifiers_bytes};
use std::env;
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<_> = env::args().collect();
    let (Some(kind), Some(path)) = (args.get(1), args.get(2)) else {
        eprintln!("usage: parse_docs docs|modifiers <path>");
        return ExitCode::from(2);
    };
    let bytes = match fs::read(path) {
        Ok(value) => value,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };
    let result = match kind.as_str() {
        "docs" => parse_docs_bytes(&bytes).map(|value| {
            format!(
                "{{\"triggers\":{},\"effects\":{}}}",
                value.triggers.len(),
                value.effects.len()
            )
        }),
        "modifiers" => {
            parse_modifiers_bytes(&bytes).map(|value| format!("{{\"modifiers\":{}}}", value.len()))
        }
        _ => {
            eprintln!("unknown kind");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(value) => {
            println!("{value}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error:?}");
            ExitCode::FAILURE
        }
    }
}
