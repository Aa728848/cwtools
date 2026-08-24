use std::env;
use std::fs;
use std::process::ExitCode;
use std::time::Instant;

use cwtools_script_syntax::{ScriptEncoding, decode_script_bytes, parse};

fn main() -> ExitCode {
    let args: Vec<_> = env::args().collect();
    let Some(path) = args.get(1) else {
        eprintln!("usage: parse_file <path> [iterations]");
        return ExitCode::from(2);
    };
    let iterations = args
        .get(2)
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(10);
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };
    let source = decode_script_bytes(&bytes, ScriptEncoding::Windows1252)
        .expect("Windows-1252 decoding cannot fail");
    let started = Instant::now();
    let mut tokens = 0_usize;
    let mut roots = 0_usize;
    for _ in 0..iterations {
        let parsed = match parse(&source) {
            Ok(parsed) => parsed,
            Err(errors) => {
                eprintln!("parse failed with {} errors", errors.len());
                return ExitCode::FAILURE;
            }
        };
        tokens = parsed.tokens.len();
        roots = parsed.roots.len();
    }
    let elapsed = started.elapsed();
    println!(
        "{{\"bytes\":{},\"iterations\":{},\"tokens\":{},\"roots\":{},\"elapsedMs\":{},\"bytesPerSecond\":{}}}",
        bytes.len(),
        iterations,
        tokens,
        roots,
        elapsed.as_secs_f64() * 1000.0,
        u128::try_from(bytes.len())
            .unwrap()
            .saturating_mul(u128::try_from(iterations).unwrap())
            .saturating_mul(1_000_000_000)
            / elapsed.as_nanos().max(1)
    );
    ExitCode::SUCCESS
}
