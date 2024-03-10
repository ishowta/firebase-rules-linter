use std::io::Write;
use tokio::process::Command;

use log::debug;
use tempfile::NamedTempFile;

use crate::config::Config;

#[test]
fn test() {
    let command_result = std::process::Command::new("/bin/bash")
        //.arg("-T:5")
        .arg("-c")
        .arg("echo 3 && echo 4")
        .output()
        .unwrap();
    println!("{:?}", command_result)
}

async fn run_z3(source: &String, config: &Config) -> String {
    debug!("{}", source);
    let mut debug_source = "".to_owned();
    let mut line_count = 0;
    for line in source.split("\n") {
        debug_source += format!("{}: {}\n", line_count + 1, line).as_str();
        line_count += 1;
    }
    debug!("RUN Z3:\n{}", debug_source);
    let mut source_file = NamedTempFile::new().unwrap();
    let _ = source_file.write_all(source.as_bytes());
    let command_result = Command::new("/bin/sh")
        //.arg("-T:5")
        .arg("-c")
        .arg(format!(
            "ulimit -t {} && z3 {}",
            config.analysis_rule_timeout_sec,
            source_file.path().to_str().unwrap()
        ))
        .output()
        .await
        .unwrap();
    let command_output: String = String::from_utf8_lossy(&command_result.stdout)
        .trim()
        .into();
    if command_output == "" {
        return "timeout".to_owned();
    }
    if command_output
        .split("\n")
        .any(|line| line.starts_with("(error ") && !line.ends_with("model is not available\")"))
        || command_output
            .split("\n")
            .find(|line| ["sat", "unsat", "unknown", "timeout"].contains(line))
            == None
    {
        eprintln!("RUN Z3:\n{}", debug_source);
        eprintln!("Z3 Error: {}", command_output);
        panic!();
    }
    command_output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResult {
    Sat(String),
    Unsat,
    Unknown,
    Timeout,
}

pub async fn solve(source: &String, config: &Config) -> SolverResult {
    let input = format!(
        "
{}

;(apply (then (repeat (then simplify solve-eqs (or-else split-clause skip) dom-simplify))))
;(check-sat)
(check-sat-using (then (repeat (then simplify solve-eqs (or-else split-clause skip) dom-simplify)) smt))
;(get-model)
(eval request_resource_data_inner)
",
        source
    );
    let output = run_z3(&input, config).await;
    debug!("{}", output);
    match output
        .split("\n")
        .find(|line| ["sat", "unsat", "unknown", "timeout"].contains(line))
    {
        Some("sat") => {
            SolverResult::Sat(output.split("\n").skip(1).collect::<Vec<&str>>().join("\n"))
        }
        Some("unsat") => SolverResult::Unsat,
        Some("unknown") => SolverResult::Unknown,
        Some("timeout") => SolverResult::Timeout,
        _ => {
            eprintln!("Z3 Error: {}", output);
            panic!()
        }
    }
}
