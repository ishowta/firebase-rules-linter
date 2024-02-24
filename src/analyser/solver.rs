use std::{io::Write, process::Command};

use log::{debug, info};
use tempfile::NamedTempFile;

fn run_z3(source: &String) -> String {
    debug!("{}", source);
    let mut debug_source = "".to_owned();
    let mut line_count = 0;
    for line in source.split("\n") {
        debug_source += format!("{}: {}\n", line_count + 1, line).as_str();
        line_count += 1;
    }
    info!("RUN Z3:\n{}", debug_source);
    let mut source_file = NamedTempFile::new().unwrap();
    let _ = source_file.write_all(source.as_bytes());
    let command_result = Command::new("z3").arg(source_file.path()).output();
    let command_output = String::from_utf8_lossy(&command_result.unwrap().stdout)
        .trim()
        .into();
    command_output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResult {
    Sat(String),
    Unsat,
    Unknown,
}

pub fn solve(source: &String) -> SolverResult {
    let input = format!(
        "
{}

(apply (then (repeat (then simplify solve-eqs (or-else split-clause skip) dom-simplify))))
(check-sat-using (then (repeat (then simplify solve-eqs (or-else split-clause skip) dom-simplify)) smt))
(get-model)
",
        source
    );
    let output = run_z3(&input);
    info!("{}", output);
    match output
        .split("\n")
        .find(|line| ["sat", "unsat", "unknown"].contains(line))
    {
        Some("sat") => {
            SolverResult::Sat(output.split("\n").skip(1).collect::<Vec<&str>>().join("\n"))
        }
        Some("unsat") => SolverResult::Unsat,
        Some("unknown") => SolverResult::Unknown,
        Some(error) => {
            eprintln!("Z3 Error: {}\n{}", error, output);
            panic!()
        }
        _ => panic!(),
    }
}
